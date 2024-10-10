import compiler as c
import prover as p
import verifier as v
import json
from mini_poseidon import rc, mds, poseidon_hash

def basic_test():
    setup = c.Setup.from_file('powersOfTau28_hez_final_11.ptau')
    print("Extracted setup")
    vk = c.make_verification_key(setup, 8, ['c <== a * b'])
    print("Generated verification key")
    their_output = json.load(open('main.plonk.vkey.json'))
    for key in ('Qm', 'Ql', 'Qr', 'Qo', 'Qc', 'S1', 'S2', 'S3', 'X_2'):
        if c.interpret_json_point(their_output[key]) != vk[key]:
            raise Exception("Mismatch {}: ours {} theirs {}"
                            .format(key, vk[key], their_output[key]))
    assert vk['w'] == int(their_output['w'])
    print("Basic test success")
    return setup

# Equivalent to this zkrepl code:
#
# template Example () {
#    signal input a;
#    signal input b;
#    signal c;
#    c <== a * b + a;
# }
def ab_plus_a_test(setup):
    vk = c.make_verification_key(setup, 8, ['ab === a - c', '-ab === a * b'])
    print("Generated verification key")
    their_output = json.load(open('main.plonk.vkey-58.json'))
    for key in ('Qm', 'Ql', 'Qr', 'Qo', 'Qc', 'S1', 'S2', 'S3', 'X_2'):
        if c.interpret_json_point(their_output[key]) != vk[key]:
            raise Exception("Mismatch {}: ours {} theirs {}"
                            .format(key, vk[key], their_output[key]))
    assert vk['w'] == int(their_output['w'])
    print("ab+a test success")

def one_public_input_test(setup):
    vk = c.make_verification_key(setup, 8, ['c public', 'c === a * b'])
    print("Generated verification key")
    their_output = json.load(open('main.plonk.vkey-59.json'))
    for key in ('Qm', 'Ql', 'Qr', 'Qo', 'Qc', 'S1', 'S2', 'S3', 'X_2'):
        if c.interpret_json_point(their_output[key]) != vk[key]:
            raise Exception("Mismatch {}: ours {} theirs {}"
                            .format(key, vk[key], their_output[key]))
    assert vk['w'] == int(their_output['w'])
    print("One public input test success")

def prover_test(setup):
    print("Beginning prover test")
    eqs = ['e public', 'c <== a * b', 'e <== c * d']
    assignments = {'a': 3, 'b': 4, 'c': 12, 'd': 5, 'e': 60}
    return p.prove_from_witness(setup, 8, eqs, assignments)
    print("Prover test success")

def verifier_test(setup, proof):
    print("Beginning verifier test")
    eqs = ['e public', 'c <== a * b', 'e <== c * d']
    public = [60]
    vk = c.make_verification_key(setup, 8, eqs)
    assert v.verify_proof(setup, 8, vk, proof, public, optimized=False)
    assert v.verify_proof(setup, 8, vk, proof, public, optimized=True)
    print("Verifier test success")

def factorization_test(setup):
    print("Beginning test: prove you know small integers that multiply to 91")
    eqs = """
        n public
        pb0 === pb0 * pb0
        pb1 === pb1 * pb1
        pb2 === pb2 * pb2
        pb3 === pb3 * pb3
        qb0 === qb0 * qb0
        qb1 === qb1 * qb1
        qb2 === qb2 * qb2
        qb3 === qb3 * qb3
        pb01 <== pb0 + 2 * pb1
        pb012 <== pb01 + 4 * pb2
        p <== pb012 + 8 * pb3
        qb01 <== qb0 + 2 * qb1
        qb012 <== qb01 + 4 * qb2
        q <== qb012 + 8 * qb3
        n <== p * q
    """
    public = [91]
    vk = c.make_verification_key(setup, 16, eqs)
    print("Generated verification key")
    assignments = c.fill_variable_assignments(eqs, {
        'pb3': 1, 'pb2': 1, 'pb1': 0, 'pb0': 1,
        'qb3': 0, 'qb2': 1, 'qb1': 1, 'qb0': 1,
    })
    proof = p.prove_from_witness(setup, 16, eqs, assignments)
    print("Generated proof")
    assert v.verify_proof(setup, 16, vk, proof, public, optimized=True)
    print("Factorization test success!")

def encryption_test(setup):
    print("Beginning test: prove you know the plaintext of an encrypted message")

    n = 8

    eqs = """
            i public
    """
    for ii in range(0, n):
        public_ii = f"""
                a{ii}0 public
                a{ii}1 public
                a{ii}2 public
                b{ii} public
            """
        eqs += public_ii
    
    eqs += """p public"""

    i_stuff = """
        i0 === i0 * i0
        i1 === i1 * i1
        i2 === i2 * i2
        ii01 <== i0 + 2 * i1
        i === ii01 + 4 * i2
        """
    i2bin = {0 : "000", 1 : "001", 2 : "010", 3 : "011", 4 : "100", 5 : "101", 6 : "110", 7 : "111"}

    for ii in range(0, n):
        i_stuff += f"""
                    i{ii}0 === {i2bin[ii][2]}
                    i{ii}1 === {i2bin[ii][1]}
                    i{ii}2 === {i2bin[ii][0]}
                    i{ii}0bar <== 1 - i{ii}0
                    i{ii}1bar <== 1 - i{ii}1
                    i{ii}2bar <== 1 - i{ii}2
                    i{ii}0diff <== i{ii}0bar - i0
                    i{ii}1diff <== i{ii}1bar - i1
                    i{ii}2diff <== i{ii}2bar - i2
                    i{ii}01prod <== i{ii}0diff * i{ii}1diff
                    i{ii}012prod <== i{ii}01prod * i{ii}2diff
                    i{ii}sel <== i{ii}012prod * i{ii}012prod
                """
    
    s_stuff = """
        s0 === s0 * s0
        s1 === s1 * s1
        s2 === s2 * s2
        p === pp
    """

    a_stuff = """"""
    for ii in range(0, n):
        a_stuff += f"""
                    a{ii}0 === aa{ii}0
                    a{ii}1 === aa{ii}1
                    a{ii}2 === aa{ii}2
                    b{ii} === bb{ii}
                    a{ii}0s0 <== aa{ii}0 * s0
                    a{ii}1s1 <== aa{ii}1 * s1
                    a{ii}2s2 <== aa{ii}2 * s2
                    as{ii}01 <== a{ii}0s0 + a{ii}1s1
                    a{ii}s <== as{ii}01 + a{ii}2s2
                    a{ii}splusp <== a{ii}s + pp
                    bsel{ii} <== bb{ii} * i{ii}sel
                    aspluspsel{ii} <== a{ii}splusp * i{ii}sel
                    bsel{ii} <== aspluspsel{ii}
                """
    eqs += i_stuff + s_stuff + a_stuff
    

    public = [  1,
                3, 7, 11, 15,
                8, 2, 5, 19, 
                5, 7, 2, 11,
                3, 1, 1, 8,
                2, 0, 10, 10,
                6, 12, 3, 5,
                5, 9, 3, 11,
                1, 0, 7, 5,
                6
            ]
    group_order = 64 * n
    vk = c.make_verification_key(setup, group_order, eqs)
    print("Generated verification key")
    assignments = c.fill_variable_assignments(eqs, {
        'i0' : 1, 'i1' : 0, 'i2' : 0,
        'aa00': 3, 'aa01': 7, 'aa02': 11, 'bb0': 15,
        'aa10': 8, 'aa11': 2, 'aa12': 5, 'bb1': 19,
        'aa20': 5, 'aa21': 7, 'aa22': 2, 'bb2': 11,
        'aa30': 3, 'aa31': 1, 'aa32': 1, 'bb3': 8,
        'aa40': 2, 'aa41': 0, 'aa42': 10, 'bb4': 10,
        'aa50': 6, 'aa51': 12, 'aa52': 3, 'bb5': 5,
        'aa60': 5, 'aa61': 9, 'aa62': 3, 'bb6': 11,
        'aa70': 1, 'aa71': 0, 'aa72': 7, 'bb7': 5,
        's0': 1, 's1': 0, 's2': 1, 
        'pp': 6
    })
    proof = p.prove_from_witness(setup, group_order, eqs, assignments)
    print("Generated proof")
    assert v.verify_proof(setup, group_order, vk, proof, public, optimized=True)
    print("Encryption test success!")


         

def output_proof_lang():
    o = []
    o.append('L0 public')
    o.append('M0 public')
    o.append('M64 public')
    o.append('R0 <== 0')
    for i in range(64):
        for j, pos in enumerate(('L', 'M', 'R')):
            f = {'x': i, 'r': rc[i][j], 'p': pos}
            if i < 4 or i >= 60 or pos == 'L':
                o.append('{p}adj{x} <== {p}{x} + {r}'.format(**f))
                o.append('{p}sq{x} <== {p}adj{x} * {p}adj{x}'.format(**f))
                o.append('{p}qd{x} <== {p}sq{x} * {p}sq{x}'.format(**f))
                o.append('{p}qn{x} <== {p}qd{x} * {p}adj{x}'.format(**f))
            else:
                o.append('{p}qn{x} <== {p}{x} + {r}'.format(**f))
        for j, pos in enumerate(('L', 'M', 'R')):
            f = {'x': i, 'p': pos, 'm': mds[j]}
            o.append('{p}suma{x} <== Lqn{x} * {m}'.format(**f))
            f = {'x': i, 'p': pos, 'm': mds[j+1]}
            o.append('{p}sumb{x} <== {p}suma{x} + Mqn{x} * {m}'.format(**f))
            f = {'x': i, 'xp1': i+1, 'p': pos, 'm': mds[j+2]}
            o.append('{p}{xp1} <== {p}sumb{x} + Rqn{x} * {m}'.format(**f))
    return '\n'.join(o)

def poseidon_test(setup):
    # PLONK-prove the correctness of a Poseidon execution. Note that this is
    # a very suboptimal way to do it: an optimized implementation would use
    # a custom PLONK gate to do a round in a single gate
    expected_value = poseidon_hash(1, 2)
    # Generate code for proof
    code = output_proof_lang()
    print("Generated code for Poseidon test")
    assignments = c.fill_variable_assignments(code, {'L0': 1, 'M0': 2})
    vk = c.make_verification_key(setup, 1024, code)
    print("Generated verification key")
    proof = p.prove_from_witness(setup, 1024, code, assignments)
    print("Generated proof")
    assert v.verify_proof(setup, 1024, vk, proof, [1, 2, expected_value])
    print("Verified proof!")
if __name__ == '__main__':
    setup = basic_test()
    # ab_plus_a_test(setup)
    # one_public_input_test(setup)
    # proof = prover_test(setup)
    # verifier_test(setup, proof)
    # factorization_test(setup)
    encryption_test(setup)
    # poseidon_test(setup)
