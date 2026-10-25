
use crate::constants::{FULL_ROUNDS, PARTIAL_ROUNDS, ROUND_CONSTANTS, T};
use crate::poseidon::{apply_mds, sbox};

use halo2_proofs::halo2curves::bn256::Fr;
use ff::Field;


pub fn poseidon_trace(input_0: Fr, input_1: Fr) -> Vec<[Fr; T]> {
    let mut state = [Fr::ZERO, input_0, input_1];
    let mut trace = vec![state];

    let r_f = FULL_ROUNDS / 2;
    let r_p = PARTIAL_ROUNDS;
    let mut round = 0;

    for _ in 0..r_f {
        for i in 0..T {
            state[i] += ROUND_CONSTANTS[round][i];
            state[i] = sbox(state[i]);
        }
        apply_mds(&mut state);
        round += 1;
        trace.push(state);
    }

    for _ in 0..r_p {
        for i in 0..T {
            state[i] += ROUND_CONSTANTS[round][i];
        }
        state[0] = sbox(state[0]);
        apply_mds(&mut state);
        round += 1;
        trace.push(state);
    }

    for _ in 0..r_f {
        for i in 0..T {
            state[i] += ROUND_CONSTANTS[round][i];
            state[i] = sbox(state[i]);
        }
        apply_mds(&mut state);
        round += 1;
        trace.push(state);
    }

    trace
}