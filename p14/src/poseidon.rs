// src/poseidon.rs
use ff::Field;
use halo2_proofs::halo2curves::bn256::Fr;
use crate::constants::{MDS, ROUND_CONSTANTS, FULL_ROUNDS, PARTIAL_ROUNDS, T};

pub fn sbox(x: Fr) -> Fr {
    let x2 = x * x;
    let x4 = x2 * x2;
    x4 * x
}

pub fn apply_mds(state: &mut [Fr; T]) {
    let mut new_state = [Fr::ZERO; T];
    for i in 0..T {
        for j in 0..T {
            new_state[i] += MDS[i][j] * state[j];
        }
    }
    *state = new_state;
}

pub fn permute(state: &mut [Fr; T]) {
    let r_f = FULL_ROUNDS / 2;
    let r_p = PARTIAL_ROUNDS;
    let mut round = 0;

    for _ in 0..r_f {
        for i in 0..T {
            state[i] += ROUND_CONSTANTS[round][i];
            state[i] = sbox(state[i]);
        }
        apply_mds(state);
        round += 1;
    }

    for _ in 0..r_p {
        for i in 0..T {
            state[i] += ROUND_CONSTANTS[round][i];
        }
        state[0] = sbox(state[0]);
        apply_mds(state);
        round += 1;
    }

    for _ in 0..r_f {
        for i in 0..T {
            state[i] += ROUND_CONSTANTS[round][i];
            state[i] = sbox(state[i]);
        }
        apply_mds(state);
        round += 1;
    }
}

pub fn hash(input: [Fr; 2]) -> Fr {
    let mut state = [Fr::ZERO, input[0], input[1]];
    permute(&mut state);
    state[0]
}