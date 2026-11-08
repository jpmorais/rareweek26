// flags.rs — the one-hot opcode flags.
//
// One boolean advice column per opcode (imm, add, mul, hlt, xor). On a given
// row, exactly one is 1 — the "which instruction" question becomes arithmetic:
// multiply each case by its flag and sum the results (only the active case
// survives).
//
// The flag constraints (each boolean + sum = 1) live in the top-level, which
// is the owner that allocates the columns. This file only groups the columns
// and offers convenience helpers.
//
// Ordering note: xor is appended LAST (index 4), leaving hlt at index 3. Code
// that detects HALT by flags[3] (Control, several tests) stays correct.

use halo2_proofs::plonk::{Advice, Column};

#[derive(Clone, Copy, Debug)]
pub struct OpFlags {
    pub imm: Column<Advice>,
    pub add: Column<Advice>,
    pub mul: Column<Advice>,
    pub hlt: Column<Advice>,
    pub xor: Column<Advice>,
}

impl OpFlags {
    /// The five columns in canonical order — useful for iterating (one-hot,
    /// assignment, fetch encoding).
    pub fn all(&self) -> [Column<Advice>; 5] {
        [self.imm, self.add, self.mul, self.hlt, self.xor]
    }
}