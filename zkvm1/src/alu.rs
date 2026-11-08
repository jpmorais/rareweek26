// alu.rs — the arithmetic: it constrains the result column c per opcode.
//
// One gate per operation, each gated by its one-hot flag so it only fires on
// the matching row:
//
//   IMM:  f_imm · (c - imm)     = 0     c is the immediate
//   ADD:  f_add · (c - a - b)   = 0     c is the sum of the operands
//   MUL:  f_mul · (c - a * b)   = 0     c is the product
//
// HALT has no gate here, so c is unconstrained on HALT rows (nothing reads
// it). The operands a, b are bound to the right registers by the RegFile;
// here the ALU only relates them to c. Keeping the three gates separate makes
// a failing MockProver point at the specific opcode.

use halo2_proofs::{
    halo2curves::bn256::Fr,
    plonk::{Advice, Column, ConstraintSystem, Fixed},
    poly::Rotation,
};

use crate::flags::OpFlags;

#[derive(Clone, Copy, Debug)]
pub struct AluConfig {
    pub a: Column<Advice>,
    pub b: Column<Advice>,
    pub c: Column<Advice>,
    pub imm: Column<Advice>,
    pub flags: OpFlags,
    pub q_exec: Column<Fixed>,
}

impl AluConfig {
    pub fn configure(
        meta: &mut ConstraintSystem<Fr>,
        q_exec: Column<Fixed>,
        a: Column<Advice>,
        b: Column<Advice>,
        c: Column<Advice>,
        imm: Column<Advice>,
        flags: OpFlags,
    ) -> Self {
        meta.create_gate("alu: IMM", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let f = meta.query_advice(flags.imm, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let imm = meta.query_advice(imm, Rotation::cur());
            vec![q * f * (c - imm)]
        });

        meta.create_gate("alu: ADD", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let f = meta.query_advice(flags.add, Rotation::cur());
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            vec![q * f * (c - a - b)]
        });

        meta.create_gate("alu: MUL", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let f = meta.query_advice(flags.mul, Rotation::cur());
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            vec![q * f * (c - a * b)]
        });

        Self { a, b, c, imm, flags, q_exec }
    }
}