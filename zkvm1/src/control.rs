// control.rs — governs the clock, the program counter, and termination.
//
// No branches in this ISA, so the control flow is simple: the clock always
// advances, the pc advances by one except on HALT (which freezes it), and the
// trace must start at the beginning and end halted.
//
// Constraints:
//   clock anchor      q_first · clk = 0                     clk starts at 0
//   clock step        q_step  · (clk' − clk − 1) = 0        clk increments
//   pc anchor         q_first · pc = 0                      pc starts at 0
//   pc step           q_step  · [ (f_imm+f_add+f_mul)·(pc'−pc−1)
//                                 + f_hlt·(pc'−pc) ] = 0
//   halt absorbing    q_step  · f_hlt · (f_hlt' − 1) = 0    HALT stays HALT
//   halt at end       q_last  · (f_hlt − 1) = 0             trace ends halted
//
// The clock never freezes — not even in padding — so clk' = clk + 1 holds on
// every transition with no special case. Only the pc has a halt case, because
// only the pc has stop semantics.
//
// Preconditions (imposed elsewhere): flags boolean and one-hot (top-level).

use halo2_proofs::{
    halo2curves::bn256::Fr,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};

use crate::flags::OpFlags;

#[derive(Clone, Copy, Debug)]
pub struct ControlConfig {
    pub clk: Column<Advice>,
    pub pc: Column<Advice>,
    pub flags: OpFlags,
    pub q_step: Column<Fixed>,
    pub q_first: Column<Fixed>,
    pub q_last: Column<Fixed>,
}

impl ControlConfig {
    pub fn configure(
        meta: &mut ConstraintSystem<Fr>,
        q_step: Column<Fixed>,
        q_first: Column<Fixed>,
        q_last: Column<Fixed>,
        clk: Column<Advice>,
        pc: Column<Advice>,
        flags: OpFlags,
    ) -> Self {
        // --- clock: anchor at 0, then increment by 1 ---
        meta.create_gate("control: clock", |meta| {
            let q_first = meta.query_fixed(q_first, Rotation::cur());
            let q_step = meta.query_fixed(q_step, Rotation::cur());
            let clk_next = meta.query_advice(clk, Rotation::next());
            let clk = meta.query_advice(clk, Rotation::cur());
            let one = Expression::Constant(Fr::one());

            vec![
                q_first * clk.clone(),                 // clk[0] = 0
                q_step * (clk_next - clk - one),       // clk' = clk + 1
            ]
        });

        // --- pc: anchor at 0, then +1 except HALT freezes ---
        meta.create_gate("control: pc", |meta| {
            let q_first = meta.query_fixed(q_first, Rotation::cur());
            let q_step = meta.query_fixed(q_step, Rotation::cur());
            let pc_next = meta.query_advice(pc, Rotation::next());
            let pc = meta.query_advice(pc, Rotation::cur());
            let f_imm = meta.query_advice(flags.imm, Rotation::cur());
            let f_add = meta.query_advice(flags.add, Rotation::cur());
            let f_mul = meta.query_advice(flags.mul, Rotation::cur());
            let f_hlt = meta.query_advice(flags.hlt, Rotation::cur());
            let one = Expression::Constant(Fr::one());

            let advances = f_imm + f_add + f_mul;
            let delta = pc_next - pc.clone(); // pc' − pc

            vec![
                q_first * pc, // pc[0] = 0
                q_step
                    * (advances * (delta.clone() - one) + f_hlt * delta),
            ]
        });

        // --- halt absorbing: once HALT, always HALT ---
        meta.create_gate("control: halt absorbing", |meta| {
            let q_step = meta.query_fixed(q_step, Rotation::cur());
            let f_hlt = meta.query_advice(flags.hlt, Rotation::cur());
            let f_hlt_next = meta.query_advice(flags.hlt, Rotation::next());
            let one = Expression::Constant(Fr::one());

            vec![q_step * f_hlt * (f_hlt_next - one)]
        });

        // --- trace ends halted ---
        meta.create_gate("control: halt at end", |meta| {
            let q_last = meta.query_fixed(q_last, Rotation::cur());
            let f_hlt = meta.query_advice(flags.hlt, Rotation::cur());
            let one = Expression::Constant(Fr::one());

            vec![q_last * (f_hlt - one)]
        });

        Self { clk, pc, flags, q_step, q_first, q_last }
    }
}