// control.rs — governs the clock, the program counter, and termination.
//
// Control flow now has a branch: JUMPI. The clock still always advances; the pc
// advances by one EXCEPT on HALT (freezes) and on a TAKEN JUMPI (goes to the
// immediate target). The trace must start at the beginning and end halted.
//
// Constraints:
//   clock anchor      q_first · clk = 0                     clk starts at 0
//   clock step        q_step  · (clk' − clk − 1) = 0        clk increments
//   pc anchor         q_first · pc = 0                      pc starts at 0
//   is-nonzero honest q_step  · a·(1 − a·a_inv) = 0         a_inv is a true inverse
//   pc step           q_step  · [ normal·(pc'−pc−1)
//                                 + f_hlt·(pc'−pc)
//                                 + f_jumpi·(pc' − pc_jumpi) ] = 0
//   halt absorbing    q_step  · f_hlt · (f_hlt' − 1) = 0    HALT stays HALT
//   halt at end       q_last  · (f_hlt − 1) = 0             trace ends halted
//
// pc step, three mutually-exclusive cases (one-hot flags guarantee at most one
// fires):
//   normal   = 1 − f_hlt − f_jumpi   → pc' = pc + 1     term: normal·(pc'−pc−1)
//   f_hlt                            → pc' = pc          term: f_hlt·(pc'−pc)
//   f_jumpi                          → pc' = pc_jumpi    term: f_jumpi·(pc'−pc_jumpi)
// with the is-nonzero bit  taken = a · a_inv  (a = regs[rs1]):
//   pc_jumpi = taken·imm + (1 − taken)·(pc + 1)
//
// Each term is the flag times "how wrong pc' is for that case", so exactly one
// term is active (one-hot) and it forces pc' to the right value; the other two
// vanish. The taken-JUMPI term reduces cleanly: f_jumpi·(pc' − pc_jumpi).
//
// The "normal" case is the COMPLEMENT of the two special flags, not a list of
// advancing opcodes (f_imm + f_add + …). The list form silently forgot new
// opcodes before (XOR, LOAD/STORE), leaving the pc free on those rows — a latent
// soundness hole. The complement couples nothing: any opcode that is neither
// HALT nor JUMPI advances automatically. Relies on one-hot so normal ∈ {0, 1}.
//
// is-nonzero gadget: taken = a·a_inv must be the boolean "a ≠ 0". The witness
// a_inv is 1/a when a ≠ 0 and 0 otherwise (filled every row by the emulator).
// The gate a·(1 − a·a_inv) = 0 forces honesty: if a ≠ 0 the only solution is
// a_inv = 1/a (so taken = 1); if a = 0 then taken = 0 regardless. Same inverse
// trick the memory argument uses for same_addr, complemented. It's global (only
// gated by q_step) because a_inv is filled every row, so honest rows never
// violate it; f_jumpi only selects WHERE taken feeds the pc.
//
// The clock never freezes — not even in padding — so clk' = clk + 1 holds on
// every transition. Only the pc has special cases.
//
// Preconditions (imposed elsewhere): flags boolean and one-hot (top-level); the
// datapath binds `a` to regs[rs1] (RegFile) and `imm` to the fetched instruction
// (Fetch), so the values this gate reads are the real ones.

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
        // JUMPI inputs: the condition register value `a`, its inverse witness
        // `a_inv`, and the immediate `imm` (the jump target).
        a: Column<Advice>,
        a_inv: Column<Advice>,
        imm: Column<Advice>,
    ) -> Self {
        // --- clock: anchor at 0, then increment by 1 ---
        meta.create_gate("control: clock", |meta| {
            let q_first = meta.query_fixed(q_first, Rotation::cur());
            let q_step = meta.query_fixed(q_step, Rotation::cur());
            let clk_next = meta.query_advice(clk, Rotation::next());
            let clk = meta.query_advice(clk, Rotation::cur());
            let one = Expression::Constant(Fr::one());

            vec![
                q_first * clk.clone(),           // clk[0] = 0
                q_step * (clk_next - clk - one), // clk' = clk + 1
            ]
        });

        // --- is-nonzero gadget honesty: a·(1 − a·a_inv) = 0 ---
        meta.create_gate("control: is-nonzero (a_inv honest)", |meta| {
            let q_step = meta.query_fixed(q_step, Rotation::cur());
            let a = meta.query_advice(a, Rotation::cur());
            let a_inv = meta.query_advice(a_inv, Rotation::cur());
            let one = Expression::Constant(Fr::one());

            // taken = a·a_inv; forces a_inv = 1/a whenever a ≠ 0.
            vec![q_step * a.clone() * (one - a * a_inv)]
        });

        // --- pc: anchor at 0 ---
        meta.create_gate("control: pc anchor", |meta| {
            let q_first = meta.query_fixed(q_first, Rotation::cur());
            let pc = meta.query_advice(pc, Rotation::cur());
            vec![q_first * pc] // pc[0] = 0
        });

        // --- pc: step (normal +1 / HALT freeze / JUMPI conditional) ---
        meta.create_gate("control: pc step", |meta| {
            let q_step = meta.query_fixed(q_step, Rotation::cur());
            let pc_next = meta.query_advice(pc, Rotation::next());
            let pc = meta.query_advice(pc, Rotation::cur());
            let f_hlt = meta.query_advice(flags.hlt, Rotation::cur());
            let f_jumpi = meta.query_advice(flags.jumpi, Rotation::cur());
            let a = meta.query_advice(a, Rotation::cur());
            let a_inv = meta.query_advice(a_inv, Rotation::cur());
            let imm = meta.query_advice(imm, Rotation::cur());
            let one = Expression::Constant(Fr::one());

            // normal = 1 − f_hlt − f_jumpi
            // if is not halt or is not jumpi, normal should be increase by one
            // it should jump if the register is non-zero
            // JUMPI RS1, IMM    Jumpi 3 100
            let normal = one.clone() - f_hlt.clone() - f_jumpi.clone();

            // is_nonzero = a·a_inv  (1 when a ≠ 0, else 0)
            // pc_jumpi = is_nonzero·imm + (1 − is_nonzero)·(pc + 1)
            // pc_jump = if the value in RS1 is zero then pc = pc + 1, otherwise pc = imm column
            // Let say I found zero, so it is zero, so is_nonzero = 0
            // Let say I found non_zero, so I should jump, so is_nonzero = 1
            let is_nonzero = a * a_inv;
            let pc_plus_1 = pc.clone() + one.clone();
            let pc_jumpi = is_nonzero.clone() * imm + (one.clone() - is_nonzero) * pc_plus_1;

            // one term per case; exactly one flag active pins pc' to its value.
            // test_normal, normal is 1 I just increase the counter
            let term_normal = normal * (pc_next.clone() - pc.clone() - one);
            let term_hlt = f_hlt * (pc_next.clone() - pc);
            let term_jumpi = f_jumpi * (pc_next - pc_jumpi);

            vec![q_step * (term_normal + term_hlt + term_jumpi)]
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