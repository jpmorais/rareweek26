// regfile.rs — connects the datapath (a, b, c) to the register file.
//
// Without this chip, a and b are free witness: the ALU proves c = a + b, but
// nothing forces a to be the value of register rs1, or c to be written into
// register rd. This chip closes that gap.
//
// Register selection by index uses Lagrange indicators over {0, 1, 2, 3}.
// L_r(idx) is 1 exactly when idx == r and 0 for the other valid indices, so
//   Σ_r L_r(idx) · regs[r]
// collapses to regs[idx] — array indexing written as arithmetic.
//
// Constraints (6 total):
//   read a:  reads_a · (a − Σ_r L_r(rs1)·regs[r]) = 0
//   read b:  reads_b · (b − Σ_r L_r(rs2)·regs[r]) = 0
//   write:   for each r in 0..4 (via q_step, next row):
//              regs[r]' = regs[r] + is_write · L_r(rd) · (c − regs[r])
//
// The opcode selectors — WHO reads a, WHO reads b, WHO writes — must list every
// opcode of that kind. LOAD/STORE break the old "reads two, writes one"
// symmetry, so read-a and read-b now have DIFFERENT selectors:
//
//   reads_a  = f_add + f_mul + f_xor + f_load + f_store
//              everyone who uses `a`. For ADD/MUL/XOR a is the left operand;
//              for LOAD/STORE a is the MEMORY ADDRESS (regs[rs1]).
//   reads_b  = f_add + f_mul + f_xor + f_store
//              everyone who uses `b`. NOT load: LOAD reads only rs1 (address);
//              its b is unused. STORE uses b as the value to store (regs[rs2]).
//   is_write = f_imm + f_add + f_mul + f_xor + f_load
//              everyone who writes a register. NOT store: STORE writes memory,
//              not a register, so on a STORE row every register must copy.
//
// IMM/HALT don't read (a/b free). HALT/STORE don't write (registers copy —
// which also makes padding rows valid).
//
// NOTE: these selectors are where the RegFile hardcodes the ISA's shape. The
// complement trick used in Control (1 − f_hlt) does not apply cleanly here
// because "reads a", "reads b", "writes" are three different subsets that do
// not each have a single excluded opcode — so they stay as explicit sums.
//
// Preconditions (imposed elsewhere): flags boolean and one-hot (top-level);
// rd, rs1, rs2 ∈ {0,1,2,3}.

use halo2_proofs::{
    halo2curves::bn256::Fr,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};

use halo2_proofs::arithmetic::Field;

use crate::flags::OpFlags;

#[derive(Clone, Copy, Debug)]
pub struct RegFileConfig {
    pub regs: [Column<Advice>; 4],
    pub rd: Column<Advice>,
    pub rs1: Column<Advice>,
    pub rs2: Column<Advice>,
    pub a: Column<Advice>,
    pub b: Column<Advice>,
    pub c: Column<Advice>,
    pub flags: OpFlags,
    pub q_exec: Column<Fixed>,
    pub q_step: Column<Fixed>,
}

/// The four Lagrange indicators [L0, L1, L2, L3] over {0,1,2,3}, evaluated at
/// `idx`. Each L_r is 1 at idx == r and 0 at the other three valid points.
fn lagrange(idx: Expression<Fr>) -> [Expression<Fr>; 4] {
    let c = |v: i64| {
        if v >= 0 {
            Expression::Constant(Fr::from(v as u64))
        } else {
            Expression::Constant(-Fr::from((-v) as u64))
        }
    };
    let inv = |v: i64| {
        let f = if v >= 0 {
            Fr::from(v as u64)
        } else {
            -Fr::from((-v) as u64)
        };
        Expression::Constant(f.invert().unwrap())
    };

    let l0 = (idx.clone() - c(1)) * (idx.clone() - c(2)) * (idx.clone() - c(3)) * inv(-6);
    let l1 = idx.clone() * (idx.clone() - c(2)) * (idx.clone() - c(3)) * inv(2);
    let l2 = idx.clone() * (idx.clone() - c(1)) * (idx.clone() - c(3)) * inv(-2);
    let l3 = idx.clone() * (idx.clone() - c(1)) * (idx - c(2)) * inv(6);

    [l0, l1, l2, l3]
}

impl RegFileConfig {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<Fr>,
        q_exec: Column<Fixed>,
        q_step: Column<Fixed>,
        regs: [Column<Advice>; 4],
        rd: Column<Advice>,
        rs1: Column<Advice>,
        rs2: Column<Advice>,
        a: Column<Advice>,
        b: Column<Advice>,
        c: Column<Advice>,
        flags: OpFlags,
    ) -> Self {
        // reads_a: who uses `a` (left operand OR memory address).
        let reads_a = |meta: &mut VirtualCells<Fr>| {
            meta.query_advice(flags.add, Rotation::cur())
                + meta.query_advice(flags.mul, Rotation::cur())
                + meta.query_advice(flags.xor, Rotation::cur())
                + meta.query_advice(flags.load, Rotation::cur())
                + meta.query_advice(flags.store, Rotation::cur())
        };

        // reads_b: who uses `b` (right operand OR store value). NOT load.
        let reads_b = |meta: &mut VirtualCells<Fr>| {
            meta.query_advice(flags.add, Rotation::cur())
                + meta.query_advice(flags.mul, Rotation::cur())
                + meta.query_advice(flags.xor, Rotation::cur())
                + meta.query_advice(flags.store, Rotation::cur())
        };

        // --- read a: a = regs[rs1], for every opcode that uses a ---
        meta.create_gate("regfile: read a", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let reads = reads_a(meta);
            let a = meta.query_advice(a, Rotation::cur());
            let rs1 = meta.query_advice(rs1, Rotation::cur());

            let l = lagrange(rs1);
            let mut selected = Expression::Constant(Fr::zero());
            for (r, col) in regs.iter().enumerate() {
                let reg = meta.query_advice(*col, Rotation::cur());
                selected = selected + l[r].clone() * reg;
            }

            vec![q * reads * (a - selected)]
        });

        // --- read b: b = regs[rs2], for every opcode that uses b ---
        meta.create_gate("regfile: read b", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let reads = reads_b(meta);
            let b = meta.query_advice(b, Rotation::cur());
            let rs2 = meta.query_advice(rs2, Rotation::cur());

            let l = lagrange(rs2);
            let mut selected = Expression::Constant(Fr::zero());
            for (r, col) in regs.iter().enumerate() {
                let reg = meta.query_advice(*col, Rotation::cur());
                selected = selected + l[r].clone() * reg;
            }

            vec![q * reads * (b - selected)]
        });

        // --- write: one constraint per register (via q_step, next row) ---
        // regs[r]' = regs[r] + is_write · L_r(rd) · (c − regs[r])
        //   is_write = imm + add + mul + xor + load  (NOT store)
        // On STORE (and HALT/padding) is_write = 0, so every register copies.
        meta.create_gate("regfile: write", |meta| {
            let q = meta.query_fixed(q_step, Rotation::cur());
            let is_write = meta.query_advice(flags.imm, Rotation::cur())
                + meta.query_advice(flags.add, Rotation::cur())
                + meta.query_advice(flags.mul, Rotation::cur())
                + meta.query_advice(flags.xor, Rotation::cur())
                + meta.query_advice(flags.load, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let rd = meta.query_advice(rd, Rotation::cur());
            let l = lagrange(rd);

            let mut constraints = Vec::new();
            for (r, col) in regs.iter().enumerate() {
                let cur = meta.query_advice(*col, Rotation::cur());
                let next = meta.query_advice(*col, Rotation::next());
                let delta = c.clone() - cur.clone();
                let expected = cur + is_write.clone() * l[r].clone() * delta;
                constraints.push(q.clone() * (next - expected));
            }
            constraints
        });

        Self { regs, rd, rs1, rs2, a, b, c, flags, q_exec, q_step }
    }
}