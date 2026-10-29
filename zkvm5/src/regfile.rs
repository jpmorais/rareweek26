// regfile.rs — connects the datapath (a, b, c) to the register file.
//
// Without this chip, a and b are free witness: the ALU proves c = a + b, but
// nothing forces a to be the value of register rs1, or c to be written into
// register rd. This chip closes that gap.
//
// Register selection by index uses Lagrange indicators over {0, 1, 2, 3}.
// L_r(idx) is 1 exactly when idx == r and 0 for the other valid indices, so
//   Σ_r L_r(idx) · regs[r]
// collapses to regs[idx] — array indexing written as arithmetic (the circuit
// cannot index an array directly).
//
// Constraints (6 total):
//   read a:  (f_add + f_mul) · (a − Σ_r L_r(rs1)·regs[r]) = 0
//   read b:  (f_add + f_mul) · (b − Σ_r L_r(rs2)·regs[r]) = 0
//   write:   for each r in 0..4 (via q_step, next row):
//              regs[r]' = regs[r] + is_write · L_r(rd) · (c − regs[r])
//            with is_write = f_imm + f_add + f_mul.
//
// IMM and HALT don't read, so a/b are unconstrained on those rows. HALT
// doesn't write (is_write = 0), so every register copies — the state freezes
// for free, which is also what makes the padding rows valid.
//
// Preconditions (imposed elsewhere): flags boolean and one-hot (top-level);
// rd, rs1, rs2 ∈ {0,1,2,3} (would be enforced by a future Fetch or range
// check — without it, out-of-range indices make the Lagrange indicators
// misbehave).

use halo2_proofs::{
    halo2curves::bn256::Fr,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
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
///
///   L_r(x) = Π_{s≠r} (x − s) / (r − s)
///
/// Degree 3 (product of three linear terms). The constant denominators are
/// folded in as field inverses.
fn lagrange(idx: Expression<Fr>) -> [Expression<Fr>; 4] {
    // helper: constant field element from a small integer
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

    // L0(x) = (x−1)(x−2)(x−3) / ((0−1)(0−2)(0−3)) = (x−1)(x−2)(x−3) / (−6)
    let l0 = (idx.clone() - c(1)) * (idx.clone() - c(2)) * (idx.clone() - c(3)) * inv(-6);
    // L1(x) = x(x−2)(x−3) / ((1)(−1)(−2)) = x(x−2)(x−3) / 2
    let l1 = idx.clone() * (idx.clone() - c(2)) * (idx.clone() - c(3)) * inv(2);
    // L2(x) = x(x−1)(x−3) / ((2)(1)(−1)) = x(x−1)(x−3) / (−2)
    let l2 = idx.clone() * (idx.clone() - c(1)) * (idx.clone() - c(3)) * inv(-2);
    // L3(x) = x(x−1)(x−2) / ((3)(2)(1)) = x(x−1)(x−2) / 6
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
        // --- read a: a = regs[rs1], only for ADD/MUL ---
        // The prefix (f_add + f_mul) is the "if this instruction reads": when
        // it is 0 (IMM/HALT) the whole constraint vanishes and a is free;
        // when it is 1, a − regs[rs1] = 0 forces the equality.
        // a cames from register source 1 (rs1)

        // a - (L_0(rs1)Reg0 + L_1(rs1)Reg1 + L_2(rs2)Reg2 + L_3(rs3)Reg3)
        // a is read correctly from the registeres
        // a = Reg[rs1]
        meta.create_gate("regfile: read a", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let reads = meta.query_advice(flags.add, Rotation::cur())
                + meta.query_advice(flags.mul, Rotation::cur());
            let a = meta.query_advice(a, Rotation::cur());
            let rs1 = meta.query_advice(rs1, Rotation::cur());

            let l = lagrange(rs1);
            let mut selected = Expression::Constant(Fr::zero());
            for (r, col) in regs.iter().enumerate() {
                let reg = meta.query_advice(*col, Rotation::cur());
                //                    L_i[rs1] Reg[i]
                selected = selected + l[r].clone() * reg;
            }

            vec![q * reads * (a - selected)]
        });

        // --- read b: b = regs[rs2], only for ADD/MUL ---
        // b = Reg[rs2]
        meta.create_gate("regfile: read b", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let reads = meta.query_advice(flags.add, Rotation::cur())
                + meta.query_advice(flags.mul, Rotation::cur());
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
        //   - is_write = f_imm + f_add + f_mul : does this instruction write?
        //   - L_r(rd)  : is r the destination register?
        // Both switches must be 1 for regs[r] to receive c; otherwise the term
        // is 0 and the register copies. When is_write = 0 (HALT/padding) every
        // register copies and the state freezes.
        // reg[rd] on the next line = c  if operation is add, mul, imm
        // all the other registers stays the same value
        meta.create_gate("regfile: write", |meta| {
            let q = meta.query_fixed(q_step, Rotation::cur());
            let is_write = meta.query_advice(flags.imm, Rotation::cur())
                + meta.query_advice(flags.add, Rotation::cur())
                + meta.query_advice(flags.mul, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let rd = meta.query_advice(rd, Rotation::cur());
            let l = lagrange(rd);

            let mut constraints = Vec::new();
            for (r, col) in regs.iter().enumerate() {
                let cur = meta.query_advice(*col, Rotation::cur());
                let next = meta.query_advice(*col, Rotation::next());
                let delta = c.clone() - cur.clone(); // change if this is the target
                let expected = cur + is_write.clone() * l[r].clone() * delta;
                constraints.push(q.clone() * (next - expected));
            }
            constraints
        });

        Self { regs, rd, rs1, rs2, a, b, c, flags, q_exec, q_step }
    }
}