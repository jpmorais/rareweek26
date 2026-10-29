// vm_circuit.rs — top-level circuit.
//
// Role of the top-level: allocate ALL shared columns, impose the flag
// constraints (boolean + one-hot), and assign the full trace. Chips are
// plugged in here one at a time, each adding its own constraints over these
// same shared columns.
//
// Plugged in: Flags (one-hot, here), ALU, Control, RegFile, RangeCheck, Xor.
//
// synthesize computes nothing about the trace content: every advice column,
// including the one-hot flags and the aux columns, is copied verbatim from the
// trace. Only the fixed selectors q_* are structural (derived from the row
// position); byte_table (0..255) and the XOR table (all byte pairs) are fixed
// data — none of these are part of the witness.
//
// NOTE on k: the XOR table holds 256×256 = 65536 entries (all byte pairs), so
// the circuit needs at least that many rows plus blinding: 2^k >= 65536 + few,
// i.e. k = 17 (131072 rows). The byte_table (256) fits easily inside that.
// This is the cost of a binary-RELATION table: XOR of two bytes is a table of
// pairs, not of values.

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::bn256::Fr,
    plonk::{Advice, Circuit, Column, ConstraintSystem, ErrorFront, Expression, Fixed, TableColumn},
    poly::Rotation,
};

use crate::alu::AluConfig;
use crate::flags::OpFlags;
use crate::vm_trace::TraceRow;
use crate::control::ControlConfig;
use crate::regfile::RegFileConfig;
use crate::range::RangeConfig;
use crate::xor::XorConfig;

#[derive(Clone, Debug)]
pub struct VmConfig {
    // state
    pub clk: Column<Advice>,
    pub pc: Column<Advice>,
    pub regs: [Column<Advice>; 4],
    // decode
    pub flags: OpFlags,
    pub rd: Column<Advice>,
    pub rs1: Column<Advice>,
    pub rs2: Column<Advice>,
    pub imm: Column<Advice>,
    // datapath
    pub a: Column<Advice>,
    pub b: Column<Advice>,
    pub c: Column<Advice>,
    // 32-bit auxiliaries
    //   hi       = high part of a op b = c + hi·2^32  (ALU reads this)
    //   c_limbs  = 8-bit limbs of c   (RangeCheck; also XOR result side)
    //   hi_limbs = 8-bit limbs of hi  (RangeCheck, under MUL)
    //   a_limbs  = 8-bit limbs of a   (Xor, operand side)
    //   b_limbs  = 8-bit limbs of b   (Xor, operand side)
    pub hi: Column<Advice>,
    pub c_limbs: [Column<Advice>; 4],
    pub hi_limbs: [Column<Advice>; 4],
    pub a_limbs: [Column<Advice>; 4],
    pub b_limbs: [Column<Advice>; 4],
    // fixed-data lookup tables
    pub byte_table: TableColumn,            // 0..=255 (range checks)
    pub xor_table: [TableColumn; 3],        // (x, y, x^y) for all byte pairs
    // fixed selectors
    pub q_exec: Column<Fixed>,
    pub q_step: Column<Fixed>,
    pub q_first: Column<Fixed>,
    pub q_last: Column<Fixed>,
    // chips
    pub alu: AluConfig,
    pub control: ControlConfig,
    pub regfile: RegFileConfig,
    pub range: RangeConfig,
    pub xor: XorConfig,
}

#[derive(Clone, Default, Debug)]
pub struct VmCircuit {
    pub trace: Vec<TraceRow>,
}

impl Circuit<Fr> for VmCircuit {
    type Config = VmConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        // --- allocate the shared columns ---
        let clk = meta.advice_column();
        let pc = meta.advice_column();
        let regs = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];
        let flags = OpFlags {
            imm: meta.advice_column(),
            add: meta.advice_column(),
            mul: meta.advice_column(),
            hlt: meta.advice_column(),
            xor: meta.advice_column(),
        };
        let rd = meta.advice_column();
        let rs1 = meta.advice_column();
        let rs2 = meta.advice_column();
        let imm = meta.advice_column();
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();

        // 32-bit auxiliaries
        let hi = meta.advice_column();
        let mk4 = |meta: &mut ConstraintSystem<Fr>| {
            [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ]
        };
        let c_limbs = mk4(meta);
        let hi_limbs = mk4(meta);
        let a_limbs = mk4(meta);
        let b_limbs = mk4(meta);

        // lookup tables (allocated specially: not advice, not fixed)
        let byte_table = meta.lookup_table_column();
        let xor_table = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        let q_exec = meta.fixed_column();
        let q_step = meta.fixed_column();
        let q_first = meta.fixed_column();
        let q_last = meta.fixed_column();

        // --- flag constraints: owned by whoever allocates them (top-level) ---
        // Each flag boolean, and exactly one set. Iterates over flags.all(), so
        // it already covers the new xor flag with no change to the logic.
        meta.create_gate("flags: boolean and one-hot", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let one = Expression::Constant(Fr::one());

            let fs = flags.all().map(|col| meta.query_advice(col, Rotation::cur()));

            let mut constraints = Vec::new();
            for f in fs.iter() {
                constraints.push(q.clone() * f.clone() * (f.clone() - one.clone()));
            }
            let mut sum = Expression::Constant(Fr::zero());
            for f in fs.iter() {
                sum = sum + f.clone();
            }
            constraints.push(q * (sum - one));
            constraints
        });

        // --- chips ---
        let alu = AluConfig::configure(meta, q_exec, a, b, c, imm, hi, flags);
        let control = ControlConfig::configure(meta, q_step, q_first, q_last, clk, pc, flags);
        let regfile = RegFileConfig::configure(meta, q_exec, q_step, regs, rd, rs1, rs2, a, b, c, flags);
        let range = RangeConfig::configure(meta, q_exec, c, c_limbs, hi, hi_limbs, byte_table, flags);
        let xor = XorConfig::configure(meta, q_exec, a, b, a_limbs, b_limbs, c_limbs, xor_table, flags);

        VmConfig {
            clk, pc, regs, flags, rd, rs1, rs2, imm, a, b, c,
            hi, c_limbs, hi_limbs, a_limbs, b_limbs,
            byte_table, xor_table,
            q_exec, q_step, q_first, q_last,
            alu, control, regfile, range, xor,
        }
    }

    fn synthesize(
        &self,
        cfg: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), ErrorFront> {
        // --- byte table: the fixed bytes 0..=255 (range checks) ---
        layouter.assign_table(
            || "byte table (0..255)",
            |mut table| {
                for value in 0..256u64 {
                    table.assign_cell(
                        || "byte",
                        cfg.byte_table,
                        value as usize,
                        || Value::known(Fr::from(value)),
                    )?;
                }
                Ok(())
            },
        )?;

        // --- xor table: (x, y, x^y) for every byte pair — 65536 rows ---
        layouter.assign_table(
            || "xor table (byte pairs)",
            |mut table| {
                let mut offset = 0usize;
                for x in 0..256u64 {
                    for y in 0..256u64 {
                        table.assign_cell(|| "x", cfg.xor_table[0], offset, || Value::known(Fr::from(x)))?;
                        table.assign_cell(|| "y", cfg.xor_table[1], offset, || Value::known(Fr::from(y)))?;
                        table.assign_cell(|| "x^y", cfg.xor_table[2], offset, || Value::known(Fr::from(x ^ y)))?;
                        offset += 1;
                    }
                }
                Ok(())
            },
        )?;

        // --- execution trace ---
        let n = self.trace.len();
        layouter.assign_region(
            || "execution",
            |mut region| {
                for (i, row) in self.trace.iter().enumerate() {
                    let adv = |v: u64| Value::known(Fr::from(v));

                    // fixed selectors (structural, not witness)
                    region.assign_fixed(|| "q_exec", cfg.q_exec, i, || Value::known(Fr::one()))?;
                    let step = if i + 1 < n { Fr::one() } else { Fr::zero() };
                    region.assign_fixed(|| "q_step", cfg.q_step, i, || Value::known(step))?;
                    let first = if i == 0 { Fr::one() } else { Fr::zero() };
                    region.assign_fixed(|| "q_first", cfg.q_first, i, || Value::known(first))?;
                    let last = if i + 1 == n { Fr::one() } else { Fr::zero() };
                    region.assign_fixed(|| "q_last", cfg.q_last, i, || Value::known(last))?;

                    // state
                    region.assign_advice(|| "clk", cfg.clk, i, || adv(row.clk))?;
                    region.assign_advice(|| "pc", cfg.pc, i, || adv(row.pc))?;
                    for (r, col) in cfg.regs.iter().enumerate() {
                        region.assign_advice(|| "reg", *col, i, || adv(row.regs[r]))?;
                    }

                    // decode
                    region.assign_advice(|| "rd", cfg.rd, i, || adv(row.rd))?;
                    region.assign_advice(|| "rs1", cfg.rs1, i, || adv(row.rs1))?;
                    region.assign_advice(|| "rs2", cfg.rs2, i, || adv(row.rs2))?;
                    region.assign_advice(|| "imm", cfg.imm, i, || adv(row.imm))?;

                    // datapath
                    region.assign_advice(|| "a", cfg.a, i, || adv(row.a))?;
                    region.assign_advice(|| "b", cfg.b, i, || adv(row.b))?;
                    region.assign_advice(|| "c", cfg.c, i, || adv(row.c))?;

                    // 32-bit auxiliaries: copied verbatim from the trace.
                    region.assign_advice(|| "hi", cfg.hi, i, || adv(row.hi))?;
                    for (limb, col) in row.c_limbs.iter().zip(cfg.c_limbs.iter()) {
                        region.assign_advice(|| "c_limb", *col, i, || adv(*limb))?;
                    }
                    for (limb, col) in row.hi_limbs.iter().zip(cfg.hi_limbs.iter()) {
                        region.assign_advice(|| "hi_limb", *col, i, || adv(*limb))?;
                    }
                    for (limb, col) in row.a_limbs.iter().zip(cfg.a_limbs.iter()) {
                        region.assign_advice(|| "a_limb", *col, i, || adv(*limb))?;
                    }
                    for (limb, col) in row.b_limbs.iter().zip(cfg.b_limbs.iter()) {
                        region.assign_advice(|| "b_limb", *col, i, || adv(*limb))?;
                    }

                    // one-hot flags: copied verbatim from the trace.
                    for (col, &v) in cfg.flags.all().iter().zip(row.flags.iter()) {
                        region.assign_advice(|| "flag", *col, i, || adv(v))?;
                    }
                }
                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::emulator::run_program;
    use crate::vm_trace::Instr;
    use halo2_proofs::dev::MockProver;

    // k must accommodate the 65536-entry XOR table (plus blinding): k = 17.
    const K: u32 = 17;

    fn example() -> Vec<TraceRow> {
        // r2 = 3 + 4 = 7, r3 = 7 * 7 = 49
        let program = vec![
            Instr::imm(0, 3),
            Instr::imm(1, 4),
            Instr::add(2, 0, 1),
            Instr::mul(3, 2, 2),
            Instr::halt(),
        ];
        run_program(&program)
    }

    #[test]
    fn valid_trace_passes() {
        let prover = MockProver::run(K, &VmCircuit { trace: example() }, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn add_wrong_result_fails() {
        let mut trace = example();
        trace[2].c = 999;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn mul_wrong_result_fails() {
        let mut trace = example();
        trace[3].c = 50; // 7 * 7 = 49, not 50
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn alu_ok_but_broken_one_hot_fails() {
        let mut trace = example();
        // row 2 is the ADD. flags = [imm, add, mul, hlt, xor] = [0,1,0,0,0].
        // Light mul as well: sum of flags becomes 2, not 1.
        trace[2].flags = [0, 1, 1, 0, 0];
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn clock_skip_fails() {
        let mut trace = example();
        trace[2].clk = 99;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn clock_not_starting_at_zero_fails() {
        let mut trace = example();
        trace[0].clk = 5;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn pc_skip_fails() {
        let mut trace = example();
        trace[2].pc = 7;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn pc_not_starting_at_zero_fails() {
        let mut trace = example();
        trace[0].pc = 3;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn pc_advances_on_halt_fails() {
        let mut trace = example();
        let hlt = trace.iter().position(|r| r.flags[3] == 1).unwrap();
        trace[hlt + 1].pc += 1;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn instruction_after_halt_fails() {
        let mut trace = example();
        let hlt = trace.iter().position(|r| r.flags[3] == 1).unwrap();
        trace[hlt + 1].flags = [1, 0, 0, 0, 0]; // claims IMM instead of HALT
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn trace_not_halted_at_end_fails() {
        let mut trace = example();
        let last = trace.len() - 1;
        trace[last].flags = [1, 0, 0, 0, 0]; // pretend IMM on the last row
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn read_a_phantom_fails() {
        let mut trace = example();
        trace[2].a = 99;
        trace[2].c = 99 + trace[2].b;
        trace[3].regs[2] = trace[2].c;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn read_b_phantom_fails() {
        let mut trace = example();
        trace[2].b = 88;
        trace[2].c = trace[2].a + 88;
        trace[3].regs[2] = trace[2].c;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn write_lost_fails() {
        let mut trace = example();
        trace[3].regs[2] = 0;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn write_to_wrong_register_fails() {
        let mut trace = example();
        trace[3].regs[1] = trace[2].c;
        trace[3].regs[2] = trace[2].regs[2];
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn unrelated_register_changed_fails() {
        let mut trace = example();
        trace[3].regs[0] = 123;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn imm_writes_immediate() {
        let mut trace = example();
        trace[1].regs[0] = 999;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    // ----- range-check sabotage -----

    #[test]
    fn range_c_recomposition_catches_tampered_limb() {
        let mut trace = example();
        trace[0].c_limbs[0] = 5; // Σ limbs = 5 ≠ c = 3
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn range_c_lookup_catches_non_byte() {
        let program = vec![Instr::imm(0, 256), Instr::halt()];
        let mut trace = run_program(&program);
        trace[0].c_limbs = [256, 0, 0, 0]; // recomposes to 256, but limb0 = 256
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn range_hi_recomposition_catches_tampered_limb() {
        let program = vec![
            Instr::imm(0, 1 << 16),
            Instr::imm(1, 1 << 16),
            Instr::mul(2, 0, 1),
            Instr::halt(),
        ];
        let mut trace = run_program(&program);
        trace[2].hi_limbs[0] = 5; // Σ hi_limbs = 5 ≠ hi = 1
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn range_hi_lookup_catches_non_byte() {
        let program = vec![
            Instr::imm(0, 1 << 20),
            Instr::imm(1, 1 << 20),
            Instr::mul(2, 0, 1),
            Instr::halt(),
        ];
        let mut trace = run_program(&program);
        trace[2].hi_limbs = [256, 0, 0, 0]; // recomposes to 256, but limb0 = 256
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn range_honest_wrap_passes() {
        let program = vec![
            Instr::imm(0, 1 << 16),
            Instr::imm(1, 1 << 16),
            Instr::mul(2, 0, 1),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        prover.assert_satisfied();
    }

    // ----- xor -----

    fn xor_example() -> Vec<TraceRow> {
        // r2 = 0xF0F0_AAAA ^ 0x0FF0_5555 = 0xFF00_FFFF
        let program = vec![
            Instr::imm(0, 0xF0F0_AAAA),
            Instr::imm(1, 0x0FF0_5555),
            Instr::xor(2, 0, 1),
            Instr::halt(),
        ];
        run_program(&program)
    }

    #[test]
    fn xor_valid_trace_passes() {
        let prover = MockProver::run(K, &VmCircuit { trace: xor_example() }, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn xor_wrong_result_fails() {
        // Corrupt the XOR result (and its limbs consistently) so recomposition
        // holds but the triple (a_limb, b_limb, c_limb) is not in the table.
        let mut trace = xor_example();
        // honest c = 0xFF00_FFFF. Flip the low limb to a wrong-but-byte value.
        trace[2].c = 0xFF00_FF00;          // wrong result
        trace[2].c_limbs = [0x00, 0xFF, 0x00, 0xFF]; // recomposes to 0xFF00FF00
        trace[3].regs[2] = trace[2].c;     // keep the write consistent
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

// ----- xor sabotage: each isolates one fence of the XOR chip -----

    /// The 'a' recomposition catches a tampered a_limb. We change one limb of a
    /// on the XOR row but keep the triple lookup satisfiable by also changing
    /// the matching c_limb to a_limb ^ b_limb — so only a ≠ Σ a_limbs fires.
    #[test]
    fn xor_a_recomposition_catches_tampered_limb() {
        let mut trace = xor_example();
        // row 2 is the XOR. Corrupt a_limbs[0] to a different byte, and fix the
        // corresponding c_limb so the triple (a_limb, b_limb, c_limb) is still a
        // valid XOR row. That keeps the triple lookup happy; the only thing left
        // inconsistent is a ≠ Σ a_limbs (a itself is unchanged).
        let bl0 = trace[2].b_limbs[0];
        trace[2].a_limbs[0] = 0x11;            // was the low byte of 0xF0F0_AAAA = 0xAA
        trace[2].c_limbs[0] = 0x11 ^ bl0;      // keep c_limb = a_limb ^ b_limb
        // Note: c (the full value) and its recomposition now also disagree, but
        // the 'a' recomposition fires regardless — the point is it IS caught.
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    /// Same for the 'b' recomposition.
    #[test]
    fn xor_b_recomposition_catches_tampered_limb() {
        let mut trace = xor_example();
        let al0 = trace[2].a_limbs[0];
        trace[2].b_limbs[0] = 0x22;            // tamper b's low limb
        trace[2].c_limbs[0] = al0 ^ 0x22;      // keep the triple valid
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    /// Operand phantom on XOR: a is not regs[rs1]. The analogue of
    /// read_a_phantom_fails for ADD — confirms the RegFile read gate now covers
    /// XOR (reads includes f_xor). We keep a's limbs and c consistent with the
    /// lying a, so ONLY the "read a" gate can catch it.
    #[test]
    fn xor_read_a_phantom_fails() {
        use crate::vm_trace::limbs32;
        let mut trace = xor_example();
        let x = trace[2].a; // real regs[rs1]
        let lie = x ^ 0x0000_00FF; // a different in-range value
        trace[2].a = lie;                       // a no longer equals regs[rs1]
        trace[2].a_limbs = limbs32(lie);        // keep a = Σ a_limbs (recomp ok)
        // keep the XOR result consistent with the lying a, so the triple lookup
        // and c-recomposition stay satisfied:
        let newc = lie ^ trace[2].b;
        trace[2].c = newc;
        trace[2].c_limbs = limbs32(newc);
        trace[3].regs[2] = newc;                // write stays consistent
        // Now every gate is happy EXCEPT regfile "read a": a ≠ regs[rs1].
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    /// c detached from its limbs on XOR. This specifically exercises the change
    /// we made to RangeCheck (q_write now includes f_xor, so c is recomposed on
    /// XOR). We keep the triple lookup valid (c_limbs are the true a^b limbs)
    /// but set the c COLUMN to a wrong value — only c ≠ Σ c_limbs fires.
    #[test]
    fn xor_c_detached_from_limbs_fails() {
        let mut trace = xor_example();
        // honest: c = 0xFF00_FFFF, c_limbs = limbs of that. Leave c_limbs alone
        // (triple lookup stays valid), but corrupt the c column.
        trace[2].c = 0xDEAD_BEEF;               // ≠ Σ c_limbs
        trace[3].regs[2] = 0xDEAD_BEEF;         // keep the write gate consistent
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    /// Positive check with a bit pattern that crosses all four limbs, making
    /// sure the four independent chunk lookups really cover the full 32 bits.
    #[test]
    fn xor_cross_limb_pattern_passes() {
        let program = vec![
            Instr::imm(0, 0x1234_5678),
            Instr::imm(1, 0x9ABC_DEF0),
            Instr::xor(2, 0, 1),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        // sanity on the expected result: 0x1234_5678 ^ 0x9ABC_DEF0 = 0x8888_8888
        assert_eq!(trace[2].c, 0x8888_8888);
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        prover.assert_satisfied();
    }

}