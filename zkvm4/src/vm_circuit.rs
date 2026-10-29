// vm_circuit.rs — top-level circuit.
//
// Role of the top-level: allocate ALL shared columns, impose the flag
// constraints (boolean + one-hot), and assign the full trace. Chips are
// plugged in here one at a time, each adding its own constraints over these
// same shared columns.
//
// Currently plugged in: Flags (one-hot, here) and ALU. Still free (no chip
// reads them yet): clk, pc, regs, rd, rs1, rs2, q_step, q_first, q_last.
//
// synthesize computes nothing about the trace content: every advice column,
// including the one-hot flags, is copied verbatim from the trace. Only the
// fixed selectors q_* are structural (derived from the row position), because
// they are not part of the witness.

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::bn256::Fr,
    plonk::{Advice, Circuit, Column, ConstraintSystem, ErrorFront, Expression, Fixed},
    poly::Rotation,
};

use crate::alu::AluConfig;
use crate::flags::OpFlags;
use crate::vm_trace::TraceRow;
use crate::control::ControlConfig;
use crate::regfile::RegFileConfig;

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
    // fixed selectors
    pub q_exec: Column<Fixed>,
    pub q_step: Column<Fixed>,
    pub q_first: Column<Fixed>,
    pub q_last: Column<Fixed>,
    // chips
    pub alu: AluConfig,
    pub control: ControlConfig,
    pub regfile: RegFileConfig,
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
        };
        let rd = meta.advice_column();
        let rs1 = meta.advice_column();
        let rs2 = meta.advice_column();
        let imm = meta.advice_column();
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let q_exec = meta.fixed_column();
        let q_step = meta.fixed_column();
        let q_first = meta.fixed_column();
        let q_last = meta.fixed_column();

        // --- flag constraints: owned by whoever allocates them (top-level) ---

        // if the flags (is_add, is_mul, is_imm, is_halt) should be binary
        // only one can be 1, is_add + is_mul + is_imm + is_halt = 1

        meta.create_gate("flags: boolean and one-hot", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let one = Expression::Constant(Fr::one());

            let fs = flags.all().map(|col| meta.query_advice(col, Rotation::cur()));

            let mut constraints = Vec::new();
            // each flag is boolean: f * (f - 1) = 0
            for f in fs.iter() {
                constraints.push(q.clone() * f.clone() * (f.clone() - one.clone()));
            }
            // exactly one is set: sum of flags = 1
            let mut sum = Expression::Constant(Fr::zero());
            for f in fs.iter() {
                sum = sum + f.clone();
            }
            constraints.push(q * (sum - one));
            constraints
        });

        // --- chips ---
        let alu = AluConfig::configure(meta, q_exec, a, b, c, imm, flags);
        let control = ControlConfig::configure(meta, q_step, q_first, q_last, clk, pc, flags);
        let regfile = RegFileConfig::configure(meta, q_exec, q_step, regs, rd, rs1, rs2, a, b, c, flags);

        VmConfig {
            clk, pc, regs, flags, rd, rs1, rs2, imm, a, b, c,
            q_exec, q_step, q_first, q_last, alu, control, regfile
        }
    }

    fn synthesize(
        &self,
        cfg: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), ErrorFront> {
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

                    // one-hot flags: copied verbatim from the trace, not
                    // derived here — synthesize computes nothing.
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
        let prover = MockProver::run(6, &VmCircuit { trace: example() }, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn add_wrong_result_fails() {
        // c is not a + b: the ADD gate rejects it
        let mut trace = example();
        trace[2].c = 999;
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn mul_wrong_result_fails() {
        // c is not a * b: the MUL gate rejects it
        let mut trace = example();
        trace[3].c = 50; // 7 * 7 = 49, not 50
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn alu_ok_but_broken_one_hot_fails() {
        // The ADD row is arithmetically correct (c = a + b = 7), so every ALU
        // gate is satisfied. But we light a second flag on that row, breaking
        // the one-hot invariant. Only the top-level one-hot gate catches this.
        let mut trace = example();
        // row 2 is the ADD. flags = [imm, add, mul, hlt] = [0, 1, 0, 0].
        // Light mul as well: sum of flags becomes 2, not 1.
        trace[2].flags = [0, 1, 1, 0];
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }


    #[test]
    fn clock_skip_fails() {
        // clk jumps instead of incrementing by 1
        let mut trace = example();
        trace[2].clk = 99;
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn clock_not_starting_at_zero_fails() {
        // clk[0] != 0 breaks the anchor (and the first step)
        let mut trace = example();
        trace[0].clk = 5;
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn pc_skip_fails() {
        // pc jumps on an ordinary instruction (should be +1)
        let mut trace = example();
        trace[2].pc = 7;
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn pc_not_starting_at_zero_fails() {
        let mut trace = example();
        trace[0].pc = 3;
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn pc_advances_on_halt_fails() {
        // On the HALT row the pc must freeze. Force it to advance in the padding
        // and the pc gate (halt case) rejects it.
        let mut trace = example();
        // find the first HALT row, then bump the pc of the row AFTER it so that
        // pc' - pc = 1 on a HALT transition.
        let hlt = trace.iter().position(|r| r.flags[3] == 1).unwrap();
        // the transition at `hlt` compares row hlt and hlt+1
        trace[hlt + 1].pc += 1;
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn instruction_after_halt_fails() {
        // Break HALT absorption: a non-HALT flag on a row past the first HALT.
        let mut trace = example();
        let hlt = trace.iter().position(|r| r.flags[3] == 1).unwrap();
        // the row after HALT claims to be IMM instead of HALT
        trace[hlt + 1].flags = [1, 0, 0, 0];
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn trace_not_halted_at_end_fails() {
        // The very last row must be HALT. Force it to another opcode.
        let mut trace = example();
        let last = trace.len() - 1;
        trace[last].flags = [1, 0, 0, 0]; // pretend IMM on the last row
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }    

    #[test]
    fn read_a_phantom_fails() {
        // On the ADD row, a is not regs[rs1]. We keep the ALU happy by adjusting c
        // so that c = a + b still holds, and keep the write consistent — so ONLY
        // the "read a" gate can catch it.
        let mut trace = example();
        // row 2 is ADD r2 = r0 + r1, with a=3 (regs[0]), b=4 (regs[1]), c=7.
        trace[2].a = 99; // lie: a is no longer regs[rs1]
        trace[2].c = 99 + trace[2].b; // ALU stays satisfied (99 + 4 = 103)
        // the result written next row must match the (lying) c, so the write gate
        // stays satisfied too:
        trace[3].regs[2] = trace[2].c; // regs[2] becomes 103 on the next row
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn read_b_phantom_fails() {
        // Same idea for b on the ADD row.
        let mut trace = example();
        trace[2].b = 88;
        trace[2].c = trace[2].a + 88; // ALU satisfied (3 + 88 = 91)
        trace[3].regs[2] = trace[2].c;
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn write_lost_fails() {
        // The ADD result does not appear in the destination register next row.
        let mut trace = example();
        // row 2 ADD writes regs[2] = 7 on row 3. Erase it.
        trace[3].regs[2] = 0;
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn write_to_wrong_register_fails() {
        // The result lands in a register that is not rd.
        let mut trace = example();
        // row 2 ADD has rd = 2. Put the result in regs[1] instead and leave regs[2]
        // unchanged.
        trace[3].regs[1] = trace[2].c; // wrong destination
        trace[3].regs[2] = trace[2].regs[2]; // rd not updated
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn unrelated_register_changed_fails() {
        // A register the instruction never touched changes across a row.
        // This is what the "copy" part of the write gate protects.
        let mut trace = example();
        // row 2 ADD only writes regs[2]. Tamper with regs[0] on the next row.
        trace[3].regs[0] = 123;
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn imm_writes_immediate() {
        // Positive check: IMM writes regs[rd] = imm on the next row.
        // Corrupting that link must fail.
        let mut trace = example();
        // row 0 is IMM r0 = 3, so regs[0] must be 3 on row 1.
        trace[1].regs[0] = 999;
        let prover = MockProver::run(6, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }    
}