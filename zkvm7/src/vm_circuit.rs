// vm_circuit.rs — top-level circuit.
//
// Role of the top-level: allocate ALL shared columns, impose the flag
// constraints (boolean + one-hot), and assign the full trace. Chips are
// plugged in here one at a time, each adding its own constraints over these
// same shared columns.
//
// Plugged in: Flags (one-hot, here), ALU, Control, RegFile, RangeCheck, Xor,
// Memory. The Memory chip owns the per-row access columns (mem_addr, mem_value,
// mem_type, mem_active), binds them to the datapath (a, b, c) and the opcode
// flags, and runs the offline memory-consistency argument over the sorted table
// (s_*), the is-zero witness (d_inv), the ordering limbs, and the grand-product
// accumulator z. So LOAD/STORE are now fully verified: a LOAD returns the value
// of the most recent STORE to its address (0 if never written).
//
// NOTE on k: the XOR table holds 256×256 = 65536 entries, so k = 17.

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
use crate::memory::MemoryConfig;

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
    pub hi: Column<Advice>,
    pub c_limbs: [Column<Advice>; 4],
    pub hi_limbs: [Column<Advice>; 4],
    pub a_limbs: [Column<Advice>; 4],
    pub b_limbs: [Column<Advice>; 4],
    // memory access (bound to datapath + flags by the Memory chip)
    pub mem_addr: Column<Advice>,
    pub mem_value: Column<Advice>,
    pub mem_type: Column<Advice>,
    pub mem_active: Column<Advice>,
    // sorted memory table + grand product (memory-consistency argument)
    pub s_active: Column<Advice>,
    pub s_addr: Column<Advice>,
    pub s_value: Column<Advice>,
    pub s_clk: Column<Advice>,
    pub s_type: Column<Advice>,
    pub d_inv: Column<Advice>,
    pub addr_delta_limbs: [Column<Advice>; 4],
    pub clk_delta_limbs: [Column<Advice>; 4],
    pub z: Column<Advice>,
    // fixed-data lookup tables
    pub byte_table: TableColumn,
    pub xor_table: [TableColumn; 3],
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
    pub memory: MemoryConfig,
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
            load: meta.advice_column(),
            store: meta.advice_column(),
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

        // memory access columns
        let mem_addr = meta.advice_column();
        let mem_value = meta.advice_column();
        let mem_type = meta.advice_column();
        let mem_active = meta.advice_column();

        // sorted memory table + grand product columns
        let s_active = meta.advice_column();
        let s_addr = meta.advice_column();
        let s_value = meta.advice_column();
        let s_clk = meta.advice_column();
        let s_type = meta.advice_column();
        let d_inv = meta.advice_column();
        let addr_delta_limbs = mk4(meta);
        let clk_delta_limbs = mk4(meta);
        let z = meta.advice_column();

        // lookup tables
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

        // --- flag constraints (boolean + one-hot). Iterates flags.all(), so it
        // already covers the new load/store flags with no change to the logic.
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
        let memory = MemoryConfig::configure(
            meta, q_exec, q_step, q_first, q_last, clk,
            a, b, c,
            mem_addr, mem_value, mem_type, mem_active,
            s_active, s_addr, s_value, s_clk, s_type,
            d_inv, addr_delta_limbs, clk_delta_limbs, z,
            byte_table, flags,
        );

        VmConfig {
            clk, pc, regs, flags, rd, rs1, rs2, imm, a, b, c,
            hi, c_limbs, hi_limbs, a_limbs, b_limbs,
            mem_addr, mem_value, mem_type, mem_active,
            s_active, s_addr, s_value, s_clk, s_type,
            d_inv, addr_delta_limbs, clk_delta_limbs, z,
            byte_table, xor_table,
            q_exec, q_step, q_first, q_last,
            alu, control, regfile, range, xor, memory,
        }
    }

    fn synthesize(
        &self,
        cfg: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), ErrorFront> {
        // --- byte table: 0..=255 ---
        layouter.assign_table(
            || "byte table (0..255)",
            |mut table| {
                for value in 0..256u64 {
                    table.assign_cell(|| "byte", cfg.byte_table, value as usize, || Value::known(Fr::from(value)))?;
                }
                Ok(())
            },
        )?;

        // --- xor table: (x, y, x^y) for every byte pair ---
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

                    region.assign_fixed(|| "q_exec", cfg.q_exec, i, || Value::known(Fr::one()))?;
                    let step = if i + 1 < n { Fr::one() } else { Fr::zero() };
                    region.assign_fixed(|| "q_step", cfg.q_step, i, || Value::known(step))?;
                    let first = if i == 0 { Fr::one() } else { Fr::zero() };
                    region.assign_fixed(|| "q_first", cfg.q_first, i, || Value::known(first))?;
                    let last = if i + 1 == n { Fr::one() } else { Fr::zero() };
                    region.assign_fixed(|| "q_last", cfg.q_last, i, || Value::known(last))?;

                    region.assign_advice(|| "clk", cfg.clk, i, || adv(row.clk))?;
                    region.assign_advice(|| "pc", cfg.pc, i, || adv(row.pc))?;
                    for (r, col) in cfg.regs.iter().enumerate() {
                        region.assign_advice(|| "reg", *col, i, || adv(row.regs[r]))?;
                    }

                    region.assign_advice(|| "rd", cfg.rd, i, || adv(row.rd))?;
                    region.assign_advice(|| "rs1", cfg.rs1, i, || adv(row.rs1))?;
                    region.assign_advice(|| "rs2", cfg.rs2, i, || adv(row.rs2))?;
                    region.assign_advice(|| "imm", cfg.imm, i, || adv(row.imm))?;

                    region.assign_advice(|| "a", cfg.a, i, || adv(row.a))?;
                    region.assign_advice(|| "b", cfg.b, i, || adv(row.b))?;
                    region.assign_advice(|| "c", cfg.c, i, || adv(row.c))?;

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

                    // memory access columns (bound by the Memory chip)
                    region.assign_advice(|| "mem_addr", cfg.mem_addr, i, || adv(row.mem_addr))?;
                    region.assign_advice(|| "mem_value", cfg.mem_value, i, || adv(row.mem_value))?;
                    region.assign_advice(|| "mem_type", cfg.mem_type, i, || adv(row.mem_type))?;
                    region.assign_advice(|| "mem_active", cfg.mem_active, i, || adv(row.mem_active))?;

                    // sorted memory table + grand product
                    region.assign_advice(|| "s_active", cfg.s_active, i, || adv(row.s_active))?;
                    region.assign_advice(|| "s_addr", cfg.s_addr, i, || adv(row.s_addr))?;
                    region.assign_advice(|| "s_value", cfg.s_value, i, || adv(row.s_value))?;
                    region.assign_advice(|| "s_clk", cfg.s_clk, i, || adv(row.s_clk))?;
                    region.assign_advice(|| "s_type", cfg.s_type, i, || adv(row.s_type))?;
                    // d_inv and z are field elements: assigned directly, not via Fr::from(u64)
                    region.assign_advice(|| "d_inv", cfg.d_inv, i, || Value::known(row.d_inv))?;
                    region.assign_advice(|| "z", cfg.z, i, || Value::known(row.z))?;
                    for (limb, col) in row.addr_delta_limbs.iter().zip(cfg.addr_delta_limbs.iter()) {
                        region.assign_advice(|| "addr_delta_limb", *col, i, || adv(*limb))?;
                    }
                    for (limb, col) in row.clk_delta_limbs.iter().zip(cfg.clk_delta_limbs.iter()) {
                        region.assign_advice(|| "clk_delta_limb", *col, i, || adv(*limb))?;
                    }

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

    const K: u32 = 17;

    fn example() -> Vec<TraceRow> {
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
        trace[3].c = 50;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn alu_ok_but_broken_one_hot_fails() {
        let mut trace = example();
        trace[2].flags = [0, 1, 1, 0, 0, 0, 0];
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
        trace[hlt + 1].flags = [1, 0, 0, 0, 0, 0, 0];
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn trace_not_halted_at_end_fails() {
        let mut trace = example();
        let last = trace.len() - 1;
        trace[last].flags = [1, 0, 0, 0, 0, 0, 0];
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
        trace[0].c_limbs[0] = 5;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn range_c_lookup_catches_non_byte() {
        let program = vec![Instr::imm(0, 256), Instr::halt()];
        let mut trace = run_program(&program);
        trace[0].c_limbs = [256, 0, 0, 0];
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
        trace[2].hi_limbs[0] = 5;
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
        trace[2].hi_limbs = [256, 0, 0, 0];
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
        let mut trace = xor_example();
        trace[2].c = 0xFF00_FF00;
        trace[2].c_limbs = [0x00, 0xFF, 0x00, 0xFF];
        trace[3].regs[2] = trace[2].c;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn xor_a_recomposition_catches_tampered_limb() {
        let mut trace = xor_example();
        let bl0 = trace[2].b_limbs[0];
        trace[2].a_limbs[0] = 0x11;
        trace[2].c_limbs[0] = 0x11 ^ bl0;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn xor_b_recomposition_catches_tampered_limb() {
        let mut trace = xor_example();
        let al0 = trace[2].a_limbs[0];
        trace[2].b_limbs[0] = 0x22;
        trace[2].c_limbs[0] = al0 ^ 0x22;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn xor_read_a_phantom_fails() {
        use crate::vm_trace::limbs32;
        let mut trace = xor_example();
        let x = trace[2].a;
        let lie = x ^ 0x0000_00FF;
        trace[2].a = lie;
        trace[2].a_limbs = limbs32(lie);
        let newc = lie ^ trace[2].b;
        trace[2].c = newc;
        trace[2].c_limbs = limbs32(newc);
        trace[3].regs[2] = newc;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn xor_c_detached_from_limbs_fails() {
        let mut trace = xor_example();
        trace[2].c = 0xDEAD_BEEF;
        trace[3].regs[2] = 0xDEAD_BEEF;
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn xor_cross_limb_pattern_passes() {
        let program = vec![
            Instr::imm(0, 0x1234_5678),
            Instr::imm(1, 0x9ABC_DEF0),
            Instr::xor(2, 0, 1),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        assert_eq!(trace[2].c, 0x8888_8888);
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        prover.assert_satisfied();
    }

    // ----- memory: honest LOAD/STORE now fully verified -----

    fn mem_example() -> Vec<TraceRow> {
        // r0 = 42 (value), r1 = 3 (address); STORE m[r1]=r0; LOAD r2=m[r1].
        let program = vec![
            Instr::imm(0, 42),
            Instr::imm(1, 3),
            Instr::store(1, 0), // m[r1] = r0  -> m[3] = 42
            Instr::load(2, 1),  // r2 = m[r1]  -> r2 = 42
            Instr::halt(),
        ];
        run_program(&program)
    }

    /// The honest LOAD/STORE trace passes the full circuit, now including the
    /// memory-consistency argument (access binding + grand product + read rule).
    #[test]
    fn mem_valid_trace_passes() {
        let prover = MockProver::run(K, &VmCircuit { trace: mem_example() }, vec![]).unwrap();
        prover.assert_satisfied();
    }

    /// STORE must not write a register: on the STORE row, is_write = 0, so every
    /// register copies. Tampering a register across the STORE row must fail the
    /// RegFile write gate (this part IS already enforced, independent of the
    /// memory argument).
    #[test]
    fn store_does_not_write_register_fails_if_tampered() {
        let mut trace = mem_example();
        // row 2 is the STORE. Force a register to change across it.
        trace[3].regs[0] = 999; // regs must be frozen on STORE -> this breaks it
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    /// LOAD writes its c into rd: corrupting the destination register on the
    /// next row must fail the RegFile write gate (also already enforced).
    #[test]
    fn load_writes_destination_fails_if_lost() {
        let mut trace = mem_example();
        // row 3 is the LOAD (rd = 2). It writes 42 into regs[2] on row 4.
        trace[4].regs[2] = 0; // erase the loaded value
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    // ----- memory-consistency sabotage (Stage 1: fixed challenges) -----
    // The memory argument has three layers of fence: (1) access binding ties
    // mem_* to the datapath a/b/c and the flags; (2) the grand product ties the
    // sorted table to the trace multiset; (3) the read rules enforce
    // read-after-write on the sorted table. Each test pierces one layer while
    // satisfying the earlier ones. Where a corrupted fingerprint leaves z stale,
    // the Z recurrence co-fires — noted per test. Tests that must isolate a read
    // rule rebuild a consistent witness first (rebuild_memory_witness).

    /// Two stores to DIFFERENT addresses: the sorted table crosses an address
    /// boundary, exercising the addr-ordering and is-zero fences in isolation.
    fn mem_two_addr_example() -> Vec<TraceRow> {
        let program = vec![
            Instr::imm(0, 3),   // r0 = 3  (addr A)
            Instr::imm(1, 5),   // r1 = 5  (addr B)
            Instr::imm(2, 100), // r2 = 100 (value)
            Instr::store(0, 2), // m[3] = 100  (clk 3)
            Instr::store(1, 2), // m[5] = 100  (clk 4)
            Instr::halt(),
        ];
        run_program(&program)
    }

    /// LAYER 1 (access binding), ISOLATED. A LOAD's datapath c is forged to 99
    /// but the access column mem_value still carries the true stored 42. The
    /// binding f_load*(mem_value - c) fires. c_limbs and regs are patched so
    /// Range and RegFile stay satisfied; mem_value is untouched, so z stays
    /// valid and the grand product does not co-fire. This is the anchor: the
    /// value a LOAD delivers to the register must equal the access it records.
    #[test]
    fn mem_load_wrong_c_fails() {
        let mut trace = mem_example();
        trace[3].c = 99; // LOAD row
        trace[3].c_limbs = crate::vm_trace::limbs32(99); // keep Range happy
        trace[4].regs[2] = 99; // keep RegFile happy
        // trace[3].mem_value stays 42 -> binding mem_value = c breaks.
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    /// LAYER 3 (read-after-write), ISOLATED. The core anchor: a LOAD returns a
    /// value different from the most recent WRITE to its address. We forge the
    /// read to 99 consistently (datapath + access column + register) and REBUILD
    /// the witness, so the binding and the grand product both pass — the sorted
    /// READ row now sits right after the WRITE(42) but carries 99, and the step
    /// read-value rule (val_next = val_cur) rejects it alone.
    #[test]
    fn mem_load_wrong_value_consistency_fails() {
        let mut trace = mem_example();
        trace[3].c = 99;
        trace[3].c_limbs = crate::vm_trace::limbs32(99);
        trace[3].mem_value = 99; // forge the recorded read value
        trace[4].regs[2] = 99;
        crate::emulator::rebuild_memory_witness(&mut trace);
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    /// LAYER 2 (grand product), and it shows CONSISTENCY ALONE IS NOT ENOUGH.
    /// Both sorted value cells (the WRITE and the READ to addr 3) are relabelled
    /// 99, so the read rule still holds internally (99 = 99). But the trace side
    /// still records 42, so the sorted table is no longer a permutation of the
    /// trace — the grand product (stale z) rejects it. Consistency passes; only
    /// the permutation fence stands.
    #[test]
    fn mem_forged_sorted_value_fails() {
        let mut trace = mem_example();
        trace[0].s_value = 99; // sorted WRITE row
        trace[1].s_value = 99; // sorted READ row
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    /// ORDERING (addr non-decreasing), ISOLATED. The addr-delta limbs must
    /// recompose to s_addr[next] - s_addr[cur] = 2. Tampering one limb to 7
    /// trips the recompose gate alone: limbs are not fingerprinted (grand
    /// product untouched), 7 is a valid byte (lookup passes), and d_inv is
    /// unchanged (is-zero passes).
    #[test]
    fn mem_addr_ordering_recompose_fails() {
        let mut trace = mem_two_addr_example();
        trace[0].addr_delta_limbs[0] = 7; // true delta 3->5 is 2, not 7
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    /// IS-ZERO GADGET, ISOLATED. With two different addresses the delta d = 2
    /// != 0, so d_inv must be 1/d and same_addr = 0. Forcing d_inv = 0 makes
    /// same_addr = 1 while d != 0, so the gate d*(1 - d*d_inv) fires. d_inv is
    /// not fingerprinted, so the grand product is untouched.
    #[test]
    fn mem_is_zero_gadget_fails() {
        let mut trace = mem_two_addr_example();
        trace[0].d_inv = Fr::zero(); // true delta is 2 != 0
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    /// ROW-0 READ RULE, ISOLATED — guards the top of the sorted table. A LOAD of
    /// a never-written address (0) lands at sorted position 0, where the step
    /// rule can't see it. We forge it to read 99 and rebuild, so binding and
    /// grand product pass; only the q_first row-0 gate (s_value = 0) rejects it.
    /// Comment out that gate and this test passes — proving the fence is
    /// load-bearing, not decorative.
    #[test]
    fn mem_row0_read_must_be_zero() {
        let program = vec![
            Instr::imm(0, 0),  // r0 = 0 (address 0, never written)
            Instr::load(1, 0), // r1 = m[0]  (honest 0)
            Instr::halt(),
        ];
        let mut trace = run_program(&program);
        trace[1].c = 99;
        trace[1].c_limbs = crate::vm_trace::limbs32(99);
        trace[1].mem_value = 99;
        trace[2].regs[1] = 99;
        crate::emulator::rebuild_memory_witness(&mut trace);
        let prover = MockProver::run(K, &VmCircuit { trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }
}