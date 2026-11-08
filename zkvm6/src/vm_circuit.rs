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
// accumulator z. LOAD/STORE are fully verified.
//
// STAGE 2 (zkvm5): the grand-product challenges beta/gamma are real Fiat-Shamir
// challenges (challenge_usable_after(FirstPhase)), and z is a SecondPhase advice
// column. First-phase columns are committed first; the challenge is derived from
// that commitment; then z is computed here in the second phase (see compute_z).
//
// FETCH: the decode columns (op/rd/rs1/rs2/imm) are bound to a program ROM by a
// lookup, so every executed row must match the instruction the program holds at
// that pc. The opcode is carried as a numeric `op` column, recomposed from the
// one-hot flags by a gate (op = Σ i·flag_i).
//
// JUMPI (this stage): a conditional jump, so the pc is no longer monotone. Two
// new pieces here: (1) the `a_inv` column — the is-nonzero witness (1/a or 0)
// the Control chip uses to test regs[rs1] != 0; (2) the OpFlags gain a `jumpi`
// flag. Control now receives a, a_inv, imm and does the three-way pc step
// (normal / HALT freeze / JUMPI conditional). clk still advances by 1 every row,
// so the memory argument is untouched.
//
// The ROM is ADVICE (not fixed): the same circuit/vk works for any program; a
// public hash of the ROM is what will pin *which* program. Padding rows copy the
// HALT row, so they match the program's own HALT entry.
//
// CONSCIOUS HOLE (hash of the ROM): the ROM is committed as advice but not tied
// to a public value yet. Deferred — see the commented block in configure.
//
// NOTE on k: the XOR table holds 256×256 = 65536 entries, so k = 17.

use halo2_proofs::{
    arithmetic::Field,
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::bn256::Fr,
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, ErrorFront, Expression,
        FirstPhase, Fixed, SecondPhase, TableColumn,
    },
    poly::Rotation,
};

use crate::alu::AluConfig;
use crate::flags::OpFlags;
use crate::vm_trace::{Instr, TraceRow, Op};
use crate::control::ControlConfig;
use crate::regfile::RegFileConfig;
use crate::range::RangeConfig;
use crate::xor::XorConfig;
use crate::memory::MemoryConfig;

/// Fixed ROM capacity (max program length the circuit supports). q_rom marks
/// these rows as valid ROM entries, INDEPENDENT of the actual program length —
/// this is what keeps the Fixed column identical between keygen (empty witness)
/// and prove (real program). Programs shorter than ROM_CAP pad the ROM with
/// HALT, which is never fetched (the pc freezes at the program's own HALT).
/// A larger program needs a larger ROM_CAP and a fresh key.
pub const ROM_CAP: usize = 64;

#[derive(Clone, Debug)]
pub struct VmConfig {
    pub clk: Column<Advice>,
    pub pc: Column<Advice>,
    pub regs: [Column<Advice>; 4],
    pub flags: OpFlags,
    pub op: Column<Advice>,
    pub rd: Column<Advice>,
    pub rs1: Column<Advice>,
    pub rs2: Column<Advice>,
    pub imm: Column<Advice>,
    pub a: Column<Advice>,
    pub b: Column<Advice>,
    pub c: Column<Advice>,
    /// is-nonzero witness for `a` (1/a or 0). Used by Control for JUMPI.
    pub a_inv: Column<Advice>,
    pub hi: Column<Advice>,
    pub c_limbs: [Column<Advice>; 4],
    pub hi_limbs: [Column<Advice>; 4],
    pub a_limbs: [Column<Advice>; 4],
    pub b_limbs: [Column<Advice>; 4],
    pub mem_addr: Column<Advice>,
    pub mem_value: Column<Advice>,
    pub mem_type: Column<Advice>,
    pub mem_active: Column<Advice>,
    pub s_active: Column<Advice>,
    pub s_addr: Column<Advice>,
    pub s_value: Column<Advice>,
    pub s_clk: Column<Advice>,
    pub s_type: Column<Advice>,
    pub d_inv: Column<Advice>,
    pub addr_delta_limbs: [Column<Advice>; 4],
    pub clk_delta_limbs: [Column<Advice>; 4],
    pub z: Column<Advice>,
    pub rom_pc: Column<Advice>,
    pub rom_op: Column<Advice>,
    pub rom_rd: Column<Advice>,
    pub rom_rs1: Column<Advice>,
    pub rom_rs2: Column<Advice>,
    pub rom_imm: Column<Advice>,
    pub q_rom: Column<Fixed>,
    pub byte_table: TableColumn,
    pub xor_table: [TableColumn; 3],
    pub q_exec: Column<Fixed>,
    pub q_step: Column<Fixed>,
    pub q_first: Column<Fixed>,
    pub q_last: Column<Fixed>,
    pub alu: AluConfig,
    pub control: ControlConfig,
    pub regfile: RegFileConfig,
    pub range: RangeConfig,
    pub xor: XorConfig,
    pub memory: MemoryConfig,
}

#[derive(Clone, Default, Debug)]
pub struct VmCircuit {
    pub program: Vec<Instr>,
    pub trace: Vec<TraceRow>,
}

fn compute_z(trace: &[TraceRow], beta: Fr, gamma: Fr) -> Vec<Fr> {
    let n = trace.len();
    let fp = |active: u64, addr: u64, value: u64, clk: u64, ty: u64| -> Fr {
        Fr::from(active)
            + Fr::from(addr) * beta
            + Fr::from(value) * beta * beta
            + Fr::from(clk) * beta * beta * beta
            + Fr::from(ty) * beta * beta * beta * beta
    };

    let mut z = vec![Fr::one(); n];
    let mut acc = Fr::one();
    z[0] = acc;
    for i in 0..n - 1 {
        let tf = if trace[i].mem_active == 1 {
            gamma + fp(
                trace[i].mem_active,
                trace[i].mem_addr,
                trace[i].mem_value,
                trace[i].clk,
                trace[i].mem_type,
            )
        } else {
            Fr::one()
        };
        let sf = if trace[i].s_active == 1 {
            gamma + fp(
                trace[i].s_active,
                trace[i].s_addr,
                trace[i].s_value,
                trace[i].s_clk,
                trace[i].s_type,
            )
        } else {
            Fr::one()
        };
        acc = acc * tf * sf.invert().unwrap();
        z[i + 1] = acc;
    }
    z
}

impl Circuit<Fr> for VmCircuit {
    type Config = VmConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
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
            jumpi: meta.advice_column(),
        };
        let op = meta.advice_column();
        let rd = meta.advice_column();
        let rs1 = meta.advice_column();
        let rs2 = meta.advice_column();
        let imm = meta.advice_column();
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let a_inv = meta.advice_column();

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

        let mem_addr = meta.advice_column();
        let mem_value = meta.advice_column();
        let mem_type = meta.advice_column();
        let mem_active = meta.advice_column();

        let s_active = meta.advice_column();
        let s_addr = meta.advice_column();
        let s_value = meta.advice_column();
        let s_clk = meta.advice_column();
        let s_type = meta.advice_column();
        let d_inv = meta.advice_column();
        let addr_delta_limbs = mk4(meta);
        let clk_delta_limbs = mk4(meta);

        let z = meta.advice_column_in(SecondPhase);

        let rom_pc = meta.advice_column();
        let rom_op = meta.advice_column();
        let rom_rd = meta.advice_column();
        let rom_rs1 = meta.advice_column();
        let rom_rs2 = meta.advice_column();
        let rom_imm = meta.advice_column();
        let q_rom = meta.fixed_column();

        let beta = meta.challenge_usable_after(FirstPhase);
        let gamma = meta.challenge_usable_after(FirstPhase);

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

        // --- flags: boolean + one-hot (iterates flags.all(), covers jumpi) ---
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

        // --- op = Σ i·flags[i] (Imm=0,…,Store=6,Jumpi=7) ---
        meta.create_gate("op = recompose(flags)", |meta| {
            let q = meta.query_fixed(q_exec, Rotation::cur());
            let op_e = meta.query_advice(op, Rotation::cur());
            let fs = flags.all().map(|col| meta.query_advice(col, Rotation::cur()));
            let mut acc = Expression::Constant(Fr::zero());
            for (i, f) in fs.iter().enumerate() {
                acc = acc + Expression::Constant(Fr::from(i as u64)) * f.clone();
            }
            vec![q * (op_e - acc)]
        });

        // --- FETCH lookup: decode tuple ∈ ROM (advice → lookup_any). PSE fork
        // needs a leading pure tag pair (q_exec, q_rom) plus each data pair
        // tagged (both sides × selector). ---
        meta.lookup_any("fetch: (pc,op,rd,rs1,rs2,imm) in ROM", |meta| {
            let q_exec_e = meta.query_fixed(q_exec, Rotation::cur());
            let q_rom_e = meta.query_fixed(q_rom, Rotation::cur());

            let pc_e = meta.query_advice(pc, Rotation::cur());
            let op_e = meta.query_advice(op, Rotation::cur());
            let rd_e = meta.query_advice(rd, Rotation::cur());
            let rs1_e = meta.query_advice(rs1, Rotation::cur());
            let rs2_e = meta.query_advice(rs2, Rotation::cur());
            let imm_e = meta.query_advice(imm, Rotation::cur());

            let rom_pc_e = meta.query_advice(rom_pc, Rotation::cur());
            let rom_op_e = meta.query_advice(rom_op, Rotation::cur());
            let rom_rd_e = meta.query_advice(rom_rd, Rotation::cur());
            let rom_rs1_e = meta.query_advice(rom_rs1, Rotation::cur());
            let rom_rs2_e = meta.query_advice(rom_rs2, Rotation::cur());
            let rom_imm_e = meta.query_advice(rom_imm, Rotation::cur());

            vec![
                (q_exec_e.clone(), q_rom_e.clone()),
                (q_exec_e.clone() * pc_e,  q_rom_e.clone() * rom_pc_e),
                (q_exec_e.clone() * op_e,  q_rom_e.clone() * rom_op_e),
                (q_exec_e.clone() * rd_e,  q_rom_e.clone() * rom_rd_e),
                (q_exec_e.clone() * rs1_e, q_rom_e.clone() * rom_rs1_e),
                (q_exec_e.clone() * rs2_e, q_rom_e.clone() * rom_rs2_e),
                (q_exec_e * imm_e,         q_rom_e * rom_imm_e),
            ]
        });

        // --- CONSCIOUS HOLE: hash of the ROM ↔ public instance (deferred). ---

        let alu = AluConfig::configure(meta, q_exec, a, b, c, imm, hi, flags);
        let control = ControlConfig::configure(
            meta, q_step, q_first, q_last, clk, pc, flags, a, a_inv, imm,
        );
        let regfile = RegFileConfig::configure(meta, q_exec, q_step, regs, rd, rs1, rs2, a, b, c, flags);
        let range = RangeConfig::configure(meta, q_exec, c, c_limbs, hi, hi_limbs, byte_table, flags);
        let xor = XorConfig::configure(meta, q_exec, a, b, a_limbs, b_limbs, c_limbs, xor_table, flags);
        let memory = MemoryConfig::configure(
            meta, q_exec, q_step, q_first, q_last, clk,
            a, b, c,
            mem_addr, mem_value, mem_type, mem_active,
            s_active, s_addr, s_value, s_clk, s_type,
            d_inv, addr_delta_limbs, clk_delta_limbs, z,
            byte_table, flags, beta, gamma,
        );

        VmConfig {
            clk, pc, regs, flags, op, rd, rs1, rs2, imm, a, b, c, a_inv,
            hi, c_limbs, hi_limbs, a_limbs, b_limbs,
            mem_addr, mem_value, mem_type, mem_active,
            s_active, s_addr, s_value, s_clk, s_type,
            d_inv, addr_delta_limbs, clk_delta_limbs, z,
            rom_pc, rom_op, rom_rd, rom_rs1, rom_rs2, rom_imm, q_rom,
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
        layouter.assign_table(
            || "byte table (0..255)",
            |mut table| {
                for value in 0..256u64 {
                    table.assign_cell(|| "byte", cfg.byte_table, value as usize, || Value::known(Fr::from(value)))?;
                }
                Ok(())
            },
        )?;

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

        // --- program ROM: ROM_CAP rows (fixed), pc = row index. Entries beyond
        // the program are padded with HALT. q_rom = 1 on ALL ROM_CAP rows, the
        // same in keygen and prove (the loop bound is a constant, not
        // program.len()), so the Fixed column matches across both. Padding HALTs
        // are never fetched: the pc freezes at the program's own HALT. ---
        layouter.assign_region(
            || "program rom",
            |mut region| {
                for i in 0..ROM_CAP  {
                    let instr = self.program.get(i).copied().unwrap_or_else(Instr::halt);
                    region.assign_fixed(|| "q_rom", cfg.q_rom, i, || Value::known(Fr::one()))?;
                    region.assign_advice(|| "rom_pc", cfg.rom_pc, i, || Value::known(Fr::from(i as u64)))?;
                    region.assign_advice(|| "rom_op", cfg.rom_op, i, || Value::known(Fr::from(instr.op as u64)))?;
                    region.assign_advice(|| "rom_rd", cfg.rom_rd, i, || Value::known(Fr::from(instr.rd)))?;
                    region.assign_advice(|| "rom_rs1", cfg.rom_rs1, i, || Value::known(Fr::from(instr.rs1)))?;
                    region.assign_advice(|| "rom_rs2", cfg.rom_rs2, i, || Value::known(Fr::from(instr.rs2)))?;
                    region.assign_advice(|| "rom_imm", cfg.rom_imm, i, || Value::known(Fr::from(instr.imm)))?;
                }
                Ok(())
            },
        )?;

        let beta = layouter.get_challenge(cfg.memory.beta);
        let gamma = layouter.get_challenge(cfg.memory.gamma);
        let trace_ref: &[TraceRow] = &self.trace;
        let z_vals: Value<Vec<Fr>> =
            beta.zip(gamma).map(|(beta, gamma)| compute_z(trace_ref, beta, gamma));

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

                    region.assign_advice(|| "op", cfg.op, i, || adv(row.op as u64))?;
                    region.assign_advice(|| "rd", cfg.rd, i, || adv(row.rd))?;
                    region.assign_advice(|| "rs1", cfg.rs1, i, || adv(row.rs1))?;
                    region.assign_advice(|| "rs2", cfg.rs2, i, || adv(row.rs2))?;
                    region.assign_advice(|| "imm", cfg.imm, i, || adv(row.imm))?;

                    region.assign_advice(|| "a", cfg.a, i, || adv(row.a))?;
                    region.assign_advice(|| "b", cfg.b, i, || adv(row.b))?;
                    region.assign_advice(|| "c", cfg.c, i, || adv(row.c))?;
                    region.assign_advice(|| "a_inv", cfg.a_inv, i, || Value::known(row.a_inv))?;

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

                    region.assign_advice(|| "mem_addr", cfg.mem_addr, i, || adv(row.mem_addr))?;
                    region.assign_advice(|| "mem_value", cfg.mem_value, i, || adv(row.mem_value))?;
                    region.assign_advice(|| "mem_type", cfg.mem_type, i, || adv(row.mem_type))?;
                    region.assign_advice(|| "mem_active", cfg.mem_active, i, || adv(row.mem_active))?;

                    region.assign_advice(|| "s_active", cfg.s_active, i, || adv(row.s_active))?;
                    region.assign_advice(|| "s_addr", cfg.s_addr, i, || adv(row.s_addr))?;
                    region.assign_advice(|| "s_value", cfg.s_value, i, || adv(row.s_value))?;
                    region.assign_advice(|| "s_clk", cfg.s_clk, i, || adv(row.s_clk))?;
                    region.assign_advice(|| "s_type", cfg.s_type, i, || adv(row.s_type))?;
                    region.assign_advice(|| "d_inv", cfg.d_inv, i, || Value::known(row.d_inv))?;
                    for (limb, col) in row.addr_delta_limbs.iter().zip(cfg.addr_delta_limbs.iter()) {
                        region.assign_advice(|| "addr_delta_limb", *col, i, || adv(*limb))?;
                    }
                    for (limb, col) in row.clk_delta_limbs.iter().zip(cfg.clk_delta_limbs.iter()) {
                        region.assign_advice(|| "clk_delta_limb", *col, i, || adv(*limb))?;
                    }

                    let z_i = z_vals.as_ref().map(|v| v[i]);
                    region.assign_advice(|| "z", cfg.z, i, || z_i)?;

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

    fn example() -> (Vec<Instr>, Vec<TraceRow>) {
        let program = vec![
            Instr::imm(0, 3),
            Instr::imm(1, 4),
            Instr::add(2, 0, 1),
            Instr::mul(3, 2, 2),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        (program, trace)
    }

    fn mem_big_example() -> (Vec<Instr>, Vec<TraceRow>) {
        let program = vec![
            Instr::imm(0, 9),
            Instr::imm(1, 2),
            Instr::imm(2, 100),
            Instr::imm(3, 200),
            Instr::store(0, 2),
            Instr::store(1, 3),
            Instr::load(2, 1),
            Instr::store(1, 2),
            Instr::load(3, 0),
            Instr::load(0, 3),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        (program, trace)
    }

    #[test]
    fn valid_trace_passes() {
        let (program, trace) = example();
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn mem_big_trace_passes() {
        let (program, trace) = mem_big_example();
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn add_wrong_result_fails() {
        let (program, mut trace) = example();
        trace[2].c = 999;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn mul_wrong_result_fails() {
        let (program, mut trace) = example();
        trace[3].c = 50;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn alu_ok_but_broken_one_hot_fails() {
        let (program, mut trace) = example();
        trace[2].flags = [0, 1, 1, 0, 0, 0, 0, 0];
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn clock_skip_fails() {
        let (program, mut trace) = example();
        trace[2].clk = 99;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn clock_not_starting_at_zero_fails() {
        let (program, mut trace) = example();
        trace[0].clk = 5;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn pc_skip_fails() {
        let (program, mut trace) = example();
        trace[2].pc = 7;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn pc_not_starting_at_zero_fails() {
        let (program, mut trace) = example();
        trace[0].pc = 3;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn pc_advances_on_halt_fails() {
        let (program, mut trace) = example();
        let hlt = trace.iter().position(|r| r.flags[3] == 1).unwrap();
        trace[hlt + 1].pc += 1;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn instruction_after_halt_fails() {
        let (program, mut trace) = example();
        let hlt = trace.iter().position(|r| r.flags[3] == 1).unwrap();
        trace[hlt + 1].flags = [1, 0, 0, 0, 0, 0, 0, 0];
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn trace_not_halted_at_end_fails() {
        let (program, mut trace) = example();
        let last = trace.len() - 1;
        trace[last].flags = [1, 0, 0, 0, 0, 0, 0, 0];
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn read_a_phantom_fails() {
        let (program, mut trace) = example();
        trace[2].a = 99;
        trace[2].c = 99 + trace[2].b;
        trace[3].regs[2] = trace[2].c;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn read_b_phantom_fails() {
        let (program, mut trace) = example();
        trace[2].b = 88;
        trace[2].c = trace[2].a + 88;
        trace[3].regs[2] = trace[2].c;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn write_lost_fails() {
        let (program, mut trace) = example();
        trace[3].regs[2] = 0;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn write_to_wrong_register_fails() {
        let (program, mut trace) = example();
        trace[3].regs[1] = trace[2].c;
        trace[3].regs[2] = trace[2].regs[2];
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn unrelated_register_changed_fails() {
        let (program, mut trace) = example();
        trace[3].regs[0] = 123;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn imm_writes_immediate() {
        let (program, mut trace) = example();
        trace[1].regs[0] = 999;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn range_c_recomposition_catches_tampered_limb() {
        let (program, mut trace) = example();
        trace[0].c_limbs[0] = 5;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn range_c_lookup_catches_non_byte() {
        let program = vec![Instr::imm(0, 256), Instr::halt()];
        let mut trace = run_program(&program);
        trace[0].c_limbs = [256, 0, 0, 0];
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
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
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
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
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
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
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        prover.assert_satisfied();
    }

    fn xor_example() -> (Vec<Instr>, Vec<TraceRow>) {
        let program = vec![
            Instr::imm(0, 0xF0F0_AAAA),
            Instr::imm(1, 0x0FF0_5555),
            Instr::xor(2, 0, 1),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        (program, trace)
    }

    #[test]
    fn xor_valid_trace_passes() {
        let (program, trace) = xor_example();
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn xor_wrong_result_fails() {
        let (program, mut trace) = xor_example();
        trace[2].c = 0xFF00_FF00;
        trace[2].c_limbs = [0x00, 0xFF, 0x00, 0xFF];
        trace[3].regs[2] = trace[2].c;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn xor_a_recomposition_catches_tampered_limb() {
        let (program, mut trace) = xor_example();
        let bl0 = trace[2].b_limbs[0];
        trace[2].a_limbs[0] = 0x11;
        trace[2].c_limbs[0] = 0x11 ^ bl0;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn xor_b_recomposition_catches_tampered_limb() {
        let (program, mut trace) = xor_example();
        let al0 = trace[2].a_limbs[0];
        trace[2].b_limbs[0] = 0x22;
        trace[2].c_limbs[0] = al0 ^ 0x22;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn xor_read_a_phantom_fails() {
        use crate::vm_trace::limbs32;
        let (program, mut trace) = xor_example();
        let x = trace[2].a;
        let lie = x ^ 0x0000_00FF;
        trace[2].a = lie;
        trace[2].a_limbs = limbs32(lie);
        let newc = lie ^ trace[2].b;
        trace[2].c = newc;
        trace[2].c_limbs = limbs32(newc);
        trace[3].regs[2] = newc;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn xor_c_detached_from_limbs_fails() {
        let (program, mut trace) = xor_example();
        trace[2].c = 0xDEAD_BEEF;
        trace[3].regs[2] = 0xDEAD_BEEF;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
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
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        prover.assert_satisfied();
    }

    fn mem_example() -> (Vec<Instr>, Vec<TraceRow>) {
        let program = vec![
            Instr::imm(0, 42),
            Instr::imm(1, 3),
            Instr::store(1, 0),
            Instr::load(2, 1),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        (program, trace)
    }

    #[test]
    fn mem_valid_trace_passes() {
        let (program, trace) = mem_example();
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn store_does_not_write_register_fails_if_tampered() {
        let (program, mut trace) = mem_example();
        trace[3].regs[0] = 999;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn load_writes_destination_fails_if_lost() {
        let (program, mut trace) = mem_example();
        trace[4].regs[2] = 0;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    fn mem_two_addr_example() -> (Vec<Instr>, Vec<TraceRow>) {
        let program = vec![
            Instr::imm(0, 3),
            Instr::imm(1, 5),
            Instr::imm(2, 100),
            Instr::store(0, 2),
            Instr::store(1, 2),
            Instr::halt(),
        ];
        let trace = run_program(&program);
        (program, trace)
    }

    #[test]
    fn mem_load_wrong_c_fails() {
        let (program, mut trace) = mem_example();
        trace[3].c = 99;
        trace[3].c_limbs = crate::vm_trace::limbs32(99);
        trace[4].regs[2] = 99;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn mem_load_wrong_value_consistency_fails() {
        let (program, mut trace) = mem_example();
        trace[3].c = 99;
        trace[3].c_limbs = crate::vm_trace::limbs32(99);
        trace[3].mem_value = 99;
        trace[4].regs[2] = 99;
        crate::emulator::rebuild_memory_witness(&mut trace);
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn mem_forged_sorted_value_fails() {
        let (program, mut trace) = mem_example();
        trace[0].s_value = 99;
        trace[1].s_value = 99;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn mem_addr_ordering_recompose_fails() {
        let (program, mut trace) = mem_two_addr_example();
        trace[0].addr_delta_limbs[0] = 7;
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn mem_is_zero_gadget_fails() {
        let (program, mut trace) = mem_two_addr_example();
        trace[0].d_inv = Fr::zero();
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn mem_row0_read_must_be_zero() {
        let program = vec![
            Instr::imm(0, 0),
            Instr::load(1, 0),
            Instr::halt(),
        ];
        let mut trace = run_program(&program);
        trace[1].c = 99;
        trace[1].c_limbs = crate::vm_trace::limbs32(99);
        trace[1].mem_value = 99;
        trace[2].regs[1] = 99;
        crate::emulator::rebuild_memory_witness(&mut trace);
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn fetch_decode_not_in_rom_fails() {
        let (program, mut trace) = example();
        trace[2].op = Op::Mul;
        trace[2].flags = TraceRow::flags_for(Op::Mul);
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    // ----- JUMPI: conditional jump / loops -----

    fn loop_example() -> (Vec<Instr>, Vec<TraceRow>) {
        let neg1 = (1u64 << 32) - 1;
        let program = vec![
            Instr::imm(0, 3),
            Instr::imm(1, neg1),
            Instr::add(0, 0, 1), // pc2: loop body (r0 -= 1)
            Instr::jumpi(2, 0),  // pc3: if r0 != 0 goto pc2
            Instr::halt(),
        ];
        let trace = run_program(&program);
        (program, trace)
    }

    #[test]
    fn jumpi_loop_passes() {
        let (program, trace) = loop_example();
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        prover.assert_satisfied();
    }

    /// is-nonzero honesty, ISOLATED: on a row with a != 0, forge a_inv = 0. The
    /// gate a·(1 − a·a_inv) = 0 becomes a·1 = a != 0 and fires. example row 2
    /// (ADD) has a = regs[0] = 3.
    #[test]
    fn jumpi_a_inv_dishonest_fails() {
        let (program, mut trace) = example();
        assert!(trace[2].a != 0);
        trace[2].a_inv = Fr::zero();
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    /// A taken JUMPI that lies about its target: force fall-through where the
    /// jump should be taken. The pc-step JUMPI term fires.
    #[test]
    fn jumpi_taken_wrong_target_fails() {
        let (program, mut trace) = loop_example();
        let j = trace
            .iter()
            .position(|r| r.op == Op::Jumpi && r.a != 0)
            .expect("a taken jumpi");
        trace[j + 1].pc = trace[j].pc + 1; // honest is 2 (loop target)
        let prover = MockProver::run(K, &VmCircuit { program, trace }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn jumpi_a_not_register_fails() {
        // The first JUMPI of the loop is honestly taken (regs[rs1] = 2).
        // Forge a = 0 on that row, so the jump is not taken and the program
        // halts early with r0 = 2. Only "regfile: read a" (which must include
        // f_jumpi) ties a to regs[rs1] and rejects it.
        let (program, honest) = loop_example();
        let j = honest.iter().position(|r| r.op == Op::Jumpi).unwrap();
        let halt_template = *honest.last().unwrap();
        let mut forged: Vec<TraceRow> = honest[..=j].to_vec();
        forged[j].a = 0;
        forged[j].a_inv = Fr::zero();
        while forged.len() < honest.len() {
            let mut r = halt_template;
            r.clk = forged.len() as u64;
            r.regs = forged[j].regs;
            forged.push(r);
        }
        let prover = MockProver::run(K, &VmCircuit { program, trace: forged }, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }
}
