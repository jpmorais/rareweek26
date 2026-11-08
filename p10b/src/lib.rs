// Goal: prove knowledge of five rows of private 8-bit values where c = a XOR b in every row.
// The table holds all the 2^16 combinations (a, b, a XOR b), and the lookup requires
// the tuple (a, b, c) of each row to match a single row of the table.

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    pasta::Fp,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector, TableColumn},
    poly::Rotation,
};

/// Number of witness rows (a, b, c).
const N_ROWS: usize = 5;

/// Checks, row by row, that c = a XOR b with a, b, c ∈ [0, 256).
struct XorCircuit {
    rows: [[Value<Fp>; 3]; N_ROWS],
}

#[derive(Clone, Debug)]
struct XorConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    q: Selector,
    t_a: TableColumn,
    t_b: TableColumn,
    // TODO: declare the field `t_c`, the third lookup table column
}

impl Circuit<Fp> for XorCircuit {
    type Config = XorConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            rows: [[Value::unknown(); 3]; N_ROWS],
        }
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let q = meta.complex_selector();

        let t_a = meta.lookup_table_column();
        // TODO: create the lookup table column for `b` and bind it to `t_b`
        // TODO: create the lookup table column for `c` and bind it to `t_c`

        // The whole tuple (a, b, c) must match a single row of the table.
        // When q = 0 the input becomes (0, 0, 0), which is in the table (0 XOR 0 = 0).
        meta.lookup(|meta| {
            let q = meta.query_selector(q);
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());

            return vec![
                (q.clone() * a, t_a),
                // TODO: pair `b`, multiplied by the selector, with the column `t_b`
                // TODO: pair `c`, multiplied by the selector, with the column `t_c`
            ]
        });

        XorConfig { a, b, c, q, t_a, t_b, t_c }
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<Fp>) -> Result<(), Error> {
        layouter.assign_region(
            || "witness",
            |mut region| {
                for (i, [a, b, c]) in self.rows.iter().enumerate() {
                    config.q.enable(&mut region, i)?;
                    region.assign_advice(|| "a", config.a, i, || *a)?;
                    region.assign_advice(|| "b", config.b, i, || *b)?;
                    region.assign_advice(|| "c", config.c, i, || *c)?;
                }
                Ok(())
            },
        )?;

        // Table with all 2^16 combinations (a, b, a XOR b).
        layouter.assign_table(
            || "8-bit xor table",
            |mut table| {
                let mut offset = 0;
                for a in 0..256u64 {
                    for b in 0..256u64 {
                        let c = a ^ b;
                        table.assign_cell(|| "t_a", config.t_a, offset, || Value::known(Fp::from(a)))?;
                        table.assign_cell(|| "t_b", config.t_b, offset, || Value::known(Fp::from(b)))?;
                        table.assign_cell(|| "t_c", config.t_c, offset, || Value::known(Fp::from(c)))?;
                        offset += 1;
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
    use halo2_proofs::dev::MockProver;

    // 2^16 table rows + blinding rows => k = 17.
    const K: u32 = 17;

    fn circuit(rows: [(u64, u64, u64); N_ROWS]) -> XorCircuit {
        XorCircuit {
            rows: rows.map(|(a, b, c)| [a, b, c].map(|v| Value::known(Fp::from(v)))),
        }
    }

    #[test]
    fn it_works() {
        let c = circuit([
            (1, 2, 3),
            (100, 50, 86),
            (200, 100, 172),
            (255, 1, 254),
            (0, 0, 0),
        ]);
        let prover = MockProver::run(K, &c, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn it_fails() {
        let c = circuit([
            (1, 2, 3),
            (100, 50, 86),
            (200, 100, 44), // this is the sum mod 256, not the XOR (172)
            (255, 1, 254),
            (0, 0, 0),
        ]);
        let prover = MockProver::run(K, &c, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn it_fails_input_out_of_range() {
        let c = circuit([
            (1, 2, 3),
            (256, 0, 256), // a and c do not fit in 8 bits
            (200, 100, 172),
            (255, 1, 254),
            (0, 0, 0),
        ]);
        let prover = MockProver::run(K, &c, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }
}