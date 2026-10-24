use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    pasta::Fp,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector, TableColumn},
    poly::Rotation,
};

/// Number of witness rows (a, b, c).
const N_ROWS: usize = 5;

/// Checks, row by row, that c = (a + b) mod 256 with a, b, c ∈ [0, 256).
struct AddCircuit {
    rows: [[Value<Fp>; 3]; N_ROWS],
}

#[derive(Clone, Debug)]
struct AddConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    q: Selector,
    t_a: TableColumn,
    t_b: TableColumn,
    t_c: TableColumn,
}

impl Circuit<Fp> for AddCircuit {
    type Config = AddConfig;
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
        let t_b = meta.lookup_table_column();
        let t_c = meta.lookup_table_column();

        // The whole tuple (a, b, c) must match a single row of the table.
        // When q = 0 the input becomes (0, 0, 0), which is in the table (0 + 0 = 0).
        meta.lookup(|meta| {
            let q = meta.query_selector(q);
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());

            return vec![
                (q.clone() * a, t_a),
                (q.clone() * b, t_b),
                (q * c, t_c),
            ]
        });

        AddConfig { a, b, c, q, t_a, t_b, t_c }
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

        // Table with all 2^16 combinations (a, b, (a + b) mod 256).
        layouter.assign_table(
            || "8-bit add table",
            |mut table| {
                let mut offset = 0;
                for a in 0..256u64 {
                    for b in 0..256u64 {
                        let c = (a + b) % 256;
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

    fn circuit(rows: [(u64, u64, u64); N_ROWS]) -> AddCircuit {
        AddCircuit {
            rows: rows.map(|(a, b, c)| [a, b, c].map(|v| Value::known(Fp::from(v)))),
        }
    }

    #[test]
    fn it_works() {
        let c = circuit([
            (1, 2, 3),
            (100, 50, 150),
            (200, 100, 44), // overflow: 300 mod 256 = 44
            (255, 1, 0),    // overflow: 256 mod 256 = 0
            (0, 0, 0),
        ]);
        let prover = MockProver::run(K, &c, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn fails_wrong_sum() {
        let c = circuit([
            (1, 2, 3),
            (100, 50, 150),
            (200, 100, 300), // not reduced mod 256
            (255, 1, 0),
            (0, 0, 0),
        ]);
        let prover = MockProver::run(K, &c, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn fails_input_out_of_range() {
        let c = circuit([
            (1, 2, 3),
            (256, 0, 0), // a does not fit in 8 bits
            (200, 100, 44),
            (255, 1, 0),
            (0, 0, 0),
        ]);
        let prover = MockProver::run(K, &c, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }
}