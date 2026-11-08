use halo2_proofs::{circuit::{SimpleFloorPlanner, Value}, plonk::{Advice, Circuit, Column, Selector, TableColumn}};
use halo2_proofs::pasta::Fp;
use halo2_proofs::poly::Rotation;


struct MyCircuit<Fp> {
    x: [Value<Fp>;4],
}

#[derive(Clone)]
struct CircuitConfig {
    a: Column<Advice>,
    table: TableColumn,
    q: Selector
}

impl Circuit<Fp> for MyCircuit<Fp> {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { x: [Value::unknown();4]}
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fp>) -> Self::Config {

        let a = meta.advice_column();
        let table = meta.lookup_table_column();
        let q = meta.complex_selector();

        meta.lookup(|meta | {

            let a = meta.query_advice(a, Rotation::cur());
            let q = meta.query_selector(q);

            return vec![(q*a, table)]

        });

        CircuitConfig {
            a, table, q
        }

    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<Fp>) -> Result<(), halo2_proofs::plonk::Error> {

        layouter.assign_region(|| "region", |mut region| {
            
            // advice at proof time
            for i in 0..4 {

                region.assign_advice(|| "a", config.a, i, || self.x[i])?;

            }

            // selector at compile time
            for i in 0..4 {
                config.q.enable(&mut region, i)?;
            }

            Ok(())

        })?;

        layouter.assign_table(|| "4 bits numbers", |mut table| {

            for i in 0..16 {
                table.assign_cell(|| "table cell", config.table, i, || Value::known(Fp::from(i as u64)))?;
            }

            Ok(())

        })


    }

}



#[cfg(test)]
mod tests {
    use halo2_proofs::dev::MockProver;

use super::*;

    #[test]
    fn it_works() {

        let circuit = MyCircuit {
            x: [
            Value::known(Fp::from(1)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(5))],
        };

        let instance = vec![];
        let prover = MockProver::run(5, &circuit, instance).unwrap();
        prover.assert_satisfied();

    }

    #[test]
    fn it_fails() {

        let circuit = MyCircuit {
            x: [
            Value::known(Fp::from(1)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(17))],
        };

        let instance = vec![];
        let prover = MockProver::run(5, &circuit, instance).unwrap();
        assert!(prover.verify().is_err());

    }


}
