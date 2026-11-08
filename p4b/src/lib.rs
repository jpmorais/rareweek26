// Goal: prove knowledge of two private values x and y whose product is a public value.
// x and y go in rows 0 and 1 of the advice column a. The public value is in row 0 of
// the instance column, and the gate enabled at row 0 reads it directly.

use halo2_proofs::{circuit::{SimpleFloorPlanner, Value}, plonk::{Advice, Circuit, Column, Instance, Selector}};
use halo2_proofs::pasta::Fp;
use halo2_proofs::poly::Rotation;


pub struct MyCircuit {
    x: Value<Fp>,
    y: Value<Fp>
}

#[derive(Clone)]
pub struct CircuitConfig {
    a: Column<Advice>,
    instance: Column<Instance>,
    q: Selector
}

impl Circuit<Fp> for MyCircuit {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { x: Value::unknown(), y: Value::unknown() }
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fp>) -> Self::Config {

        let a = meta.advice_column();
        // TODO: create the instance column and bind it to `instance`
        let q = meta.complex_selector();

        meta.create_gate("mul gate", |meta| {

            let a0 = meta.query_advice(a, Rotation::cur());
            let a1 = meta.query_advice(a, Rotation::next());
            // TODO: query the instance column at the current row and bind it to `a2`

            let q = meta.query_selector(q);

            vec![q*(a0 * a1 - a2)]

        });

        CircuitConfig {
            a, instance, q
        }

    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<Fp>) -> Result<(), halo2_proofs::plonk::Error> {

        layouter.assign_region(|| "region", |mut region| {

            region.assign_advice(|| "a0", config.a, 0, || self.x)?;
            // TODO: assign `self.y` to column `a` at offset 1

            // TODO: enable the selector at the row that lets the gate read the instance value

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
            x: Value::known(Fp::from(3)),
            y: Value::known(Fp::from(4))
        };

        let instance = vec![Fp::from(12)];
        let prover = MockProver::run(4, &circuit, vec![instance]).unwrap();
        prover.assert_satisfied();

    }

    #[test]
    fn it_fails() {

        let circuit = MyCircuit {
            x: Value::known(Fp::from(3)),
            y: Value::known(Fp::from(4))
        };

        let instance = vec![Fp::from(13)];
        let prover = MockProver::run(4, &circuit, vec![instance]).unwrap();
        assert!(prover.verify().is_err());

    }

}
