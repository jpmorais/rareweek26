use halo2_proofs::{circuit::{SimpleFloorPlanner, Value}, plonk::{Advice, Circuit, Column, Instance, Selector}};
use halo2_proofs::pasta::Fp;
use halo2_proofs::poly::Rotation;


struct MyCircuit<Fp> {
    x: Value<Fp>,
    y: Value<Fp>
}

#[derive(Clone)]
struct CircuitConfig {
    a: Column<Advice>,
    instance: Column<Instance>,
    q: Selector
}

impl Circuit<Fp> for MyCircuit<Fp> {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { x: Value::unknown(), y: Value::unknown() }
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fp>) -> Self::Config {

        let a = meta.advice_column();
        let instance = meta.instance_column();
        let q = meta.complex_selector();

        meta.create_gate("add gate", |meta| {

            let a0 = meta.query_advice(a, Rotation::cur());
            let a1 = meta.query_advice(a, Rotation::next());
            let a2 = meta.query_instance(instance, Rotation::cur());

            let q = meta.query_selector(q);

            vec![q*(a0 + a1 - a2)]

        });

        CircuitConfig {
            a, instance, q
        }

    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<Fp>) -> Result<(), halo2_proofs::plonk::Error> {

        layouter.assign_region(|| "region", |mut region| {

            region.assign_advice(|| "a0", config.a, 0, || self.x)?;
            region.assign_advice(|| "a1", config.a, 1, || self.y)?;

            config.q.enable(&mut region, 0)?;

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
            x: Value::known(Fp::from(1)),
            y: Value::known(Fp::from(2))
        };

        let instance = vec![Fp::from(3)];
        let prover = MockProver::run(4, &circuit, vec![instance]).unwrap();
        prover.assert_satisfied();

    }

        #[test]
    fn it_fails() {

        let circuit = MyCircuit {
            x: Value::known(Fp::from(2)),
            y: Value::known(Fp::from(2))
        };

        let instance = vec![Fp::from(3)];
        let prover = MockProver::run(4, &circuit, vec![instance]).unwrap();
        assert!(prover.verify().is_err());

    }

}
