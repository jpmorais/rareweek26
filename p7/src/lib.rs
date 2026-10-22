use halo2_proofs::{circuit::{AssignedCell, SimpleFloorPlanner, Value}, plonk::{Advice, Circuit, Column, Instance, Selector, Fixed}};
use halo2_proofs::pasta::Fp;
use halo2_proofs::poly::Rotation;


struct MyCircuit<Fp> {
    x: [Value<Fp>;4],
    y: [Value<Fp>;4],
}

#[derive(Clone)]
struct CircuitConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Fixed>,
    q: Selector
}

impl Circuit<Fp> for MyCircuit<Fp> {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { x: [Value::unknown();4], y: [Value::unknown();4] }
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fp>) -> Self::Config {

        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.fixed_column();
        let q = meta.complex_selector();

        meta.create_gate("add gate", |meta| {

            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());

            let c = meta.query_fixed(c);
            // let c = meta.query_any(c, Rotation::cur());

            let q = meta.query_selector(q);

            vec![q*(a*b - c)]

        });

        CircuitConfig {
            a, b, c, q
        }

    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<Fp>) -> Result<(), halo2_proofs::plonk::Error> {

        layouter.assign_region(|| "region", |mut region| {
            
            // advices
            for i in 0..4 {

                region.assign_advice(|| "a", config.a, i, || self.x[i])?;
                region.assign_advice(|| "b", config.b, i, || self.y[i])?;

            }


            // fixed
            for i in 0..4 {

                region.assign_fixed(|| "fixed", config.c, i, || Value::known(Fp::from((i+2) as u64)))?;
                config.q.enable(&mut region, i)?;
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
            y: [
            Value::known(Fp::from(2)),
            Value::known(Fp::from(1)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(1))],
        };

        let instance = vec![];
        let prover = MockProver::run(4, &circuit, instance).unwrap();
        prover.assert_satisfied();

    }

    #[test]
    fn should_fail() {

        let circuit = MyCircuit {
            x: [
            Value::known(Fp::from(1)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(2)),
            Value::known(Fp::from(5))],
            y: [
            Value::known(Fp::from(2)),
            Value::known(Fp::from(1)),
            Value::known(Fp::from(3)),
            Value::known(Fp::from(1))],
        };

        let instance = vec![];
        let prover = MockProver::run(4, &circuit, instance).unwrap();
        assert!(prover.verify().is_err());

    }


}
