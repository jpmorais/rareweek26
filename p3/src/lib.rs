

use std::alloc::Layout;

use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::circuit::{SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{Advice, Circuit, Column, Selector};
use halo2_proofs::poly::Rotation;

struct MyCircuit<Fr> {
    x: Value<Fr>,
    y: Value<Fr>,
}

#[derive(Clone)]
struct CircuitConfig {
    a: Column<Advice>,
    q: Selector
}

impl Circuit<Fr> for MyCircuit<Fr> {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { x: Value::unknown(), y: Value::unknown() }
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fr>) -> Self::Config {
        
        let a = meta.advice_column();
        let q = meta.selector();

        meta.create_gate("add gate", |meta| {

            let a1 = meta.query_advice(a, Rotation::cur());
            let a2 = meta.query_advice(a, Rotation::next());
            let a3 = meta.query_advice(a, Rotation(2));

            let q = meta.query_selector(q);

            vec![q*(a1 + a2 - a3)]

        });

        CircuitConfig {
            a, q
        }

    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<Fr>) -> Result<(), halo2_proofs::plonk::ErrorFront> {
        
        layouter.assign_region(|| "region", |mut region| {

            region.assign_advice(|| "a0", config.a, 0, || self.x)?;
            region.assign_advice(|| "a1", config.a, 1, || self.y)?;
            let z = self.x + self.y;
            region.assign_advice(|| "a2", config.a, 2, || z)?;

            config.q.enable(&mut region, 0)?;

            Ok(())

        })

    }
}


#[cfg(test)]
mod tests {
    use halo2_proofs::{circuit, dev::MockProver};

use super::*;

    #[test]
    fn it_works() {

        let circuit = MyCircuit {
            x: Value::known(Fr::from(1)),
            y: Value::known(Fr::from(2)),
        };

        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }


}
