

// Only Add Chip

use std::marker::PhantomData;

use ff::PrimeField;

use halo2_proofs::circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{Advice, Circuit, Column, ConstraintSystem, ErrorFront, Selector};
use halo2_proofs::poly::Rotation;

pub struct MyCircuit<F: PrimeField> {
    a: [Value<F>;2],
    b: [Value<F>;2],
}


///////////////////////////////
// ADD CHIP
///////////////////////////////
#[derive(Clone)]
pub struct AddConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    q_add: Selector
}

pub struct AddChip<F> {
    config: AddConfig,
    _ph: PhantomData<F>
}


impl<F: PrimeField> AddChip<F> {

    pub fn construct(config: AddConfig) -> Self {
        AddChip { config, _ph: PhantomData }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> AddConfig {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let q_add = meta.complex_selector();

        meta.create_gate("add gate", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());

            let q_add = meta.query_selector(q_add);

            vec![q_add*(a + b - c)]

        });

        AddConfig { a, b, c, q_add }
    }

    pub fn assign(&self, layouter: &mut impl Layouter<F>, a: Value<F>, b: Value<F>) -> Result<AssignedCell<F,F>, ErrorFront> {
        let config = &self.config;

        layouter.assign_region(|| "add region", |mut region| {
            config.q_add.enable(&mut region, 0)?;

            region.assign_advice(|| "a", config.a, 0, || a)?;
            region.assign_advice(|| "b", config.b, 0, || b)?;
            let out_val = a + b;

            let out = region.assign_advice(|| "c", config.c, 0, || out_val)?;

            Ok(out)

        })
    }

}
/////////////////////////
/// /////////////////////


#[derive(Clone)]
pub struct CircuitConfig {
    add_config: AddConfig
}

impl<F: PrimeField> Circuit<F> for MyCircuit<F> {

    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        MyCircuit { a: [Value::unknown();2], b: [Value::unknown();2] }
    }
    
    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
        let add_config = AddChip::configure(meta);
        CircuitConfig { add_config}    
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<F>) -> Result<(), halo2_proofs::plonk::ErrorFront> {
        let add_chip = AddChip::construct(config.add_config);
        add_chip.assign(&mut layouter, self.a[0], self.b[0])?;
        add_chip.assign(&mut layouter, self.a[1], self.b[1])?;

        Ok(())
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};

    #[test]
    fn it_works() {

        let circuit = MyCircuit {
            a: [Value::known(Fr::from(1)), Value::known(Fr::from(2))],
            b: [Value::known(Fr::from(1)), Value::known(Fr::from(2))],
        };

        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

        let advices = prover.advice();

        for i in 0..advices[0].len() {
            println!("a[{i}]={:?}, b[{i}]={:?}, c[{i}]={:?}", advices[0][i], advices[1][i], advices[2][i]);
        }


    }
}
