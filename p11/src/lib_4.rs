
// Using cells but wrong

// x + y = z
// z * p = q


use std::marker::PhantomData;

use ff::PrimeField;

use halo2_proofs::circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{Advice, Circuit, Column, ConstraintSystem, ErrorFront, Selector};
use halo2_proofs::poly::Rotation;

pub struct MyCircuit<F: PrimeField> {
    x: Value<F>,
    y: Value<F>,
    p: Value<F>,
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

    pub fn configure(meta: &mut ConstraintSystem<F>, a: Column<Advice>, b: Column<Advice>, c: Column<Advice>) -> AddConfig {
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

    pub fn unconstrained(&self, layouter: &mut impl Layouter<F>, a: Value<F>) -> Result<AssignedCell<F,F>, ErrorFront> {
        let config = &self.config;

        layouter.assign_region(|| "unconstrained", |mut region| {
            let out = region.assign_advice(|| "unconstrained", config.a, 0, || a)?;

            Ok(out)
        })

    }


    pub fn assign(&self, layouter: &mut impl Layouter<F>, a: AssignedCell<F, F>, b: AssignedCell<F,F>) -> Result<AssignedCell<F,F>, ErrorFront> {
        let config = &self.config;

        layouter.assign_region(|| "add region", |mut region| {
            config.q_add.enable(&mut region, 0)?;

            let a_val = a.value().copied();
            let b_val = b.value().copied();

            region.assign_advice(|| "a", config.a, 0, || a_val)?;
            region.assign_advice(|| "b", config.b, 0, || b_val)?;
            let out_val = a_val + b_val;

            let out = region.assign_advice(|| "c", config.c, 0, || out_val)?;

            Ok(out)

        })
    }

}
/////////////////////////
/// /////////////////////


///////////////////////////////
// MUL CHIP
///////////////////////////////
#[derive(Clone)]
pub struct MulConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    q_mul: Selector
}

pub struct MulChip<F> {
    config: MulConfig,
    _ph: PhantomData<F>
}


impl<F: PrimeField> MulChip<F> {

    pub fn construct(config: MulConfig) -> Self {
        MulChip { config, _ph: PhantomData }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>, a: Column<Advice>, b: Column<Advice>, c: Column<Advice>) -> MulConfig {
        let q_mul = meta.complex_selector();

        meta.create_gate("mul gate", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());

            let q_mul = meta.query_selector(q_mul);

            vec![q_mul*(a*b - c)]

        });

        MulConfig { a, b, c, q_mul }
    }

    pub fn assign(&self, layouter: &mut impl Layouter<F>, a: AssignedCell<F,F>, b: AssignedCell<F,F>) -> Result<AssignedCell<F,F>, ErrorFront> {
        let config = &self.config;

        layouter.assign_region(|| "add region", |mut region| {
            config.q_mul.enable(&mut region, 0)?;

            let a_val = a.value().copied();
            let b_val = b.value().copied();

            region.assign_advice(|| "a", config.a, 0, || a_val)?;
            region.assign_advice(|| "b", config.b, 0, || b_val)?;
            let out_val = a_val*b_val;

            let out = region.assign_advice(|| "c", config.c, 0, || out_val)?;

            Ok(out)

        })
    }

    pub fn unconstrained(&self, layouter: &mut impl Layouter<F>, a: Value<F>) -> Result<AssignedCell<F,F>, ErrorFront> {
        let config = &self.config;

        layouter.assign_region(|| "unconstrained", |mut region| {
            let out = region.assign_advice(|| "unconstrained", config.a, 0, || a)?;

            Ok(out)
        })
    }

}
/////////////////////////
/// /////////////////////



#[derive(Clone)]
pub struct CircuitConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    add_config: AddConfig,
    mul_config: MulConfig
}

impl<F: PrimeField> Circuit<F> for MyCircuit<F> {

    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        MyCircuit { x: Value::unknown(), y: Value::unknown(), p: Value::unknown()}
    }
    
    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {

        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();

        let add_config = AddChip::configure(meta, a, b, c);
        let mul_config = MulChip::configure(meta, a, b, c);
        CircuitConfig { a, b, c, add_config, mul_config}    
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<F>) -> Result<(), halo2_proofs::plonk::ErrorFront> {
        let add_chip: AddChip<F> = AddChip::construct(config.add_config);
        let mul_chip: MulChip<F> = MulChip::construct(config.mul_config);

        // x + y = z
        // z * p = q

        let x_cell = add_chip.unconstrained(&mut layouter, self.x)?;
        let y_cell = add_chip.unconstrained(&mut layouter, self.y)?;

        let z_cell = add_chip.assign(&mut layouter, x_cell, y_cell)?;

        let p_cell = mul_chip.unconstrained(&mut layouter, self.p)?;
        
        let q_cell = mul_chip.assign(&mut layouter, z_cell, p_cell)?;

        Ok(())
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};

    #[test]
    fn it_works_4() {

        let circuit = MyCircuit {
            x: Value::known(Fr::from(1)),
            y: Value::known(Fr::from(2)),
            p: Value::known(Fr::from(4)),
        };

        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

        let advices = prover.advice();
        let selectors = prover.selectors();

        for i in 0..advices[0].len() {
            println!("a[{i}]={:?}, b[{i}]={:?}, c[{i}]={:?}", advices[0][i], advices[1][i], advices[2][i]);
        }

        for i in 0..selectors[0].len() {
            println!("q_add[{i}]={:?}, q_mul[{i}]={:?}", selectors[0][i], selectors[1][i]);
        }


    }

    // #[test]
    // fn it_should_not_work() {

    //     let circuit = MyCircuit {
    //         x: Value::known(Fr::from(1)),
    //         y: Value::known(Fr::from(2)),
    //         p: Value::known(Fr::from(4)),
    //     };

    //     let prover = MockProver::run(4, &circuit, vec![]).unwrap();
    //     assert!(prover.verify().is_err());


    // }


}

