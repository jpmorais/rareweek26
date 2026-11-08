// Goal: chain three chips that share the same columns and link their cells with copy constraints.
// x + y = z    (AddChip)
// z * p = q    (MulChip)
// q - r = s    (SubChip)


use std::marker::PhantomData;

use ff::PrimeField;

use halo2_proofs::circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{Advice, Circuit, Column, ConstraintSystem, ErrorFront, Selector};
use halo2_proofs::poly::Rotation;

pub struct MyCircuit<F: PrimeField> {
    x: Value<F>,
    y: Value<F>,
    p: Value<F>,
    r: Value<F>,
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

            let new_a = region.assign_advice(|| "a", config.a, 0, || a_val)?;
            let new_b = region.assign_advice(|| "b", config.b, 0, || b_val)?;
            
            region.constrain_equal(new_a.cell(), a.cell())?;
            region.constrain_equal(new_b.cell(), b.cell())?;
            
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

        layouter.assign_region(|| "mul region", |mut region| {
            config.q_mul.enable(&mut region, 0)?;

            // let a_val = a.value().copied();
            // let b_val = b.value().copied();

            //region.assign_advice(|| "a", config.a, 0, || a_val)?;
            //region.assign_advice(|| "b", config.b, 0, || b_val)?;

            // region.constrain_equal(new_a.cell(), a.cell())?;
            // region.constrain_equal(new_b.cell(), b.cell())?;
            
            let a = a.copy_advice(|| "a copied", &mut region, config.a, 0)?;
            let b = b.copy_advice(|| "b copied", &mut region, config.b, 0)?;            
            
            let out_val = a.value().copied() * b.value().copied();

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


///////////////////////////////
// SUB CHIP
///////////////////////////////
#[derive(Clone)]
pub struct SubConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    q_sub: Selector
}

pub struct SubChip<F> {
    config: SubConfig,
    _ph: PhantomData<F>
}


impl<F: PrimeField> SubChip<F> {

    pub fn construct(config: SubConfig) -> Self {
        SubChip { config, _ph: PhantomData }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>, a: Column<Advice>, b: Column<Advice>, c: Column<Advice>) -> SubConfig {
        let q_sub = meta.complex_selector();

        meta.create_gate("sub gate", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());

            let q_sub = meta.query_selector(q_sub);

            // TODO: return the constraint that enforces c = a - b when q_sub is on

        });

        SubConfig { a, b, c, q_sub }
    }

    pub fn assign(&self, layouter: &mut impl Layouter<F>, a: AssignedCell<F,F>, b: AssignedCell<F,F>) -> Result<AssignedCell<F,F>, ErrorFront> {
        let config = &self.config;

        layouter.assign_region(|| "sub region", |mut region| {
            config.q_sub.enable(&mut region, 0)?;

            // TODO: copy the cell `a` into column `a` at offset 0, keeping the copy constraint, and bind it to `a`
            // TODO: copy the cell `b` into column `b` at offset 0, keeping the copy constraint, and bind it to `b`

            // TODO: compute the value a - b and bind it to `out_val`

            let out = region.assign_advice(|| "c", config.c, 0, || out_val)?;

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
    mul_config: MulConfig,
    sub_config: SubConfig
}

impl<F: PrimeField> Circuit<F> for MyCircuit<F> {

    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        MyCircuit { x: Value::unknown(), y: Value::unknown(), p: Value::unknown(), r: Value::unknown()}
    }
    
    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {

        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);

        let add_config = AddChip::configure(meta, a, b, c);
        let mul_config = MulChip::configure(meta, a, b, c);
        let sub_config = SubChip::configure(meta, a, b, c);
        CircuitConfig { a, b, c, add_config, mul_config, sub_config }
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<F>) -> Result<(), halo2_proofs::plonk::ErrorFront> {
        let add_chip: AddChip<F> = AddChip::construct(config.add_config);
        let mul_chip: MulChip<F> = MulChip::construct(config.mul_config);
        let sub_chip: SubChip<F> = SubChip::construct(config.sub_config);

        let x_cell = add_chip.unconstrained(&mut layouter, self.x)?;
        let y_cell = add_chip.unconstrained(&mut layouter, self.y)?;

        let z_cell = add_chip.assign(&mut layouter, x_cell, y_cell)?;

        let p_cell = mul_chip.unconstrained(&mut layouter, self.p)?;
        
        let q_cell = mul_chip.assign(&mut layouter, z_cell, p_cell)?;

        let r_cell = mul_chip.unconstrained(&mut layouter, self.r)?;

        let _s_cell = sub_chip.assign(&mut layouter, q_cell, r_cell)?;

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
            x: Value::known(Fr::from(1)),
            y: Value::known(Fr::from(2)),
            p: Value::known(Fr::from(4)),
            r: Value::known(Fr::from(5)),
        };

        // (1 + 2) * 4 - 5 = 7
        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

        let advices = prover.advice();
        let selectors = prover.selectors();

        for i in 0..advices[0].len() {
            println!("a[{i}]={:?}, b[{i}]={:?}, c[{i}]={:?}", advices[0][i], advices[1][i], advices[2][i]);
        }

        for i in 0..selectors[0].len() {
            println!("q_add[{i}]={:?}, q_mul[{i}]={:?}, q_sub[{i}]={:?}", selectors[0][i], selectors[1][i], selectors[2][i]);
        }


    }

}
