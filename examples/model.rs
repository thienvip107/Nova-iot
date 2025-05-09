use ff::Field;
use ff::PrimeField;
use flate2::{write::ZlibEncoder, Compression};
use nova_snark::{
    frontend::{num::AllocatedNum, ConstraintSystem, SynthesisError, Assignment},
    nova::{CompressedSNARK, PublicParams, RecursiveSNARK}, // Assuming types match minroot.rs context
    provider::{Bn256EngineKZG, GrumpkinEngine},
    traits::{circuit::StepCircuit, Engine, Group, snark::RelaxedR1CSSNARKTrait}, // Removed snark::RelaxedR1CSSNARKTrait as it's used internally by S1/S2
};
use num_bigint::BigUint; // Not strictly needed for SimpleLinearModel, but from minroot
use std::marker::PhantomData; // For PhantomData in SimpleLinearModelCircuit if needed
use std::time::Instant;

// --- Type aliases based on minroot.rs ---
type E1 = Bn256EngineKZG;
type E2 = GrumpkinEngine;

// Evaluation Engines for Spartan SNARKs
type EE1 = nova_snark::provider::hyperkzg::EvaluationEngine<E1>;
type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>; // minroot uses ipa_pc for Grumpkin

// Spartan RelaxedR1CSSNARK types
type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>;
type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;

// Scalar field for the primary circuit (SimpleLinearModelCircuit)
type F1 = <E1 as Engine>::Scalar;

// --- SimpleLinearModelCircuit definition (adapted for this context) ---
#[derive(Clone, Debug)]
pub struct SimpleLinearModelCircuit<F: PrimeField> {
    // Model parameters
    pub w_soil_moisture_val: F, // Made non-Option as they are fixed for an instance
    pub w_temperature_val: F,
    pub bias_val: F,

    // Current step's sensor inputs
    pub x_soil_moisture_val: Option<F>, // Option because template might not have it
    pub x_temperature_val: Option<F>,
    _p: PhantomData<F>, // To use F if other fields were all Option or not F
}

impl<F: PrimeField> SimpleLinearModelCircuit<F> {
    pub fn new(
        w_soil: F,
        w_temp: F,
        bias: F,
        x_soil: Option<F>,
        x_temp: Option<F>,
    ) -> Self {
        Self {
            w_soil_moisture_val: w_soil,
            w_temperature_val: w_temp,
            bias_val: bias,
            x_soil_moisture_val: x_soil,
            x_temperature_val: x_temp,
            _p: PhantomData,
        }
    }
}

impl<F: PrimeField> StepCircuit<F> for SimpleLinearModelCircuit<F> {
    fn arity(&self) -> usize {
        1 // Public input/output is the previous/current model output y
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _z_in: &[AllocatedNum<F>], // y_previous, can be ignored if current step is independent
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let x_soil = AllocatedNum::alloc(cs.namespace(|| "x_soil"), || {
            self.x_soil_moisture_val
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        let x_temp = AllocatedNum::alloc(cs.namespace(|| "x_temp"), || {
            self.x_temperature_val
                .ok_or(SynthesisError::AssignmentMissing)
        })?;

        let w_soil = AllocatedNum::alloc(cs.namespace(|| "w_soil"), || Ok(self.w_soil_moisture_val))?;
        let w_temp = AllocatedNum::alloc(cs.namespace(|| "w_temp"), || Ok(self.w_temperature_val))?;
        let bias = AllocatedNum::alloc(cs.namespace(|| "bias"), || Ok(self.bias_val))?;

        let ps = AllocatedNum::alloc(cs.namespace(|| "ps"), || {
            Ok(*w_soil.get_value().get()? * x_soil.get_value().get()?)
        })?;
        cs.enforce(
            || "w_s * x_s = ps",
            |lc| lc + w_soil.get_variable(),
            |lc| lc + x_soil.get_variable(),
            |lc| lc + ps.get_variable(),
        );

        let pt = AllocatedNum::alloc(cs.namespace(|| "pt"), || {
            Ok(*w_temp.get_value().get()? * x_temp.get_value().get()?)
        })?;
        cs.enforce(
            || "w_t * x_t = pt",
            |lc| lc + w_temp.get_variable(),
            |lc| lc + x_temp.get_variable(),
            |lc| lc + pt.get_variable(),
        );

        let sum_p = AllocatedNum::alloc(cs.namespace(|| "sum_p"), || {
            Ok(*ps.get_value().get()? + pt.get_value().get()?)
        })?;
        cs.enforce(
            || "ps + pt = sum_p",
            |lc| lc + ps.get_variable() + pt.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + sum_p.get_variable(),
        );

        let y_output = AllocatedNum::alloc(cs.namespace(|| "y"), || {
            Ok(*sum_p.get_value().get()? + bias.get_value().get()?)
        })?;
        cs.enforce(
            || "sum_p + b = y",
            |lc| lc + sum_p.get_variable() + bias.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + y_output.get_variable(),
        );

        Ok(vec![y_output])
    }
}
fn main() {
    println!("Nova-based Recursive Proof for SimpleLinearModel");
    println!("=========================================================");

    // THAY ĐỔI CHÍNH: Số bước đệ quy là 1,000,000
    let num_steps = 1_000_000;
    println!(
        "WARNING: num_steps is set to {}. This will take a VERY LONG TIME and consume significant memory.",
        num_steps
    );

    // Trọng số mô hình cố định
    let w_s = F1::from(2u64);
    let w_t = F1::from(3u64);
    let b = F1::from(1u64);

    // Dữ liệu cảm biến cho mỗi bước
    // SỬA LỖI: Sử dụng biến lặp `i` để tạo dữ liệu đa dạng.
    // Ví dụ: tạo dữ liệu thay đổi một chút cho mỗi bước.
    println!("Generating {} sensor data points (this might take some RAM)...", num_steps);
    let start_data_gen = Instant::now();
    let sensor_data_per_step: Vec<(F1, F1)> = (0..num_steps)
        .map(|i| {
            // Logic tạo dữ liệu đa dạng hơn, ví dụ:
            let soil_val = 50u64 + (i as u64 % 1000); // Thay đổi trong khoảng 0-999
            let temp_val = 15u64 + ((i as u64 / 1000) % 500); // Thay đổi chậm hơn
            (F1::from(soil_val), F1::from(temp_val))
        })
        .collect();
    println!("Sensor data generation took {:?}.", start_data_gen.elapsed());


    let circuit_primary_template = SimpleLinearModelCircuit::new(w_s, w_t, b, None, None);

    println!("Producing public parameters (this may take a moment)...");
    let start_pp = Instant::now();
    type C1 = SimpleLinearModelCircuit<F1>;
    let pp = PublicParams::<E1, E2, C1>::setup(
        &circuit_primary_template,
        &*S1::ck_floor(),
        &*S2::ck_floor(),
    )
    .unwrap();
    println!("PublicParams::setup took {:?} ", start_pp.elapsed());

    // Thông tin về constraints và variables (giữ nguyên)
    println!(
        "Number of constraints per step (primary circuit): {}",
        pp.num_constraints().0
    );
    println!(
        "Number of constraints per step (secondary circuit): {}",
        pp.num_constraints().1
    );
     println!(
        "Number of variables per step (primary circuit): {}",
        pp.num_variables().0
    );
    println!(
        "Number of variables per step (secondary circuit): {}",
        pp.num_variables().1
    );

    // Tạo vector các instance mạch.
    // CẢNH BÁO: Với num_steps = 1,000,000, vector này sẽ lớn (~170-200MB RAM).
    // Nếu gặp vấn đề về bộ nhớ, một giải pháp là tạo `circuit_step_i` ngay trong vòng lặp `prove_step`
    // thay vì tạo tất cả upfront, tuy nhiên việc này sẽ làm thay đổi cấu trúc so với minroot.rs.
    println!("Preparing {} circuit instances (this will consume RAM)...", num_steps);
    let start_circuit_gen = Instant::now();
    let primary_circuits: Vec<C1> = (0..num_steps)
        .map(|i| {
            let (soil, temp) = sensor_data_per_step[i]; // Truy cập trực tiếp, không cần clone data
            SimpleLinearModelCircuit::new(w_s, w_t, b, Some(soil), Some(temp))
        })
        .collect();
    println!("Circuit instances preparation took {:?}.", start_circuit_gen.elapsed());


    let z0_primary = vec![F1::from(0u64)];

    println!("Generating a RecursiveSNARK for {} steps...", num_steps);
    println!("This will take an EXTREMELY LONG TIME. Progress will be reported periodically.");
    let overall_start_time = Instant::now();

    let mut recursive_snark =
        RecursiveSNARK::<E1, E2, C1>::new(&pp, &primary_circuits[0], &z0_primary).unwrap();
    
    let progress_interval = num_steps / 20; // In tiến độ khoảng 20 lần (hoặc ít nhất 1)
    let report_interval = if progress_interval == 0 { 1 } else { progress_interval };


    for i in 0..num_steps {
        let circuit_step_i = &primary_circuits[i]; // Sử dụng tham chiếu đến circuit đã tạo
        
        // In tiến độ ít thường xuyên hơn
        if (i + 1) % report_interval == 0 || i == 0 || i == num_steps - 1 {
            println!(
                "Proving step {}/{}... (Total elapsed: {:?})",
                i + 1,
                num_steps,
                overall_start_time.elapsed()
            );
        }
        // let step_start_time = Instant::now(); // Có thể bỏ qua để giảm overhead
        
        let res = recursive_snark.prove_step(&pp, circuit_step_i);
        
        if !res.is_ok() {
             eprintln!("Error proving step {}: {:?}", i + 1, res.err());
             panic!("Failed to prove step {}", i + 1);
        }

        // Bỏ qua việc in thời gian cho từng bước để tránh làm chậm và quá nhiều output
        // if (i + 1) % report_interval == 0 || i == 0 || i == num_steps - 1 {
        //     println!(
        //         "RecursiveSNARK::prove_step {} done in {:?}", // Step i+1
        //         i + 1,
        //         step_start_time.elapsed()
        //     );
        // }

        // Việc kiểm tra y_i_expected mỗi bước cũng sẽ rất tốn kém và tạo nhiều output.
        // Nên tin tưởng vào quá trình verify cuối cùng.
    }
    println!(
        "Total time for {} proof steps: {:?}",
        num_steps,
        overall_start_time.elapsed()
    );

    println!("Verifying a RecursiveSNARK (this might also take time)...");
    let start_verify = Instant::now();
    let res_verify = recursive_snark.verify(&pp, num_steps, &z0_primary);
    println!(
        "RecursiveSNARK::verify: {:?}, took {:?}",
        res_verify.is_ok(),
        start_verify.elapsed()
    );
    if !res_verify.is_ok() {
        panic!("RecursiveSNARK verification failed!");
    }


    println!("Generating a CompressedSNARK using Spartan (this will take time)...");
    let start_compress_setup = Instant::now();
    let (pk, vk) = CompressedSNARK::<E1, E2, C1, S1, S2>::setup(&pp).unwrap();
    println!("CompressedSNARK setup took {:?}", start_compress_setup.elapsed());
    
    let start_compress_prove = Instant::now();
    let res_compress_prove = CompressedSNARK::<E1, E2, C1, S1, S2>::prove(&pp, &pk, &recursive_snark);
    if !res_compress_prove.is_ok() {
        panic!("CompressedSNARK prove failed: {:?}", res_compress_prove.err());
    }
    println!(
        "CompressedSNARK::prove took {:?}",
        start_compress_prove.elapsed()
    );
    let compressed_snark = res_compress_prove.unwrap();

    // Optional: Encode and print size
    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
    bincode::serialize_into(&mut encoder, &compressed_snark).unwrap();
    let compressed_snark_encoded = encoder.finish().unwrap();
    println!(
        "CompressedSNARK::len {:?} bytes",
        compressed_snark_encoded.len()
    );

    println!("Verifying a CompressedSNARK (this might also take time)...");
    let start_verify_compressed = Instant::now();
    let res_verify_compressed = compressed_snark.verify(&vk, num_steps, &z0_primary);
    println!(
        "CompressedSNARK::verify: {:?}, took {:?}",
        res_verify_compressed.is_ok(),
        start_verify_compressed.elapsed()
    );
    if !res_verify_compressed.is_ok() {
        panic!("CompressedSNARK verification failed!");
    }

    println!("=========================================================");
    println!(
        "SimpleLinearModel recursive proof for {} steps completed and verified successfully!", num_steps
    );
}