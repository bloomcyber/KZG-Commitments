// Random number generation and scalar point multiplication
// Crate contains functions, modules, and traits.

// use ark_bn254::{Bn254, Fr, G1Affine, G2Affine}; 
// use ark_ec::short_weierstrass::Affine;
// use ark_ec::twisted_edwards::MontgomeryAffine;
// BN254 elliptic curve
// use ark_ec::AffineRepr;   //for affine representation of the points. Offers compact representation compared to Projective but not efficient for operations.
// use ark_ec::CurveGroup;   //for projective representation of the points. Effective for mul and other operatoins.

use ark_bn254::{Bn254, G1Affine, G1Projective, G2Affine, Fr, Fq};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::{BigInteger, Field, PrimeField};

// use ark_std::UniformRand;
// use std::ops::Mul;
// use rand::thread_rng;

// use ark_ff::Fp;
// use ark_ff::MontBackend;
use ark_poly::DenseUVPolynomial;
// Curve traits for G1, G2
use rand::Rng; // Random number generator
use rand::thread_rng; // Thread-local RNG
use ark_std::UniformRand; // Uniform random trait
use ark_std::Zero;
use std::ops::Mul;
use std::vec;
use ark_poly::{univariate::DensePolynomial,univariate::DenseOrSparsePolynomial,Polynomial};



// Generate a random field element 
fn generate_random_fr() -> Fr {
    let mut rng = thread_rng();
    Fr::rand(&mut rng)
}

// Get the generators for the curve
fn get_generators() -> (G1Affine, G2Affine) {
    let g1 = G1Affine::generator(); // Get base generator for G1
    let g2 = G2Affine::generator(); // Get base generator for G2
    (g1, g2)
}

// Compute powers of tau: τ^i * G1
fn powers_of_tau(generator_1: G1Affine, generator_2: G2Affine, tau: Fr, degree: usize) -> (Vec<G1Affine>,Vec<G2Affine>) {
    let mut crs = vec![generator_1]; // Start with generator_1
    let mut current_point = generator_1.into_group(); // Track current power

    for _ in 1..degree {
        current_point = current_point.mul(tau); // Compute τ^i * G1
        crs.push(current_point.into_affine());
    }

    let mut crs2 = vec![generator_2]; // Start with generator_1
    let mut current_point = generator_2.into_group(); // Track current power

    for _ in 1..degree {
        current_point = current_point.mul(tau); // Compute τ^i * G1
        crs2.push(current_point.into_affine());
    }

    (crs,crs2)
}

//polynomial is f(x)=x^3+2x+4
// we have to commit to this polynomial f. f(tau).G = ((tau)^3+2*(tau)+4).G is the commitment.
// Tau is of type Fr. And 

fn kzg_commitment(crs:&Vec<G1Affine>,pol:&Vec<Fr>)-> G1Affine{
	
    assert!(crs.len() >= pol.len(), "CRS vector is too short for the polynomial");
    //store identity element 
	let mut comm_pol:G1Projective = G1Projective::zero();
	for i in 0..pol.len(){
		
		if !pol[i].is_zero() {
			let mut crs_point= crs[i].into_group();
			crs_point = crs_point.mul(pol[i]);
			comm_pol=comm_pol+crs_point;
		}
	}
	comm_pol.into_affine()   //affine representation of the point on the BN254 curve. 
}

// what needs to be done now?
// what do we have now?
    // given a polynomial in vector form, we give its polynomial commitment. Ok.
    // In the KZG commitment scheme, once the pol. commitment is done. The verifier asks the evaluation of a chosen point on the committed polynomial. 
    // Ok, for given x, we have to find the y. The statement "(x,y) lies on the polynomial curve" should be proven to the verifier. 
    // We have to calculate, 
    //
    /*  if P(z)=y, when x=z ==> for the polynomial , P(x)-y=0 at x=z,
    ==> P(x)-y/(x-z)=Q(x)    Same witness Q(secret).G for all the evaluations? 
    ==> Above relation has to be checked. As per scwartz zippel lemma( Different polynomials have most points different), majority of points agree the relation if it is true at some set of points. Did we get the lemma correct?
    ==> P(secret)P(secret)-y/(secret-z)=Q(secret)
    ==> But the secret is not known to the verifier and the prover. But they can compute it using the CRS, the value P(secret).G
    ==> So we check the relation, P(secret).G-y.G/(secret-z).G=Q(secret).G
    ==> Here P(secret).G is the commitment we have calculated for the polynomial. And Q(secret).G will be the evaluation commitment or the witness. 

y=f(x)=x^3+2x+4
(x-4)
     */

// fn witness(pol:Vec<Fr>, x:Fr) -> Vec<Affine>{
//     // evaluate the polynomial at x, and get the Q(x)
//     Polynomial.

// }

fn q_pol(pol:DensePolynomial<Fr>,z:Fr) -> (DensePolynomial<Fr>, Fr) {

    let divisor_pol = DensePolynomial::from_coefficients_vec(vec![-z,Fr::from(1u32)]);
    
    let y= pol.evaluate(&z);
    
        // P(x)-y/(x-z)=Q(x)

        // Calculate dividend polynomial  P(x)-y
    let dividend_pol = &pol - &DensePolynomial::from_coefficients_vec(vec![y]);


    // convert to Dense or sparse polynomial type
    let dividend_pol_1=DenseOrSparsePolynomial::from(dividend_pol);
    let divisor_pol_1=DenseOrSparsePolynomial::from(divisor_pol);

    // let div_pol = dividend_pol.clone();
    let res = dividend_pol_1.divide_with_q_and_r(&divisor_pol_1).expect("Division failed");

    let (quotient_pol,rem_pol) = res;

    println!("Quotient polynomial is {:?} and Remainder Polynomial is {:?}", quotient_pol, rem_pol);
    (quotient_pol,y)
    
}


fn verify(p_x:&G1Affine, q_x:&G1Affine, z:&Fr, y:&Fr, crs1:&Vec<G1Affine>,crs2:&Vec<G2Affine>, g1:&G1Affine,g2:&G2Affine) -> bool {

    
    
    /*  (p(x) -y)  = Q(x) * (x-z)
    e(G1,G2)^(p(x) -y)  = e(G1,G2)^Q(x) * (x-z)
    e(P(x).G1-y.G1,G2) = e(Q(x).G1,x.G2-z.G2)
    at x= secret.
    e(P(sec).G1-y.G1,G2) = e(Q(sec).G1,sec.G2-z.G2)
    ==> e(P_x-y.G1,G2) == e(q_x, sec.G2 -z.G2)

    */

    
    let y_g1 = g1.into_group().mul(y).into_affine(); // y * G1
    
    // subtract two points p_x -y_g1
    let diff1= p_x.into_group()-y_g1.into_group();


    let z_g2 = g2.into_group().mul(z).into_affine(); // z * G2
    // subtract two points crs2[1]-z_g1
    
    let diff2= crs2[1].into_group()-z_g2.into_group();
    
    // check pairing

    

    // 4️⃣ Compute pairings
    let pairing_1 = Bn254::pairing(&diff1, g2);  // e(diff1, G2)
    // let pairing_2 = Bn254::pairing(g1, b_g2);  // e(G1, bG2)

    // 5️⃣ Compute expected result: e(G1, G2)^(a * b)
    // let base_pairing = Bn254::pairing(g1, g2); // e(G1, G2)
    let expected_pairing =Bn254::pairing(q_x, diff2); // e(G1, G2)^(a*b))

    // 6️⃣ Verify bilinearity property
    // println!("Pairing 1 (e(aG1, G2)): {:?}", pairing_1);
    // // println!("Pairing 2 (e(G1, bG2)): {:?}", pairing_2);
    // println!("Expected Pairing (e(G1, G2)^(ab)): {:?}", expected_pairing);

    if pairing_1.0 == expected_pairing.0 {
        println!("✅ Bilinearity property verified successfully!");
        // println!("Pairing 1 {:?} ", pairing_1);
        // println!("Pairing 2 {:?} ", expected_pairing);
        true
    } else {
        
        println!("✅ Bilinearity property verified failed!");
        false
    }
    

    


}

    
fn main() {
    let mut rng = thread_rng();
    let scalar: u32 = rng.gen();
    println!("Random Scalar value: {}", scalar);
    dbg!(scalar);

    let tau = generate_random_fr();
    println!("Tau value is {:?}", tau);

    let (generator_1, generator_2) = get_generators();
    println!("Generator 1 is {:?} and Generator 2 is {:?}", generator_1, generator_2);

    let degree: usize = 10;
    let (crs,crs2) = powers_of_tau(generator_1, generator_2, tau, degree);
    // let crs2 = powers_of_tau(generator_2, tau, degree);
    println!("CRS is {:?} and {:?}", &crs, &crs2);

    // x^3+2x+4
	let pol:Vec<Fr> = vec![Fr::from(4u32), Fr::from(2u32), Fr::from(0u32),Fr::from(1),];

	let comm_pol=kzg_commitment(&crs, &pol);
	println!("The polynomial is {:?} and the Polynomial Committment is {:?}", pol, comm_pol);

    

    let our_pol = DensePolynomial::from_coefficients_vec(vec![Fr::from(4u32), Fr::from(2u32), Fr::from(0u32),Fr::from(1),]);

    let z=Fr::from(3u32);
    let (witness_pol,y) = q_pol(our_pol, z);

    println!("witness polynomial is {:?}", witness_pol);

    let witness_pol_commitment:G1Affine=kzg_commitment(&crs, &witness_pol.coeffs);

    println!("witness polynomial is {:?}", witness_pol_commitment);

    let _ = verify(&comm_pol,&witness_pol_commitment,&z,&y,&crs,&crs2,&generator_1,&generator_2);

}
