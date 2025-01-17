#include <cstdint>

#include <gtest/gtest.h>

#include <libff/algebra/curves/alt_bn128/alt_bn128_pp.hpp>

#include <libff/algebra/fields/binary/gf64.hpp>
#include "libiop/relations/examples/r1cs_examples.hpp"
#include "libiop/snark/ligero_snark.hpp"
#include "libiop/bcs/common_bcs_parameters.hpp"

namespace libiop {

TEST(InterleavedR1CSSnarkTest, SimpleTest) {
    return;

    /* Set up R1CS */
    typedef libff::gf64 FieldT;

//    std::size_t num_constraints = 1 << 18;
    // std::size_t constraint_dim = 20;
//    std::size_t num_inputs = 1 << 17;
//    std::size_t num_variables = (1 << 18) - 1;
//    r1cs_example<FieldT> ex = generate_r1cs_example<FieldT>(num_constraints, num_inputs, num_variables);

    // r1cs_example<FieldT> ex = generate_range_proof_r1cs<FieldT>(128, 1024);

    // r1cs_constraint_system<FieldT> constraints = ex.constraint_system_;
    // r1cs_primary_input<FieldT> primary_input = ex.primary_input_;
    // r1cs_auxiliary_input<FieldT> auxiliary_input = ex.auxiliary_input_;

    // EXPECT_TRUE(constraints.is_satisfied(primary_input, auxiliary_input));

    // /* Actual SNARK test */
    // for (std::size_t i = 0; i < 2; i++)
    // {
    //     ligero_snark_parameters<FieldT, binary_hash_digest> parameters;
    //     parameters.security_level_ = 128;
    //     parameters.height_width_ratio_ = 0.001;
    //     parameters.RS_extra_dimensions_ = 2;
    //     parameters.make_zk_ = (i == 1);
    //     parameters.domain_type_ = affine_subspace_type;
    //     parameters.LDT_reducer_soundness_type_ = LDT_reducer_soundness_type::proven;
    //     parameters.bcs_params_ = default_bcs_params<FieldT, binary_hash_digest>(
    //         blake2b_type, parameters.security_level_, constraint_dim);

    //     const ligero_snark_argument<FieldT, binary_hash_digest> argument =
    //         ligero_snark_prover<FieldT>(constraints, primary_input, auxiliary_input, parameters);

    //     const bool bit = ligero_snark_verifier<FieldT, binary_hash_digest>(constraints, primary_input, argument, parameters);

    //     EXPECT_TRUE(bit);
    // }
}

bool ligero_fixed_snark_test(size_t bit_width_dim, size_t instance_dim) {
    printf("START ligero FIXED range proof with bit width dim: %d and instance dim: %d\n", bit_width_dim, instance_dim);
    /* Set up R1CS */
    libff::alt_bn128_pp::init_public_params();
    typedef libff::alt_bn128_Fr FieldT;

    size_t bit_width = 1 << bit_width_dim;
    size_t instance_num = 1 << instance_dim;
    // std::size_t num_constraints = 16;
    std::size_t constraint_dim = bit_width_dim + instance_dim + 1;
    r1cs_example<FieldT> ex = generate_fixed_range_proof_r1cs<FieldT>(bit_width, instance_num);

    r1cs_constraint_system<FieldT> constraints = ex.constraint_system_;
    r1cs_primary_input<FieldT> primary_input = ex.primary_input_;
    r1cs_auxiliary_input<FieldT> auxiliary_input = ex.auxiliary_input_;

    if (!constraints.is_satisfied(primary_input, auxiliary_input)) {
        return false;
    }

    /* Actual SNARK test */
    ligero_snark_parameters<FieldT, binary_hash_digest> parameters;
    parameters.security_level_ = 120;
    parameters.height_width_ratio_ = 0.001;
    parameters.RS_extra_dimensions_ = 2;
    parameters.make_zk_ = true;
    parameters.domain_type_ = multiplicative_coset_type;
    parameters.LDT_reducer_soundness_type_ = LDT_reducer_soundness_type::proven;
    parameters.bcs_params_ = default_bcs_params<FieldT, binary_hash_digest>(
        blake2b_type, parameters.security_level_, constraint_dim);

    const ligero_snark_argument<FieldT, binary_hash_digest> argument =
        ligero_snark_prover<FieldT, binary_hash_digest>(constraints, primary_input, auxiliary_input, parameters);

    const bool bit = ligero_snark_verifier<FieldT, binary_hash_digest>(constraints, primary_input, argument, parameters);

    return bit;
}

bool ligero_arbitrary_snark_test(size_t bit_width_dim, size_t instance_dim) {
    printf("START ligero ARBITRARY range proof with bit width dim: %d and instance dim: %d\n", bit_width_dim, instance_dim);
    /* Set up R1CS */
    libff::alt_bn128_pp::init_public_params();
    typedef libff::alt_bn128_Fr FieldT;

    size_t bit_width = 1 << bit_width_dim;
    size_t instance_num = 1 << instance_dim;
    std::size_t constraint_dim = bit_width_dim + instance_dim + 4;
    r1cs_example<FieldT> ex = generate_arbitrary_range_proof_r1cs<FieldT>(bit_width, instance_num);

    r1cs_constraint_system<FieldT> constraints = ex.constraint_system_;
    r1cs_primary_input<FieldT> primary_input = ex.primary_input_;
    r1cs_auxiliary_input<FieldT> auxiliary_input = ex.auxiliary_input_;

    if (!constraints.is_satisfied(primary_input, auxiliary_input)) {
        return false;
    }

    /* Actual SNARK test */
    ligero_snark_parameters<FieldT, binary_hash_digest> parameters;
    parameters.security_level_ = 120;
    parameters.height_width_ratio_ = 0.001;
    parameters.RS_extra_dimensions_ = 2;
    parameters.make_zk_ = true;
    parameters.domain_type_ = multiplicative_coset_type;
    parameters.LDT_reducer_soundness_type_ = LDT_reducer_soundness_type::proven;
    parameters.bcs_params_ = default_bcs_params<FieldT, binary_hash_digest>(
        blake2b_type, parameters.security_level_, constraint_dim);

    const ligero_snark_argument<FieldT, binary_hash_digest> argument =
        ligero_snark_prover<FieldT, binary_hash_digest>(constraints, primary_input, auxiliary_input, parameters);

    const bool bit = ligero_snark_verifier<FieldT, binary_hash_digest>(constraints, primary_input, argument, parameters);

    return bit;
}

TEST(InterleavedR1CSSnarkMultiplicativeTest, SimpleTest) {
    size_t bit_width_dim[] = {5, 7, 9, 7, 7, 7};
    size_t instance_dim[] = {0, 0, 0, 6, 8, 10};
    EXPECT_EQ(sizeof(bit_width_dim), sizeof(instance_dim));
    EXPECT_TRUE(ligero_arbitrary_snark_test(bit_width_dim[5], instance_dim[5]));
    // EXPECT_TRUE(ligero_fixed_snark_test(bit_width_dim[3], instance_dim[3]));
}

}
