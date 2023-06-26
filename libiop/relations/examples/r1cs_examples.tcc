/** @file
 *****************************************************************************

 Implementation of functions to sample R1CS examples with prescribed parameters
 (according to some distribution).

 See r1cs_examples.hpp .

 *****************************************************************************
 * @author     This file is adapted from libsnark, developed by SCIPR Lab
 *             and contributors
 *             (see AUTHORS for libsnark and here for libiop).
 * @copyright  MIT license (see LICENSE file)
 *****************************************************************************/

#include <cassert>
#include <stdexcept>

#include "libiop/algebra/utils.hpp"

namespace libiop {

    template<typename FieldT>
    r1cs_example<FieldT> generate_range_proof_r1cs(const size_t bit_width, const size_t instance_num) {
        size_t num_bits = bit_width * instance_num;
        size_t padding_length = instance_num * 4 - 1;
        size_t num_variables = num_bits * 7; // A B x diff_A diff_B carry_A carry_B
#define RANGE_A 0
#define RANGE_B 1
#define VALUE_X 2
#define DIFF_A 3
#define DIFF_B 4
#define CARRY_A 5
#define CARRY_B 6

        std::vector<FieldT> range_a, range_b, value_x, diff_a, diff_b, carry_a, carry_b;
        std::vector<FieldT> public_ranges;
        for (size_t i = 0; i < instance_num; i++) {
            size_t a = std::rand() % (1ull << 32);
            size_t b = std::rand() % (1ull << 32);
            if (a > b) {
                std::swap(a, b);
            }

            size_t x = std::rand() % (b - a + 1) + a;
            public_ranges.push_back(FieldT(a));
            public_ranges.push_back(FieldT(b));
            size_t d_a = x - a;
            size_t d_b = b - x;
            size_t c_a = 0, c_b = 0;
            for (size_t j = 0; j < bit_width; j++) {
                carry_a.push_back(FieldT(c_a > 1));
                c_a >>= 1;
                carry_b.push_back(FieldT(c_b > 1));
                c_b >>= 1;
                c_a += (a & 1) + (d_a & 1);
                c_b += (x & 1) + (d_b & 1);

                range_a.push_back(FieldT(a & 1));
                a >>= 1;
                range_b.push_back(FieldT(b & 1));
                b >>= 1;
                value_x.push_back(FieldT(x & 1));
                x >>= 1;
                diff_a.push_back(FieldT(d_a & 1));
                d_a >>= 1;
                diff_b.push_back(FieldT(d_b & 1));
                d_b >>= 1;
            }
        }

        for (size_t i = 1; i < instance_num * 2; i++) {
            public_ranges.push_back(FieldT::zero());
        }

        r1cs_constraint_system<FieldT> cs;
        cs.primary_input_size_ = instance_num * 4 - 1;
        cs.auxiliary_input_size_ = num_bits * 7;
        r1cs_variable_assignment<FieldT> variables;

        variables.insert(variables.end(), range_a.begin(), range_a.end());
        variables.insert(variables.end(), range_b.begin(), range_b.end());
        variables.insert(variables.end(), value_x.begin(), value_x.end());
        variables.insert(variables.end(), diff_a.begin(), diff_a.end());
        variables.insert(variables.end(), diff_b.begin(), diff_b.end());
        variables.insert(variables.end(), carry_a.begin(), carry_a.end());
        variables.insert(variables.end(), carry_b.begin(), carry_b.end());

        // constraint range a and range b
        for (size_t i = 0; i < instance_num; i++) {
            linear_combination<FieldT> A, B, C;
            for (size_t j = 0; j < 32; j++) {
                A.add_term(num_bits * RANGE_A + bit_width * i + 1 + padding_length, FieldT(2) ^ (1ull << j));
            }
            A.add_term(i * 2 + 1, -FieldT::one());
        }

        // constraint all variables in 0/1
        for (size_t i = 0; i < num_variables; i++) {
            linear_combination<FieldT> A, B, C;
            A.add_term(i + 1 + padding_length, FieldT::one());
            B.add_term(i + 1 + padding_length, FieldT::one());
            B.add_term(0, -FieldT::one());
            cs.add_constraint(r1cs_constraint<FieldT>(A, B, C));
        }

        // constraint all carry[0] is 0
        for (size_t i = 0; i < instance_num; i++) {
            linear_combination<FieldT> A, B, C, D;
            A.add_term(num_bits * CARRY_A + bit_width * i + 1 + padding_length, FieldT::one());
            B.add_term(0, FieldT::one());
            cs.add_constraint(r1cs_constraint<FieldT>(A, B, C));
            D.add_term(num_bits * CARRY_B + bit_width * i + 1 + padding_length, FieldT::one());
            cs.add_constraint(r1cs_constraint<FieldT>(D, B, C));
        }

        // constraint a + diff_a = x, x + diff_b = b
        for (size_t i = 0; i < instance_num; i++) {
            for (size_t j = 0; j < bit_width; j++) {
                // a[j] + diff_a[j] + carry_a[j] = x[j] + 2 * carry_a[j+1]
                linear_combination<FieldT> A, B, C;
                A.add_term(num_bits * RANGE_A + i * bit_width + j + 1 + padding_length, FieldT::one());
                A.add_term(num_bits * DIFF_A + i * bit_width + j + 1 + padding_length, FieldT::one());
                A.add_term(num_bits * CARRY_A + i * bit_width + j + 1 + padding_length, FieldT::one());
                A.add_term(num_bits * VALUE_X + i * bit_width + j + 1 + padding_length, -FieldT::one());
                if (j < bit_width - 1) {
                    A.add_term(num_bits * CARRY_A + i * bit_width + j + 2 + padding_length, -FieldT::one() - FieldT::one());
                }
                B.add_term(0, FieldT::one());
                cs.add_constraint(r1cs_constraint<FieldT>(A, B, C));

                // x[j] + diff_b[j] + carry_b[j] = b[j] + 2 * carry_b[j+1]
                linear_combination<FieldT> D;
                D.add_term(num_bits * VALUE_X + i * bit_width + j + 1 + padding_length, FieldT::one());
                D.add_term(num_bits * DIFF_B + i * bit_width + j + 1 + padding_length, FieldT::one());
                D.add_term(num_bits * CARRY_B + i * bit_width + j + 1 + padding_length, FieldT::one());
                D.add_term(num_bits * RANGE_B + i * bit_width + j + 1 + padding_length, -FieldT::one());
                if (j < bit_width - 1) {
                    D.add_term(num_bits * CARRY_B + i * bit_width + j + 2 + padding_length, -FieldT::one() - FieldT::one());
                }
                cs.add_constraint(r1cs_constraint<FieldT>(D, B, C));
            }
        }

        while (cs.num_constraints() < num_bits * 16) {
            linear_combination<FieldT> A;
            cs.add_constraint(r1cs_constraint<FieldT>(A, A, A));
        }
        r1cs_primary_input<FieldT> primary_input(public_ranges.begin(), public_ranges.end());
        r1cs_primary_input<FieldT> auxiliary_input(variables.begin(), variables.end());
        assert(cs.primary_input_size_ == instance_num * 4 - 1);
        assert(cs.auxiliary_input_size_ == num_bits * 7);
        assert(cs.is_satisfied(primary_input, auxiliary_input));
        assert(cs.num_variables() < num_bits * 8);

        return r1cs_example<FieldT>(std::move(cs), std::move(primary_input), std::move(auxiliary_input));
    }

template<typename FieldT>
r1cs_example<FieldT> generate_r1cs_example(const size_t num_constraints,
                                           const size_t num_inputs,
                                           const size_t num_variables)
{
    if (num_inputs > num_variables)
    {
        throw std::invalid_argument("Number of inputs can't exceed number of variables.");
    }

    r1cs_constraint_system<FieldT> cs;
    cs.primary_input_size_ = num_inputs;
    cs.auxiliary_input_size_ = num_variables - num_inputs;

    const r1cs_variable_assignment<FieldT> full_variable_assignment
        = random_FieldT_vector<FieldT>(num_variables);

    for (size_t i = 0; i < num_constraints; ++i)
    {
        linear_combination<FieldT> A, B, C;

        const std::size_t A_idx = i % num_variables;
        const std::size_t B_idx = (i + 7) % num_variables;


        A.add_term(A_idx + 1, FieldT::one());
        B.add_term(B_idx + 1, FieldT::one());
        const FieldT AB_val = full_variable_assignment[A_idx] * full_variable_assignment[B_idx];

        const std::size_t C_idx = (2 * i + 1) % num_variables;
        const FieldT C_val = full_variable_assignment[C_idx];
        if (C_val.is_zero())
        {
            C.add_term(0, AB_val);
        }
        else
        {
            C.add_term(C_idx + 1, AB_val * C_val.inverse());
        }

        cs.add_constraint(r1cs_constraint<FieldT>(A, B, C));
    }

    /* split variable assignment */
    r1cs_primary_input<FieldT> primary_input(full_variable_assignment.begin(), full_variable_assignment.begin() + num_inputs);
    r1cs_primary_input<FieldT> auxiliary_input(full_variable_assignment.begin() + num_inputs, full_variable_assignment.end());

    /* sanity checks */
    assert(cs.num_variables() == num_variables);
    assert(cs.num_variables() >= num_inputs);
    assert(cs.num_inputs() == num_inputs);
    assert(cs.num_constraints() == num_constraints);
    assert(cs.is_satisfied(primary_input, auxiliary_input));

    return r1cs_example<FieldT>(std::move(cs), std::move(primary_input), std::move(auxiliary_input));
}

} // libiop
