/*
 * Copyright 2023 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */
include "../util/option.dfy"
include "../util/int.dfy"
include "../ecc/affine_curve.dfy"

// The ellptic curve given by y^2 == x^3 + 3.
module AltBn128 refines AffineCurve {
    // Specify the number of elements in the finite field
    const N := ALT_BN128_PRIME;
    // As per EIP196
    const ALT_BN128_PRIME := 21888242871839275222246405745257275088696311157297823662689037894645226208583
    // Identifies the number of distinct points in the curve.
    const ALT_BN128_ORDER := 21888242871839275222246405745257275088548364400416034343698204186575808495617
    // Parameters for the curve
    const A := Value(0);
    const B := Value(3);
    // Axiom to establish that this is really a prime field.  This is needed
    // because Dafny cannot possible determine that ALT_BN128_PRIME is a prime.
    lemma {:axiom} IsPrimeField()
    ensures IsPrime(ALT_BN128_PRIME) {
        assume {:axiom} IsPrime(ALT_BN128_PRIME);
    }
}
