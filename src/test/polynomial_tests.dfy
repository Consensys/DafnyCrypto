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
include "../dafny/util/polynomial.dfy"
include "utils.dfy"

module PolynomialTests {
    import opened MathUtils
    import opened Polynomial
    import opened Utils

    // ==============================================================
    // Example polynomials
    // ==============================================================

    const TERM_m2 : Term := (-2,0)
    const TERM_m1 : Term := (-1,0)
    const TERM_1 : Term := (1,0)
    const TERM_2 : Term := (2,0)
    const TERM_3 : Term := (3,0)
    const TERM_X : Term := (1,1)
    const TERM_2X : Term := (2,1)
    const TERM_3X : Term := (3,1)
    const TERM_X2 : Term := (1,2)
    const TERM_2X2 : Term := (2,2)
    const TERM_3X2 : Term := (3,2)
    const TERM_X3 : Term := (1,3)
    const TERM_2X3 : Term := (2,3)
    const TERM_3X3 : Term := (3,3)

    const POLY_m2X2 := [0,0,-2] // -2x^2
    const POLY_m2X := [0,-2] // -2x
    const POLY_mX := [0,-1] // -x
    const POLY_m2 := [-2] // -2
    const POLY_m1 := [-1] // -1
    const POLY_1 := [1] // 1
    const POLY_2 := [2] // 2
    const POLY_3 : Polynomial := [3] // 3
    const POLY_X : Polynomial := [0,1] // x
    const POLY_2X : Polynomial := [0,2] // 2x
    const POLY_3X : Polynomial := [0,3] // 3x
    const POLY_X2 : Polynomial := [0,0,1] // x^2
    const POLY_2X2 : Polynomial := [0,0,2] // 2x^2
    const POLY_3X2 : Polynomial := [0,0,3] // 3x^2
    const POLY_X3 : Polynomial := [0,0,0,1] // x^3
    const POLY_3_X2 : Polynomial := [3,0,1] // 3 + x^2
    const POLY_3_X3 : Polynomial := [3,0,0,1] // 3 + x^3

    // ==============================================================
    // Tests
    // ==============================================================

    method {:test} test_eval() {
        assert PowN(1,1) == [1];
        assert VecMul([1],[1]) == [1];
        AssertAndExpect(Eval(POLY_1,1) == 1);
        assert PowN(2,1) == [1];
        AssertAndExpect(Eval(POLY_1,2) == 1);
        // x
        assert PowN(1,2) == [1,1];
        AssertAndExpect(Eval(POLY_X,1) == 1);
        assert PowN(2,2) == [1,2];
        assert VecMul([1,2],[0,1]) == [0,2];
        assert VecSum([0,2]) == 2;
        AssertAndExpect(Eval(POLY_X,2) == 2);
        // x^2
        assert PowN(1,3) == [1,1,1];
        AssertAndExpect(Eval(POLY_X2,1) == 1);
        assert PowN(2,3) == [1,2,4];
        assert VecMul([1,2,4],[0,0,1]) == [0,0,4];
        assert VecSum([0,0,4]) == 4;
        AssertAndExpect(Eval(POLY_X2,2) == 4);
        // 3 + x^2
        AssertAndExpect(Eval(POLY_3_X2,1) == 4);
        AssertAndExpect(Eval(POLY_3_X2,2) == 7);
    }

    method {:test} test_neg() {
        expect Neg(POLY_1) == POLY_m1;
        expect Neg(POLY_2) == POLY_m2;
        expect Neg(POLY_X) == POLY_mX;
        expect Neg(POLY_2X) == POLY_m2X;
        expect Neg(POLY_2X2) == POLY_m2X2;
    }

    method {:test} test_add() {
        expect Add(POLY_1,POLY_2) == POLY_3;
        expect Add(POLY_2,POLY_1) == POLY_3;
        expect Add(POLY_X,POLY_2X) == POLY_3X;
        expect Add(POLY_2X,POLY_X) == POLY_3X;
        expect Add(POLY_X2,POLY_2X2) == POLY_3X2;
        expect Add(POLY_2X2,POLY_X2) == POLY_3X2;
    }

    method {:test} test_sub() {
        expect Sub(POLY_1,POLY_2) == POLY_m1;
        expect Sub(POLY_2,POLY_1) == POLY_1;
        expect Sub(POLY_X,POLY_2X) == POLY_mX;
        expect Sub(POLY_2X,POLY_X) == POLY_X;
        expect Sub(POLY_X2,POLY_3X2) == POLY_m2X2;
        expect Sub(POLY_2X2,POLY_X2) == POLY_X2;
    }

    method {:test} test_sum() {
        expect Sum([POLY_1]) == POLY_1;
        expect Sum([POLY_1,POLY_1]) == POLY_2;
        expect Sum([POLY_1,POLY_2]) == POLY_3;
        expect Sum([POLY_2,POLY_1]) == POLY_3;
        expect Sum([POLY_X,POLY_X]) == POLY_2X;
    }

    method {:test} test_multerm() {
        expect MulTerm(POLY_1,TERM_1,1) == POLY_1;
        expect MulTerm(POLY_1,TERM_2,1) == POLY_2;
        expect MulTerm(POLY_1,TERM_X,2) == POLY_X;
        expect MulTerm(POLY_2,TERM_X,2) == POLY_2X;
        expect MulTerm(POLY_2X,TERM_X,3) == POLY_2X2;
        expect MulTerm(POLY_X,TERM_X2,4) == POLY_X3;
    }

    method test_mul() {
        expect Mul(POLY_1,POLY_1) == POLY_1;
        expect Mul(POLY_1,POLY_2) == POLY_2;
        expect Mul(POLY_2,POLY_1) == POLY_2;
        expect Mul(POLY_X,POLY_2) == POLY_2X;
        expect Mul(POLY_3,POLY_X) == POLY_3X;
        expect Mul(POLY_X,POLY_X) == POLY_X2;
        expect Mul(POLY_X,POLY_2X) == POLY_2X2;
    }
}