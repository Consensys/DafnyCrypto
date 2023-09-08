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

    // 1
    const POLY_1 : Polynomial := [1]
    // 2
    const POLY_2 : Polynomial := [2]
    // 3
    const POLY_3 : Polynomial := [3]
    // x
    const POLY_X : Polynomial := [0,1]
    // 2x
    const POLY_2X : Polynomial := [0,2]
    // 3x
    const POLY_3X : Polynomial := [0,3]
    // x^2
    const POLY_X2 : Polynomial := [0,0,1]
    // 2x^2
    const POLY_2X2 : Polynomial := [0,0,2]
    // 3x^2
    const POLY_3X2 : Polynomial := [0,0,3]
    // 3 + x^2
    const POLY_3_X2 : Polynomial := [3,0,1]
    // 3 + x^3
    const POLY_3_X3 : Polynomial := [3,0,0,1]

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

    method {:test} test_add() {
        expect Add(POLY_1,POLY_2) == POLY_3;
        expect Add(POLY_2,POLY_1) == POLY_3;
        // x
        expect Add(POLY_X,POLY_2X) == POLY_3X;
        expect Add(POLY_2X,POLY_X) == POLY_3X;
        // x^2
        expect Add(POLY_X2,POLY_2X2) == POLY_3X2;
        expect Add(POLY_2X2,POLY_X2) == POLY_3X2;
    }
}