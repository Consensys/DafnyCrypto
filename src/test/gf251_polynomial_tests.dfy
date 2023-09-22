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

module Gf251PolynomialTests {
    import opened MathUtils
    import GF251
    import opened Gf251Polynomial
    import opened Utils

    // ==============================================================
    // Field Elements
    // ==============================================================

    const vm3 : GF251.Element := GF251.From(248)
    const vm2 : GF251.Element := GF251.From(249)
    const vm1 : GF251.Element := GF251.From(250)
    const v0 : GF251.Element := GF251.From(0)
    const v1 : GF251.Element := GF251.From(1)
    const v2 : GF251.Element := GF251.From(2)
    const v3 : GF251.Element := GF251.From(3)
    const v4 : GF251.Element := GF251.From(4)
    const v5 : GF251.Element := GF251.From(5)
    const v6 : GF251.Element := GF251.From(6)
    const v7 : GF251.Element := GF251.From(7)
    const v8 : GF251.Element := GF251.From(8)
    const v9 : GF251.Element := GF251.From(9)
    const v10 : GF251.Element := GF251.From(10)
    const v11 : GF251.Element := GF251.From(11)
    const v17 : GF251.Element := GF251.From(17)
    const v33 : GF251.Element := GF251.From(33)
    const v41 : GF251.Element := GF251.From(41)
    const v46 : GF251.Element := GF251.From(46)
    const v49 : GF251.Element := GF251.From(49)
    const v52 : GF251.Element := GF251.From(52)
    const v94 : GF251.Element := GF251.From(94)
    const v99 : GF251.Element := GF251.From(99)
    const v100 : GF251.Element := GF251.From(100)
    const v101 : GF251.Element := GF251.From(101)
    const v104 : GF251.Element := GF251.From(104)
    const v119 : GF251.Element := GF251.From(119)
    const v144 : GF251.Element := GF251.From(144)
    const v155 : GF251.Element := GF251.From(155)
    const v156 : GF251.Element := GF251.From(156)
    const v182 : GF251.Element := GF251.From(182)
    const v200 : GF251.Element := GF251.From(200)
    const v213 : GF251.Element := GF251.From(213)
    const v233 : GF251.Element := GF251.From(233)
    const v249 : GF251.Element := GF251.From(249)
    const v250 : GF251.Element := GF251.From(250)

    // ==============================================================
    // Example polynomials
    // ==============================================================

    const POLY_m2X2 := [v0,v0,vm2] // -2x^2
    const POLY_m2X := [v0,vm2] // -2x
    const POLY_mX := [v0,vm1] // -x
    const POLY_m2 := [vm2] // -2
    const POLY_m1 := [vm1] // -1
    const POLY_1 := [v1] // 1
    const POLY_2 := [v2] // 2
    const POLY_3 := [v3] // 3
    const POLY_X := [v0,v1] // x
    const POLY_2X := [v0,v2] // 2x
    const POLY_3X := [v0,v3] // 3x
    const POLY_X2 := [v0,v0,v1] // x^2
    const POLY_2X2 := [v0,v0,v2] // 2x^2
    const POLY_3X2 := [v0,v0,v3] // 3x^2
    const POLY_X3 := [v0,v0,v0,v1] // x^3
    const POLY_3_X2 := [v3,v0,v1] // 3 + x^2
    const POLY_3_X3 := [v3,v0,v0,v1] // 3 + x^3

    // ==============================================================
    // Tests
    // ==============================================================

    method {:test} test_eval() {
       expect Eval(POLY_1,v2) == v1;
       expect Eval(POLY_X,v2) == v2;
       expect Eval(POLY_X,v101) == v101;
       expect Eval(POLY_X,v250) == v250;
       expect Eval(POLY_2X,v1) == v2;
       expect Eval(POLY_2X,v3) == v6;
       expect Eval(POLY_2X,v100) == v200;
       expect Eval(POLY_2X,v250) == v249;
    }

    method {:test} test_neg() {
        expect Neg(POLY_1) == POLY_m1;
        expect Neg(POLY_2) == POLY_m2;
        expect Neg(POLY_X) == POLY_mX;
        expect Neg(POLY_2X) == POLY_m2X;
        expect Neg(POLY_2X2) == POLY_m2X2;
    }

    method {:test} test_lagrange() {
        var p0 := Interpolate([v0,v1],[v213,v3]);
        expect p0 == [v213,v41];
        expect Eval(p0,v0) == v213;
        expect Eval(p0,v1) == v3;
        //
        var p1 := Interpolate([v0,v1,v2],[v7,v11,v213]);
        expect p1 == [v7, v156, v99];
        expect Eval(p1,v0) == v7;
        expect Eval(p1,v1) == v11;
        expect Eval(p1,v2) == v213;
        //
        var p2 := Interpolate([v0,v3,v6],[v7,v11,v213]);
        expect p2 == [v7, v52, v11];
        expect Eval(p2,v0) == v7;
        expect Eval(p2,v3) == v11;
        expect Eval(p2,v6) == v213;
        //
        var p3 := Interpolate([v0,v1,v2,v3,v4],[v250,v213,v0,v1,v101]);
        expect p3 ==  [v250, v119, v249, v3, v94];
        expect Eval(p3,v0) == v250;
        expect Eval(p3,v1) == v213;
        expect Eval(p3,v2) == v0;
        expect Eval(p3,v3) == v1;
        expect Eval(p3,v4) == v101;
        //
        var p4 := Interpolate([v0,v1,v2,v3,v4,v5,v6,v7,v8,v9],[v3,v213,v11,v7,v213,v52,v101,v6,v94,v99]);
        expect p4 == [v3, v155, v46, v17, v182, v33, v49, v144, v233, v104];
        expect Eval(p4,v0) == v3;
        expect Eval(p4,v1) == v213;
        expect Eval(p4,v2) == v11;
        expect Eval(p4,v3) == v7;
        expect Eval(p4,v4) == v213;
        expect Eval(p4,v5) == v52;
        expect Eval(p4,v6) == v101;
        expect Eval(p4,v7) == v6;
        expect Eval(p4,v8) == v94;
        expect Eval(p4,v9) == v99;
    }
}