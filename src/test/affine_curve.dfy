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
include "utils.dfy"
include "../dafny/ecc/affine_curve.dfy"

// A simple curve corresponding with Y^2 = x^3 + 1 which, in this case, is
// defined over GF5.  There are nine points in this curve, given as follows:
//
// O; (0,1); (2, 1); (3, 1); (4, 2); (4, 3); (0, 4); (2, 4); (3, 4)
module E11F5 refines AffineCurve {
    import opened Utils
    // Specify the number of elements in the finite field
    const N := 5;
    // Parameters for the curve
    const A := Value(1);
    const B := Value(1);

    const P0_1 : Point := Pair(Value(0),Value(1));
    const P0_4 : Point := Pair(Value(0),Value(4));
    const P2_1 : Point := Pair(Value(2),Value(1));
    const P2_4 : Point := Pair(Value(2),Value(4));
    const P3_1 : Point := Pair(Value(3),Value(1));
    const P3_4 : Point := Pair(Value(3),Value(4));
    const P4_2 : Point := Pair(Value(4),Value(2));
    const P4_3 : Point := Pair(Value(4),Value(3));

    // Check that Dafny agree's on all the members of the curve.
    method {:test} test_members() {
        AssertAndExpect(Infinity.Valid());
        AssertAndExpect(!Pair(Value(0),Value(0)).Valid());
        AssertAndExpect(Pair(Value(0),Value(1)).Valid()); // 1
        AssertAndExpect(!Pair(Value(0),Value(2)).Valid());
        AssertAndExpect(!Pair(Value(0),Value(3)).Valid());
        AssertAndExpect(Pair(Value(0),Value(4)).Valid()); // 2
        AssertAndExpect(!Pair(Value(1),Value(0)).Valid());
        AssertAndExpect(!Pair(Value(1),Value(1)).Valid());
        AssertAndExpect(!Pair(Value(1),Value(2)).Valid());
        AssertAndExpect(!Pair(Value(1),Value(3)).Valid());
        AssertAndExpect(!Pair(Value(1),Value(4)).Valid());
        AssertAndExpect(!Pair(Value(2),Value(0)).Valid());
        AssertAndExpect(Pair(Value(2),Value(1)).Valid());  // 3
        AssertAndExpect(!Pair(Value(2),Value(2)).Valid());
        AssertAndExpect(!Pair(Value(2),Value(3)).Valid());
        AssertAndExpect(Pair(Value(2),Value(4)).Valid()); // 4
        AssertAndExpect(!Pair(Value(3),Value(0)).Valid());
        AssertAndExpect(Pair(Value(3),Value(1)).Valid()); // 5
        AssertAndExpect(!Pair(Value(3),Value(2)).Valid());
        AssertAndExpect(!Pair(Value(3),Value(3)).Valid());
        AssertAndExpect(Pair(Value(3),Value(4)).Valid()); // 6
        AssertAndExpect(!Pair(Value(4),Value(0)).Valid());
        AssertAndExpect(!Pair(Value(4),Value(1)).Valid());
        AssertAndExpect(Pair(Value(4),Value(2)).Valid()); // 7
        AssertAndExpect(Pair(Value(4),Value(3)).Valid()); // 8
        AssertAndExpect(!Pair(Value(4),Value(4)).Valid());
    }

    method {:test} test_double() {
        AssertAndExpect(P0_1.Double() == P4_2);
        AssertAndExpect(P0_4.Double() == P4_3);
        AssertAndExpect(P2_1.Double() == P2_4);
        AssertAndExpect(P2_4.Double() == P2_1);
        AssertAndExpect(P3_1.Double() == P0_1);
        AssertAndExpect(P3_4.Double() == P0_4);
        AssertAndExpect(P4_2.Double() == P3_4);
        AssertAndExpect(P4_3.Double() == P3_1);
    }

    method {:test} test_add() {
        // (0,1)
        AssertAndExpect(P0_1.Add(Infinity) == P0_1);
        AssertAndExpect(P0_1.Add(P0_1) == P4_2);
        AssertAndExpect(P0_1.Add(P0_4) == Infinity);
        AssertAndExpect(P0_1.Add(P2_1) == P3_4);
        AssertAndExpect(P0_1.Add(P2_4) == P4_3);
        AssertAndExpect(P0_1.Add(P3_1) == P2_4);
        AssertAndExpect(P0_1.Add(P3_4) == P3_1);
        AssertAndExpect(P0_1.Add(P4_2) == P2_1);
        AssertAndExpect(P0_1.Add(P4_3) == P0_4);
        // (0,4)
        AssertAndExpect(P0_4.Add(Infinity) == P0_4);
        AssertAndExpect(P0_4.Add(P0_1) == Infinity);
        AssertAndExpect(P0_4.Add(P0_4) == P4_3);
        AssertAndExpect(P0_4.Add(P2_1) == P4_2);
        AssertAndExpect(P0_4.Add(P2_4) == P3_1);
        AssertAndExpect(P0_4.Add(P3_1) == P3_4);
        AssertAndExpect(P0_4.Add(P3_4) == P2_1);
        AssertAndExpect(P0_4.Add(P4_2) == P0_1);
        AssertAndExpect(P0_4.Add(P4_3) == P2_4);
        // (2,1)
        AssertAndExpect(P2_1.Add(Infinity) == P2_1);
        AssertAndExpect(P2_1.Add(P0_1) == P3_4);
        AssertAndExpect(P2_1.Add(P0_4) == P4_2);
        AssertAndExpect(P2_1.Add(P2_1) == P2_4);
        AssertAndExpect(P2_1.Add(P2_4) == Infinity);
        AssertAndExpect(P2_1.Add(P3_1) == P0_4);
        AssertAndExpect(P2_1.Add(P3_4) == P4_3);
        AssertAndExpect(P2_1.Add(P4_2) == P3_1);
        AssertAndExpect(P2_1.Add(P4_3) == P0_1);
        // (2,4)
        AssertAndExpect(P2_4.Add(Infinity) == P2_4);
        AssertAndExpect(P2_4.Add(P0_1) == P4_3);
        AssertAndExpect(P2_4.Add(P0_4) == P3_1);
        AssertAndExpect(P2_4.Add(P2_1) == Infinity);
        AssertAndExpect(P2_4.Add(P2_4) == P2_1);
        AssertAndExpect(P2_4.Add(P3_1) == P4_2);
        AssertAndExpect(P2_4.Add(P3_4) == P0_1);
        AssertAndExpect(P2_4.Add(P4_2) == P0_4);
        AssertAndExpect(P2_4.Add(P4_3) == P3_4);
        // (3,1)
        AssertAndExpect(P3_1.Add(Infinity) == P3_1);
        AssertAndExpect(P3_1.Add(P0_1) == P2_4);
        AssertAndExpect(P3_1.Add(P0_4) == P3_4);
        AssertAndExpect(P3_1.Add(P2_1) == P0_4);
        AssertAndExpect(P3_1.Add(P2_4) == P4_2);
        AssertAndExpect(P3_1.Add(P3_1) == P0_1);
        AssertAndExpect(P3_1.Add(P3_4) == Infinity);
        AssertAndExpect(P3_1.Add(P4_2) == P4_3);
        AssertAndExpect(P3_1.Add(P4_3) == P2_1);
        // (3,4)
        AssertAndExpect(P3_4.Add(Infinity) == P3_4);
        AssertAndExpect(P3_4.Add(P0_1) == P3_1);
        AssertAndExpect(P3_4.Add(P0_4) == P2_1);
        AssertAndExpect(P3_4.Add(P2_1) == P4_3);
        AssertAndExpect(P3_4.Add(P2_4) == P0_1);
        AssertAndExpect(P3_4.Add(P3_1) == Infinity);
        AssertAndExpect(P3_4.Add(P3_4) == P0_4);
        AssertAndExpect(P3_4.Add(P4_2) == P2_4);
        AssertAndExpect(P3_4.Add(P4_3) == P4_2);
        // (4,2)
        AssertAndExpect(P4_2.Add(Infinity) == P4_2);
        AssertAndExpect(P4_2.Add(P0_1) == P2_1);
        AssertAndExpect(P4_2.Add(P0_4) == P0_1);
        AssertAndExpect(P4_2.Add(P2_1) == P3_1);
        AssertAndExpect(P4_2.Add(P2_4) == P0_4);
        AssertAndExpect(P4_2.Add(P3_1) == P4_3);
        AssertAndExpect(P4_2.Add(P3_4) == P2_4);
        AssertAndExpect(P4_2.Add(P4_2) == P3_4);
        AssertAndExpect(P4_2.Add(P4_3) == Infinity);
        // (4,3)
        AssertAndExpect(P4_3.Add(Infinity) == P4_3);
        AssertAndExpect(P4_3.Add(P0_1) == P0_4);
        AssertAndExpect(P4_3.Add(P0_4) == P2_4);
        AssertAndExpect(P4_3.Add(P2_1) == P0_1);
        AssertAndExpect(P4_3.Add(P2_4) == P3_4);
        AssertAndExpect(P4_3.Add(P3_1) == P2_1);
        AssertAndExpect(P4_3.Add(P3_4) == P4_2);
        AssertAndExpect(P4_3.Add(P4_2) == Infinity);
        AssertAndExpect(P4_3.Add(P4_3) == P3_1);
    }

    method {:test} test_mul() {
        // (0,1)
        AssertAndExpect(P0_1.Mul(0) == Infinity);
        AssertAndExpect(P0_1.Mul(1) == P0_1);
        AssertAndExpect(P0_1.Mul(2) == P4_2);
        AssertAndExpect(P0_1.Mul(3) == P2_1);
        AssertAndExpect(P0_1.Mul(4) == P3_4);
        AssertAndExpect(P0_1.Mul(5) == P3_1);
        AssertAndExpect(P0_1.Mul(6) == P2_4);
        AssertAndExpect(P0_1.Mul(7) == P4_3);
        AssertAndExpect(P0_1.Mul(8) == P0_4);
        // (0,4)
        AssertAndExpect(P0_4.Mul(0) == Infinity);
        AssertAndExpect(P0_4.Mul(1) == P0_4);
        AssertAndExpect(P0_4.Mul(2) == P4_3);
        AssertAndExpect(P0_4.Mul(3) == P2_4);
        AssertAndExpect(P0_4.Mul(4) == P3_1);
        AssertAndExpect(P0_4.Mul(5) == P3_4);
        AssertAndExpect(P0_4.Mul(6) == P2_1);
        AssertAndExpect(P0_4.Mul(7) == P4_2);
        AssertAndExpect(P0_4.Mul(8) == P0_1);
        // (2,1)
        AssertAndExpect(P2_1.Mul(0) == Infinity);
        AssertAndExpect(P2_1.Mul(1) == P2_1);
        AssertAndExpect(P2_1.Mul(2) == P2_4);
        AssertAndExpect(P2_1.Mul(3) == Infinity);
        AssertAndExpect(P2_1.Mul(4) == P2_1);
        AssertAndExpect(P2_1.Mul(5) == P2_4);
        AssertAndExpect(P2_1.Mul(6) == Infinity);
        AssertAndExpect(P2_1.Mul(7) == P2_1);
        AssertAndExpect(P2_1.Mul(8) == P2_4);
        // (2,4)
        AssertAndExpect(P2_4.Mul(0) == Infinity);
        AssertAndExpect(P2_4.Mul(1) == P2_4);
        AssertAndExpect(P2_4.Mul(2) == P2_1);
        AssertAndExpect(P2_4.Mul(3) == Infinity);
        AssertAndExpect(P2_4.Mul(4) == P2_4);
        AssertAndExpect(P2_4.Mul(5) == P2_1);
        AssertAndExpect(P2_4.Mul(6) == Infinity);
        AssertAndExpect(P2_4.Mul(7) == P2_4);
        AssertAndExpect(P2_4.Mul(8) == P2_1);
        // (3,1)
        AssertAndExpect(P3_1.Mul(0) == Infinity);
        AssertAndExpect(P3_1.Mul(1) == P3_1);
        AssertAndExpect(P3_1.Mul(2) == P0_1);
        AssertAndExpect(P3_1.Mul(3) == P2_4);
        AssertAndExpect(P3_1.Mul(4) == P4_2);
        AssertAndExpect(P3_1.Mul(5) == P4_3);
        AssertAndExpect(P3_1.Mul(6) == P2_1);
        AssertAndExpect(P3_1.Mul(7) == P0_4);
        AssertAndExpect(P3_1.Mul(8) == P3_4);
        // (3,4)
        AssertAndExpect(P3_4.Mul(0) == Infinity);
        AssertAndExpect(P3_4.Mul(1) == P3_4);
        AssertAndExpect(P3_4.Mul(2) == P0_4);
        AssertAndExpect(P3_4.Mul(3) == P2_1);
        AssertAndExpect(P3_4.Mul(4) == P4_3);
        AssertAndExpect(P3_4.Mul(5) == P4_2);
        AssertAndExpect(P3_4.Mul(6) == P2_4);
        AssertAndExpect(P3_4.Mul(7) == P0_1);
        AssertAndExpect(P3_4.Mul(8) == P3_1);
        // (4,2)
        AssertAndExpect(P4_2.Mul(0) == Infinity);
        AssertAndExpect(P4_2.Mul(1) == P4_2);
        AssertAndExpect(P4_2.Mul(2) == P3_4);
        AssertAndExpect(P4_2.Mul(3) == P2_4);
        AssertAndExpect(P4_2.Mul(4) == P0_4);
        AssertAndExpect(P4_2.Mul(5) == P0_1);
        AssertAndExpect(P4_2.Mul(6) == P2_1);
        AssertAndExpect(P4_2.Mul(7) == P3_1);
        AssertAndExpect(P4_2.Mul(8) == P4_3);
        // (4,3)
        AssertAndExpect(P4_3.Mul(0) == Infinity);
        AssertAndExpect(P4_3.Mul(1) == P4_3);
        AssertAndExpect(P4_3.Mul(2) == P3_1);
        AssertAndExpect(P4_3.Mul(3) == P2_1);
        AssertAndExpect(P4_3.Mul(4) == P0_1);
        AssertAndExpect(P4_3.Mul(5) == P0_4);
        AssertAndExpect(P4_3.Mul(6) == P2_4);
        AssertAndExpect(P4_3.Mul(7) == P3_4);
        AssertAndExpect(P4_3.Mul(8) == P4_2);
    }

    lemma {:verify false} LemmaMulScalar(p:Point, n:nat)
    ensures p.Mul(n) == p.Mul(n%9)
    decreases n
    {
        // NOTE: I belive that this is true, though I did not manage to prove it
        // yet.  Observe that (n%2) != (n%9)%2.  For example, 9%2 == 1, whilst
        // 9%9%2 == 0%2 == 0.
    }
}
