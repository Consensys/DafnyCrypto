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
include "math.dfy"
include "polynomial.dfy"

module Lagrange {
    import opened MathUtils
    import opened Polynomial

    // Give an array of coefficients x_i, computes the product x - x_i (as a
    // polynomial).
    function l_x(xs: seq<int>) : (r:Polynomial)
    requires 0 < |xs| {
        var x := Unit((1,1),2);
        var xm := Unit((xs[0],0),2);
        // x - x_m
        var r := Sub(x,xm);
        //
        if |xs| == 1 then r
        else
            Mul(r,l_x(xs[1..]))
    }

    function l_num(j: nat, xs: seq<int>, m: nat) : Polynomial
    requires m <= |xs| && j < |xs|
    decreases |xs| - m {
        if m >= |xs| then [1]
        else if j == m then l_num(j,xs,m+1)
        else
            var x := Unit((1,1),2);
            var xm := Unit((xs[m],0),2);
            // x - x_m
            var r := Sub(x,xm);
            Mul(r,l_num(j,xs,m+1))
    }

    // Compute the Barycentric Weight for the given positions.  Observe that
    // the actual weight is one over this number.
    function Weight(j: nat, xs: seq<int>, m: nat := 0) : int
    requires m <= |xs| && j < |xs|
    decreases |xs| - m
    {
        // Base case
        if m >= |xs| then 1
        // Recursive case
        else if j != m then
            (xs[j] - xs[m]) * Weight(j,xs,m+1)
        else
            Weight(j,xs,m+1)
    }

    // Evaluate the Lagrange polynomial at a given point.  This is really just a
    // test function for now.
    function {:verify false} L(x: nat, xs: seq<int>, ys: seq<int>) : int
    requires |xs| == |ys| {
        var l_xs := seq(|xs|,(i:nat) => (ys[i] * Eval(l_num(i,xs,0),x) / Weight(i,xs)));
        VecSum(l_xs)
    }

    // Simple proof relating the size of the polynomial arising from the
    // Lagrange interpolating formula
    lemma LemmaLagrangeOrder(xs: seq<int>)
    requires |xs| > 0
    ensures |l_x(xs)| == Pow(2,|xs|)
    {
        if |xs| == 1 {
            assert Pow(2,1) == 2;
        } else {
            var x := Unit((1,1),2);
            var xm := Unit((xs[0],0),2);
            var r := Sub(x,xm);
            assert |r| == 2;
            // Unfold l_x
            assert l_x(xs) == Mul(r,l_x(xs[1..]));
            // Unfold Mul (with respect to size)
            assert |l_x(xs)| == 2 * |l_x(xs[1..])|;
            // Unfold Pow
            LemmaPow(2,|xs|);
            // Induction
            LemmaLagrangeOrder(xs[1..]);
        }
    }

    method {:test} test() {
        var xs := [0,1,2,3];
        var ys := [8,1,6,4];
        print L(0,xs,ys);
        print "\n";
        print L(1,xs,ys);
        print "\n";
        print L(2,xs,ys);
        print "\n";
        print L(3,xs,ys);
        print "\n";
    }
}