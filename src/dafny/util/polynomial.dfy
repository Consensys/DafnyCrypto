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

// Algorithms for manipulating polynomials in one variable.
module Polynomial {
    import opened MathUtils
    // A polynomial is represented as an array of consecutive coefficients.  For
    // example, if `arr=[1,2,0]` then the polynomial described is `1*x^0 + 2*x^1
    // + 0*x^2`.
    type Polynomial = seq<nat>

    // Evaluate a given polynomial at a given position.
    function Eval(poly: Polynomial, x: nat) : nat {
        // Compute powers x^0, x^1, x^2, ...
        var powers := MathUtils.PowN(x,|poly|);
        // Multiply out coefficients
        var terms := VecMul(powers,poly);
        // Sum result
        VecSum(terms)
    }

    // add two polynomials together.
    function {:verify false} Add(left: Polynomial, right: Polynomial) : (res:Polynomial)
    // For simplicity, requires that polynomial orders match
    requires |left| == |right|
    // Resulting polynomial has matching length
    ensures |res| == |left|
    // Resulting polynomial is left plus right at every point.
    ensures forall x : nat :: Eval(left,x) + Eval(right,x) == Eval(res,x)
    {
        VecAdd(left,right)
    }

    // Multiply two polynomials together.
    function {:verify false} Mul(left: Polynomial, right: Polynomial) : (res:Polynomial)
    // For simplicity, requires that polynomial orders match
    requires |left| == |right|
    // Resulting polynomial is left multiplied by right at every point.
    ensures forall x : nat :: Eval(left,x) * Eval(right,x) == Eval(res,x)
    {
        []
    }

    // Encode a given sequence of data d into a polynomial p, such that p(i) ==
    // d[i].  This is achieved using Lagrange interpolation.
    function {:verify false} Encode(data: seq<nat>) : (p:Polynomial)
    // Ensure data encoded correctly in the result!
    ensures forall i :: 0 <= i < |data| ==> Eval(p,i) == data[i]
    {
        []
    }
}