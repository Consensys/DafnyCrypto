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
    type Polynomial = seq<int>

    // Represents a single term in a polynomial.  For example, 2*x^3 is (2,3).
    type Term = (int,nat)

    // Construct a polynomial of a given order n from a given term.  For
    // example, [123,0,0] represents 123 as a polynomial of order 3.  Likewise,
    // [0,2,0] represents 2*x as a polynomial of order 3.
    function Unit(t:Term, n:nat) : Polynomial
    requires n > t.1 {
        seq(n,(i:nat) => if i == t.1 then t.0 else 0)
    }

    // Evaluate a given polynomial at a given position.
    function Eval(poly: Polynomial, x: nat) : int {
        // Compute powers x^0, x^1, x^2, ...
        var powers := MathUtils.PowN(x,|poly|);
        // Multiply out coefficients
        var terms := VecMul(powers,poly);
        // Sum result
        VecSum(terms)
    }

    function {:verify false} Neg(poly: Polynomial) : (res:Polynomial)
    // Length unchanged
    ensures |res| == |poly|
    // Result is negation of original polynomial.
    ensures forall x : nat :: Eval(poly,x) == -Eval(res,x)
    {
        seq(|poly|,(i:nat) requires i < |poly| => -poly[i])
    }

    // Add two polynomials together.
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

    // Subtract one polynomial form another
    function {:verify false} Sub(left: Polynomial, right: Polynomial) : (res:Polynomial)
    // For simplicity, requires that polynomial orders match
    requires |left| == |right|
    // Resulting polynomial has matching length
    ensures |res| == |left|
    {
        VecAdd(left,Neg(right))
    }

    // Sum one or more polynomials
    function Sum(polys: seq<Polynomial>) : Polynomial
    // Cannot sum zero polynomials!
    requires |polys| > 0
    // Every polynomial in the sum has same order
    requires forall i :: 0 <= i < |polys| ==> |polys[i]| == |polys[0]| {
        if |polys| == 1 then polys[0]
        else
            Add(polys[0],Sum(polys[1..]))
    }

    // Multiply two polynomials together.
    function {:verify false} Mul(left: Polynomial, right: Polynomial) : (res:Polynomial)
    // For simplicity, requires that polynomial orders match
    ensures |res| == |left| * |right|
    // Resulting polynomial is left multiplied by right at every point.
    //ensures forall x : nat :: Eval(left,x) * Eval(right,x) == Eval(res,x)
    {
        var n := |left| * |right|;
        var rows := seq(|right|,(i:nat) => MulTerm(left,(right[i],i),n));
        Sum(rows)
    }

    // Encode a given sequence of data d into a polynomial p, such that p(i) ==
    // d[i].  This is achieved using Lagrange interpolation.
    function {:verify false} Encode(data: seq<nat>) : (p:Polynomial)
    // Ensure data encoded correctly in the result!
    ensures forall i :: 0 <= i < |data| ==> Eval(p,i) == data[i]
    {
        []
    }

    // Multiply a polynomial by a single term, producing a polynomial of a
    // specific order n.
    function MulTerm(p: Polynomial, t: Term, n:nat) : (r:Polynomial)
    requires n >= |p| + t.1
    // Resulting polynomial is of order n
    ensures |r| == n {
        var (c,m) := t;
        seq(n, (i:nat) => if i < m || (i-m) >= |p| then 0 else (c*p[i-m]))
    }
}