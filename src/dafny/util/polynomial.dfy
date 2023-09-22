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
include "galois_field.dfy"

// Algorithms for manipulating polynomials in one variable over finite fields.
abstract module Polynomial {
    // Defines the type of elements used in this polynomial.  This could be the
    // type of natural numbers, or the type of a finite field, etc.
    type Field

    // Defines the bottom element in the field.
    const ZERO : Field

    // Defines the unit element in the field.
    const ONE : Field

    // A polynomial is represented as an array of consecutive coefficients.  For
    // example, if `arr=[1,2,0]` then the polynomial described is `1*x^0 + 2*x^1
    // + 0*x^2`.
    type Polynomial = seq<Field>

    // Represents a single term in a polynomial.  For example, 2*x^3 is (2,3).
    type Term = (Field,nat)

    // Construct a polynomial of a given order n from a given term.  For
    // example, [123,0,0] represents 123 as a polynomial of order 3.  Likewise,
    // [0,2,0] represents 2*x as a polynomial of order 3.
    function Unit(t:Term, n:nat) : Polynomial
    requires n > t.1 {
        seq(n,(i:nat) => if i == t.1 then t.0 else ZERO)
    }

    // Evaluate a given polynomial at a given position.
    function Eval(poly: Polynomial, x: Field) : Field {
        if |poly| == 0 then ZERO
        else
            var r := FieldMul(x,Eval(poly[1..],x));
            FieldAdd(poly[0],r)
    }

    // ========================================================================
    // Polynomial Operations
    // ========================================================================

    function Neg(poly: Polynomial) : (res:Polynomial)
    // Length unchanged
    ensures |res| == |poly|
    {
        seq(|poly|,(i:nat) requires i < |poly| => FieldNeg(poly[i]))
    }

    // Add two polynomials together.
    function Add(left: Polynomial, right: Polynomial) : (res:Polynomial)
    // For simplicity, requires that polynomial orders match
    requires |left| == |right|
    // Resulting polynomial has matching length
    ensures |res| == |left|
    {
        seq(|left|,(i:nat) requires i < |left| => FieldAdd(left[i],right[i]))
    }

    // Subtract one polynomial form another
    function Sub(left: Polynomial, right: Polynomial) : (res:Polynomial)
    // For simplicity, requires that polynomial orders match
    requires |left| == |right|
    // Resulting polynomial has matching length
    ensures |res| == |left|
    {
        seq(|left|,(i:nat) requires i < |left| => FieldAdd(left[i],FieldNeg(right[i])))
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

    // Multiply one or more polynomials
    function Product(polys: seq<Polynomial>) : Polynomial
    // Cannot sum zero polynomials!
    requires |polys| > 0  {
        if |polys| == 1 then polys[0]
        else
            Mul(polys[0],Product(polys[1..]))
    }

    // Multiply two polynomials together.
    function {:verify false} Mul(left: Polynomial, right: Polynomial) : (res:Polynomial)
    // For simplicity, requires that polynomial orders match
    ensures |res| == (|left| + |right|) - 1
    {
        if |left| == 0 then left
        else if |right| == 0 then right
        else
            var n := (|left| + |right|) - 1;
            var rows := seq(|right|,(i:nat) requires i < |right| => MulTerm(left,(right[i],i),n));
            Sum(rows)
    }

    // ========================================================================
    // Field Operations
    // ========================================================================

    // Negate item
    function FieldNeg(n:Field) : Field

    // Add two items together
    function FieldAdd(l:Field,r:Field) : Field

    // Multiple two items together
    function FieldMul(l:Field,r:Field) : Field

    // Sum a vector
    function FieldSum(vec: seq<Field>) : Field
    {
        if |vec| == 0 then ZERO
        else
            FieldAdd(vec[0],FieldSum(vec[1..]))
    }

    // Multiply two vectors
    function FieldVecMul(left: seq<Field>, right: seq<Field>) : (res:seq<Field>)
    requires |left| == |right|
    {
        seq(|left|,(i:nat) requires i < |left| => FieldMul(left[i],right[i]))
    }

    // ========================================================================
    // Misc helpers
    // ========================================================================

    // Multiply a polynomial by a single term, producing a polynomial of a
    // specific order n.
    function MulTerm(p: Polynomial, t: Term, n:nat) : (r:Polynomial)
    requires n >= |p| + t.1
    // Resulting polynomial is of order n
    ensures |r| == n {
        var (c,m) := t;
        seq(n, (i:nat) => if i < m || (i-m) >= |p| then ZERO else (FieldMul(c,p[i-m])))
    }
}

// ============================================================================
// Concrete Instances
// ============================================================================

// An invertible polynomial is a polynomial where every field value has a unique
// inverse.  This allows the Lagrange interpolating polynomial to be constructed.
abstract module InvertiblePolynomial refines Polynomial {

    // Compute the lagrange interpolating polynomial.
    function {:verify false} Interpolate(xs: seq<Field>, ys: seq<Field>) : Polynomial
    // Cannot interpolate with less than two elements
    requires |xs| > 1
    // Must have same number of x/y positions.
    requires |xs| == |ys| {
        var n := |xs|;
        var cols := seq(n,(i:nat) requires i < n => Mul(Unit((ys[i],0),1),LagrangeBasis(i,xs)));
        Sum(cols)
    }

    // ========================================================================
    // Field Operations
    // ========================================================================

    // Compute 1/n
    function FieldInv(n:Field) : (r:Field)

    // ========================================================================
    // Misc helpers
    // ========================================================================

    function LagrangeBasis(j: nat, xs: seq<Field>) : (p:Polynomial)
    requires j < |xs| && |xs| > 1 {
        var ls := seq(|xs|-1, (m:nat) requires m < |xs|-1 => LagrangeBasisIth(j,m,xs));
        Product(ls)
    }

    function LagrangeBasisIth(j: nat, m:nat, xs: seq<Field>) : (p:Polynomial)
    requires j < |xs|
    requires m < |xs|-1 {
        var x_m := if m < j then xs[m] else xs[m+1];
        var nx_m := FieldNeg(x_m); // -x_m
        var x_i := xs[j];
        // x - x_m
        var num := [nx_m,ONE];
        // 1 / (x_j - x_m)
        var den := [FieldInv(FieldAdd(x_i,nx_m))];
        //
        Mul(num,den)
    }
}

// Polynomials with integer coefficients.
module IntPolynomial refines Polynomial {
    import MathUtils
    type Field = int

    const ZERO : Field := 0
    const ONE : Field := 1

    function FieldNeg(n:Field) : Field { -n }

    // Add two items together
    function FieldAdd(l:Field,r:Field) : Field { l+r }

    // Multiple two items together
    function FieldMul(l:Field,r:Field) : Field { l*r }
}

abstract module PrimePolynomial refines InvertiblePolynomial {
    // Import abstract notion of a field.
    import GF : PrimeField

    // Define polynomial coefficients to be over finite field elements.
    type Field = GF.Element
    // Define notion of "zero", where x*0 = 0 for any x.
    const ZERO : Field := GF.Element.Value(0)
    // Define notion of "one", where x*1 = 1 for any x.
    const ONE : Field := GF.Element.Value(1)

    function FieldNeg(n:Field) : Field {
        ZERO.Sub(n)
    }

    // Add two items together
    function FieldAdd(l:Field,r:Field) : Field { l.Add(r) }

    // Multiple two items together
    function FieldMul(l:Field,r:Field) : Field { l.Mul(r) }

    // Compute 1/n
    function FieldInv(n:Field) : Field {
        // FIXME: is this safe?
        if n.n == 0 then ZERO
        else
            n.Inverse()
    }
}

// Example prime polynomials
module Gf5Polynomial refines PrimePolynomial { import GF = GF5 }
module Gf251Polynomial refines PrimePolynomial { import GF = GF251 }