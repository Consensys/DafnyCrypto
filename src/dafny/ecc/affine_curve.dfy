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
include "../util/galois_field.dfy"

// The affine representation of a Short Weierstrass curve.  That is an elliptic
// curve in where y^2 == x^3 + Ax + B, for some A and B where 4A^2 + 27B^2 != 0.
module AffineCurve refines GaloisField {
    // Parameter defining the curve
    const A : Element
    // Paramter defining the curve
    const B : Element

    // Equation defining what it means for a point (other than infinity) to be
    // on the elliptic curve.
    predicate OnCurve(x:Element,y:Element) {
        // y^2 == x^3 + A.x + B
        y.Pow(2) == x.Pow(3).Add(A.Mul(x)).Add(B)
    }

    // A point on the curve is either an actual point on the curve, or the
    // special "point at infinity".
    type Point = p:RawPoint | p.Valid() witness Infinity

    // A pair of elements (which may or may not be on the curve), and the
    // special point at infinity.  This datatype is only needed because of
    // Dafny's limited syntax.
    datatype RawPoint = Pair(Element,Element) | Infinity {
        // Determines when a point is considered valid or not.  That is, when
        // its on the curve.
        predicate Valid() {this.Infinity? || (var Pair(x,y) := this; OnCurve(x,y))}

        // Add two points on the curve together producing another point on the curve.
        function Add(q: Point) : (r:Point)
        // Underlying field must have prime order
        requires N > 3 && IsPrime(N)
        // Point under addition must be on the curve.
        requires this.Valid()
        {
            if this.Infinity? then q
            else if q.Infinity? then this
            else if this == q then this.Double()
            else
                var Pair(x_p,y_p) := this;
                var Pair(x_q,y_q) := q;
                var x_diff := x_q.Sub(x_p);
                if x_diff == Value(0) then Infinity
                else
                    var y_diff := y_q.Sub(y_p);
                    var lam := y_diff.Div(x_diff);
                    var x_r := lam.Pow(2).Sub(x_p).Sub(x_q);
                    var y_r := lam.Mul(x_p.Sub(x_r)).Sub(y_p);
                    // FIXME: Dafny cannot prove this?
                    assume {:axiom} OnCurve(x_r,y_r);
                    // Done
                    Pair(x_r,y_r)
        }

        function Double() : (r:Point)
        // Underlying field must have prime order
        requires N > 3 && IsPrime(N)
        // Point must be a pair of elements on the curve.
        requires this.Valid() && this.Pair?
        {
            var Pair(x,y) := this;
            var top := x.Pow(2).Mul(Value(3)).Add(A);
            var bottom := y.Mul(Value(2));
            // Is this guaranteed not to hold?
            if bottom == Value(0) then Infinity
            else
                var lam := top.Div(bottom);
                var x_r := lam.Pow(2).Sub(x).Sub(x);
                var y_r := lam.Mul(x.Sub(x_r)).Sub(y);
                // FIXME: Dafny cannot prove this?
                assume {:axiom} OnCurve(x_r,y_r);
                // Done
                Pair(x_r,y_r)
        }

        // Multiply a point by a given factor on the curve.
        function Mul(n: nat) : (r:Point)
        // Underlying field must have prime order
        requires N > 3 && IsPrime(N)
        // Point being multiplied must be on the curve.
        requires this.Valid()
        decreases n
        {
            if n == 0 then Infinity
            else
                var res := this.Add(this).Mul(n / 2);
                if n % 2 == 1 then this.Add(res)
                else res
        }
    }

    // Straightforward check: p * 1 == p
    lemma LemmaMul1(p:Point)
    requires N > 3 && IsPrime(N)
    ensures p == p.Mul(1)
    {
    }

    // Another check: p*2 == p+p
    lemma LemmaAddMul2(p:Point)
    ensures p.Add(p) == p.Mul(2)
    requires N > 3 && IsPrime(N)
    {
    }
}