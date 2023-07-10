/*
 * Copyright 2022 ConsenSys Software Inc.
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
include "../util/finite_field.dfy"

// An elliptic curve where y^2 == x^3 + Ax + B
module EllipticCurve refines FiniteField {
    import opened Optional
    // Define the so-called "point at infinity"
    const INFINITY : (Element,Element) := (Value(0),Value(0))
    // Parameter defining the curve
    const A : Element;
    // Paramter defining the curve
    const B : Element;
    // Equation defining this particular elliptic curve.
    function Curve(x:Element,y:Element) : bool {
        // y^2 == x^3 + A.x + B
        y.Pow(2) == x.Pow(3).Add(A.Mul(x)).Add(B)
    }
    // A point on the curve is either INFINITY or a valid point on the curve.
    type Point = p:(Element,Element) | p == INFINITY || Curve(p.0,p.1) witness INFINITY

    // Add two points on the curve together producing another point on the curve.
    function PointAdd(p: Point, q: Point) : (r:Point)
    requires N > 3 && IsPrime(N)
    {
        var x_p := p.0;
        var x_q := q.0;
        var y_p := p.1;
        var y_q := q.1;
        //
        if p == INFINITY then q
        else if q == INFINITY then p
        else if p == q then Double(p)
        else
            var x_diff := x_q.Sub(x_p);
            if x_diff == Value(0) then INFINITY
            else
                var y_diff := y_q.Sub(y_p);
                var lam := y_diff.Div(x_diff);
                var x_r := lam.Pow(2).Sub(x_p).Sub(x_q);
                var y_r := lam.Mul(x_p.Sub(x_r)).Sub(y_p);
                // FIXME: Dafny cannot prove this?
                if Curve(x_r,y_r)
                then
                    (x_r,y_r)
                else
                    INFINITY
    }

    function Double(p:Point) : (r:Point)
    requires N > 3 && IsPrime(N)
    requires p != INFINITY {
        var x := p.0;
        var y := p.1;
        var top := x.Pow(2).Mul(Value(3)).Add(A);
        var bottom := y.Mul(Value(2));
        // Is this guaranteed not to hold?
        if bottom == Value(0) then INFINITY
        else
            var lam := top.Div(bottom);
            var x_r := lam.Pow(2).Sub(x).Sub(x);
            var y_r := lam.Mul(x.Sub(x_r)).Sub(y);
            // FIXME: Dafny cannot prove this?
            if Curve(x_r,y_r)
            then
                var rp : Point := (x_r,y_r);
                rp
            else
                INFINITY
    }

    // Multiply a point by a given factor on the curve.
    function PointMul(p: Point, n: u256) : (r:Point)
    requires N > 3 && IsPrime(N)
    decreases n
    {
        if n == 0 then INFINITY
        else
            var res := PointMul(PointAdd(p,p),n / 2);
            if n % 2 == 1 then PointAdd(res,p)
            else res
    }
}