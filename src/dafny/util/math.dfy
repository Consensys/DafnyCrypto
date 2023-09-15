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
include "option.dfy"

module MathUtils {
    import opened Optional

    // Compute absolute value
    function Abs(x: int) : nat {
        if x >= 0 then x else -x
    }

    // Sum a vector
    function VecSum(vec: seq<int>) : int
    {
        if |vec| == 0 then 0
        else
            vec[0] + VecSum(vec[1..])
    }

    // Multiply two vectors
    function VecMul(left: seq<int>, right: seq<int>) : (res:seq<int>)
    requires |left| == |right|
    ensures |res| == |left|
    ensures forall k :: 0 <= k < |left| ==> res[k] == (left[k] * right[k])
    {
        if |left| == 0 then []
        else
            [left[0] * right[0]] + VecMul(left[1..],right[1..])
    }

    // Add two vectors
    function VecAdd(left: seq<int>, right: seq<int>) : (res:seq<int>)
    requires |left| == |right|
    ensures |res| == |left|
    ensures forall k :: 0 <= k < |left| ==> res[k] == (left[k] + right[k])
    {
        if |left| == 0 then []
        else
            [left[0] + right[0]] + VecAdd(left[1..],right[1..])
    }


    // =========================================================
    // Exponent
    // =========================================================

    /**
     * Compute n^k.
     */
    function Pow(n:nat, k:nat) : (r:nat)
    // Following needed for some proofs
    ensures n > 0 ==> r > 0 {
        if k == 0 then 1
        else if k == 1 then n
        else
            var p := k / 2;
            var np := Pow(n,p);
            if p*2 == k then np * np
            else
                np * np * n
    }

    // Simple lemma about POW.
    lemma lemma_pow2(k:nat)
    ensures Pow(2,k) > 0 {
        if k == 0 {
            assert Pow(2,k) == 1;
        } else if k == 1 {
            assert Pow(2,k) == 2;
        } else {
            lemma_pow2(k/2);
        }
    }

    // Another simple lemma about pow.
    lemma {:verify false} LemmaPow(n: nat, m:nat)
    requires m > 1
    ensures Pow(n,m) == n * Pow(n,m-1) {
        // FIXME: prove this!
    }

    // Calculate sequence [x^0, x^1, x^2, .. x^(n-1)].
    function PowN(x: nat, n:nat) : (pwrs:seq<nat>)
    ensures |pwrs| == n {
        seq(n,(i:nat) => Pow(x,i))
    }

    /**
     * Compute n^k % m.  This is more efficient that doing Pow(n,k) % m.  In
     * essence, this works by recursive decomposing the work and squaring the
     * results.
     */
    function ModPow(n:nat, k:nat, m:nat) : (r:nat)
    requires m > 0
    ensures r < m
    ensures n > 0 ==> r >= 0
    decreases k {
        var nm := n % m;
        if k == 0 || m == 1 then 1%m
        else if k == 1 then nm
        else
            var np := ModPow(nm,k/2,m);
            var np2 := (np * np) % m;
            if (k%2) == 0 then
                // Even case.  n^2k = n^k * n^k
                np2
            else
                // Odd case.  n^2k+1 = n^2k * n
                (np2 * nm) % m
    }

    // Euclid's extended GCD algorithm, implemented recursively.
    function GcdExtended(a: nat, b: nat) : (r:(nat,int,int))
    // Conditions under which gcd is non-zero
    ensures b > 0 ==> r.0 > 0
    // Bezout's identity
    ensures (a*r.1)+(b*r.2) == r.0 {
        if a == 0 then (b,0,1)
        else
            var (g,x,y) := GcdExtended(b%a,a);
            (g,y-((b/a)*x),x)
    }

    /// Determine multiplicative inverse of an element a under mod n.
    function Inverse(a: nat, n: nat) : (r:Option<nat>)
    requires a < n
    ensures r != None ==> r.Unwrap() < n
    {
        var (gcd,x,y) := GcdExtended(a,n);
        // Following property is known to hold for Euclid's extended
        // algorithm.  Unfortunately, I did not yet figure out how to get
        // Dafny to prove this for us.
        assume {:axiom} Abs(x) < n;
        //
        if gcd > 1 then None
        else if x >= 0 then Some(x)
        else
            // Done
            Some(x+n)
    }

    // A prime number is a natural greater than 1 that is not divisible by any
    // smaller number (except 1).
    predicate IsPrime(n: nat) {
        n > 1 && forall a :: 1 <= a < n ==> GcdExtended(a,n).0 == 1
    }

    // Every element in a prime field has a multiplicative inverse.
    lemma PrimeFieldsHaveInverse(a:nat, n: nat)
    requires IsPrime(n)
    requires 1 <= a < n
    ensures Inverse(a,n) != None {
        assert GcdExtended(a,n).0 == 1;
    }
}