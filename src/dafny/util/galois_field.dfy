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
include "../util/option.dfy"
include "../util/math.dfy"

// Represents a finite field of a given order N.
module GaloisField {
    import opened MathUtils

    type pospos = n:nat | n > 1 witness 2

    // The number of elements in the given field.
    const N : pospos

    // Define the raw set of field elements.
    type Field = n:nat | n < N

    // Construct a field element from a nat.
    function From(n:nat) : Element
    requires n < N {
        Element.Value(n)
    }

    // A specific element in the field.
    datatype Element = Value(n:Field) {
        // Add two elements from the field together.
        function Add(rhs: Element) : Element {
            Value((this.n + rhs.n) % N)
        }
        // Subtract one element from another.
        function Sub(rhs: Element) : Element {
            Value((this.n - rhs.n) % N)
        }
        // Multiply two elements together.
        function Mul(rhs: Element) : Element {
            Value((this.n * rhs.n) % N)
        }
        // Divide one element into another.
        function Div(rhs: Element) : Element
        requires IsPrime(N) {
            if rhs.n == 0 then Value(0)
            else
                this.Mul(rhs.Inverse())
        }
        // Compute the multiplicative inverse of the given element.  This always
        // exists when N is a prime.
        function Inverse() : Element
        // Inverse exists for prime fields.
        requires IsPrime(N)
        // Zero does not have an inverse.
        requires this.n != 0 {
            var n := this.n;
            assert n < N;
            PrimeFieldsHaveInverse(n,N);
            var inverse := MathUtils.Inverse(n,N).Unwrap();
            Value(inverse)
        }

        // Raise field element to a given power (mod N).
        function Pow(n: nat) : Element {
            Value(ModPow(this.n,n,N))
        }
    }
}

abstract module PrimeField refines GaloisField {
    type prime = n:nat | IsPrime(n) witness *
    // Define prime order
    const PN : prime
    // The number of elements in the given field.
    const N := PN
}

// Example fields, primarily useful for testing.
module GF2 refines GaloisField { const N := 2 }
module GF3 refines PrimeField { const {:verify false} PN := 3 }
module GF4 refines GaloisField { const N := 4 }
module GF5 refines PrimeField { const {:verify false} PN := 5 }
module GF251 refines PrimeField { const {:verify false} PN := 251 }