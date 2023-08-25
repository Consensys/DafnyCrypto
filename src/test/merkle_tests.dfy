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
include "../dafny/merkle/merkle.dfy"

// A very simple Merkle tree implementation using bytes as words.
module ByteMerkle refines Merkle {
    import opened Utils
    // Instantiate our Merkle system
    type Word = n:nat | n < 256

    // A very simple (and definitely not cryptographically strong) hash
    // function.
    opaque function Hash(lhs: Word, rhs: Word) : Word {
        var l8 := lhs as bv8;
        var r8 := rhs as bv8;
        (l8 ^ r8) as Word
    }

    method {:test} test_roots() {
        AssertAndExpect(Root([0]) == 0);
        AssertAndExpect(Root([0,0]) == 0);
        AssertAndExpect(Root([1,0]) == 1);
        AssertAndExpect(Root([5,1]) == 4);
        AssertAndExpect(Root([7,2]) == 5);
        AssertAndExpect(Root([1,255]) == 254);
        AssertAndExpect(Root([2,1,0]) == 3);
        assert Root([7,2,1,0]) == Root([Root([7,2]),Root([1,0])]);
        AssertAndExpect(Root([7,2,1,0]) == 4);
    }

    method {:test} test_proofs() {
        AssertAndExpect(Verify([0]) == 0);
        AssertAndExpect(Verify([1,0]) == 1);
        assert Verify([2,1,0]) == Hash(2,Hash(1,0));
        AssertAndExpect(Verify([2,1,0]) == 3);
        // Proof that either 1 or 0 is in [7,2,1,0]
        assert Verify([5,1,0]) == Hash(5,Hash(1,0));
        AssertAndExpect(Verify([5,1,0]) == 4);
    }
}