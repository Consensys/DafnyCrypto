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
include "../dafny/util/merkle.dfy"

// A very simple Merkle Tree implementation over byte blobs which uses exclusive
// or as the hash.
module ByteMerkle {
    import opened Utils
    import Merkle

    // In our scheme, messages and hashes are bytes.
    type byte = n:nat | n < 256

    // A very simple (and definitely not cryptographically strong) hash
    // function.
    function Hash(lhs: byte, rhs: byte) : byte {
        var l8 := lhs as bv8;
        var r8 := rhs as bv8;
        (l8 ^ r8) as byte
    }

    function Root(bytes: seq<byte>) : byte
    requires |bytes| > 0 {
        Merkle.Root(bytes,Hash)
    }

    function Proof(bytes: seq<byte>, i:nat) : seq<byte>
    requires |bytes| > 0 && i < |bytes| {
        Merkle.Proof(bytes,i,Hash)
    }

    function Verify(proof: seq<byte>) : byte
    requires |proof| > 0 {
        Merkle.Verify(proof,Hash)
    }

    method {:test} test_root() {
        AssertAndExpect(Root([0]) == 0);
        AssertAndExpect(Root([0,0]) == 0);
        AssertAndExpect(Root([1,0]) == 1);
        AssertAndExpect(Root([5,1]) == 4);
        AssertAndExpect(Root([7,2]) == 5);
        AssertAndExpect(Root([1,255]) == 254);
        AssertAndExpect(Root([2,1,0]) == 3);
        assert Merkle.Root([7,2,1,0],Hash) == Hash(Hash(7,2),Hash(1,0));
        AssertAndExpect(Root([7,2,1,0]) == 4);
    }

    method {:test} test_verify() {
        AssertAndExpect(Verify([0]) == 0);
        AssertAndExpect(Verify([1,0]) == 1);
        assert Merkle.Verify([2,1,0],Hash) == Hash(2,Hash(1,0));
        AssertAndExpect(Verify([2,1,0]) == 3);
        // Proof that either 1 or 0 is in [7,2,1,0]
        assert Merkle.Verify([5,1,0],Hash) == Hash(5,Hash(1,0));
        AssertAndExpect(Verify([5,1,0]) == 4);
    }

    method {:test} test_proof() {
        // n = 1
        AssertAndExpect(Proof([0],0) == [0]);
        // n = 2
        AssertAndExpect(Proof([0,1],0) == [0,1]);
        AssertAndExpect(Proof([0,1],1) == [0,1]);
        // n = 3
        assert Merkle.Proof([0,1,2],0,Hash) == Merkle.Proof([0],0,Hash) + [Merkle.Root([1,2],Hash)];
        AssertAndExpect(Proof([0,1,2],0) == [0,3]);
        AssertAndExpect(Proof([0,1,2],1) == [0,1,2]);
        AssertAndExpect(Proof([0,1,2],2) == [0,1,2]);
        // n = 4
        assert Merkle.Proof([0,1,2,3],0,Hash) == Merkle.Proof([0,1],0,Hash) + [Merkle.Root([2,3],Hash)];
        AssertAndExpect(Proof([0,1,2,3],0) == [0,1,1]);
        assert Merkle.Proof([0,1,2,3],1,Hash) == Merkle.Proof([0,1],0,Hash) + [Merkle.Root([2,3],Hash)];
        AssertAndExpect(Proof([0,1,2,3],1) == [0,1,1]);
        AssertAndExpect(Proof([0,1,2,3],2) == [1,2,3]);
        AssertAndExpect(Proof([0,1,2,3],3) == [1,2,3]);
    }
}