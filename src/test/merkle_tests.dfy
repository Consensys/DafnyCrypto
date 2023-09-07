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

    // A proof is over byte words
    type Proof = Merkle.Proof<byte>

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

    function Generate(bytes: seq<byte>, i:nat) : Proof
    requires |bytes| > 0 && i < |bytes| {
        Merkle.Generate(bytes,i,Hash)
    }

    function Verify(proof: Proof) : byte {
        Merkle.Verify(proof,Hash)
    }

    // ==============================================================
    // Proofs
    // ==============================================================

    // Proof that 0 is in [0]
    const PROOF_0_0 : Proof := ([],[0])
    // Proof that 0 is in [0,1]
    const PROOF_0_01 : Proof := ([false],[1,0])
    // Proof that 1 is in [0,1]
    const PROOF_1_01 : Proof := ([true],[0,1])
    // Proof that 0 is in [0,1,2]
    const PROOF_0_012 : Proof := ([false],[3,0])
    // Proof that 1 is in [0,1,2]
    const PROOF_1_012 : Proof := ([true,false],[0,2,1])
    // Proof that 2 is in [0,1,2]
    const PROOF_2_012 : Proof := ([true,true],[0,1,2])
    // Proof that 0 is in [0,1,2,3]
    const PROOF_0_0123 : Proof := ([false,false],[1,1,0])
    // Proof that 1 is in [0,1,2,3]
    const PROOF_1_0123 : Proof := ([false,true],[1,0,1])
    // Proof that 2 is in [0,1,2,3]
    const PROOF_2_0123 : Proof := ([true,false],[1,3,2])
    // Proof that 3 is in [0,1,2,3]
    const PROOF_3_0123 : Proof := ([true,true],[1,2,3])

    // ==============================================================
    // Tests
    // ==============================================================

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
        AssertAndExpect(Verify(PROOF_0_0) == 0);
        AssertAndExpect(Verify(PROOF_0_01) == 1);
        AssertAndExpect(Verify(PROOF_1_01) == 1);
        AssertAndExpect(Verify(PROOF_0_012) == 3);
        AssertAndExpect(Verify(PROOF_1_012) == 3);
    }

    // Dafny needs a lot of hand holding here :(
    method {:test} test_proof() {
        // n = 1
        AssertAndExpect(Generate([0],0) == PROOF_0_0);
        // n = 2
        assert Generate([0,1],0).0 == [false];
        assert Generate([0,1],0).1 == [1,0];
        AssertAndExpect(Generate([0,1],0) == PROOF_0_01);
        assert Generate([0,1],1).0 == [true];
        assert Generate([0,1],1).1 == [0,1];
        AssertAndExpect(Generate([0,1],1) == PROOF_1_01);
        // n = 3
        assert Root([1,2]) == 3;
        assert Generate([0,1,2],0).1 == [3,0];
        AssertAndExpect(Generate([0,1,2],0) == PROOF_0_012);
        assert Generate([0,1,2],1).0 == [true,false];
        assert Generate([0,1,2],1).1 == [0,2,1];
        AssertAndExpect(Generate([0,1,2],1) == PROOF_1_012);
        assert Generate([0,1,2],2).0 == [true,true];
        assert Generate([0,1,2],2).1 == [0,1,2];
        AssertAndExpect(Generate([0,1,2],2) == PROOF_2_012);
        // n = 4
        expect Generate([0,1,2,3],0).0 == [false,false];
        expect Generate([0,1,2,3],0).1 == [1,1,0];
        AssertAndExpect(Generate([0,1,2,3],0) == PROOF_0_0123);
        expect Generate([0,1,2,3],1).0 == [false,true];
        expect Generate([0,1,2,3],1).1 == [1,0,1];
        AssertAndExpect(Generate([0,1,2,3],1) == PROOF_1_0123);
        expect Generate([0,1,2,3],2).0 == [true,false];
        expect Generate([0,1,2,3],2).1 == [1,3,2];
        AssertAndExpect(Generate([0,1,2,3],2) == PROOF_2_0123);
        expect Generate([0,1,2,3],3).0 == [true,true];
        expect Generate([0,1,2,3],3).1 == [1,2,3];
        AssertAndExpect(Generate([0,1,2,3],3) == PROOF_3_0123);
    }
}