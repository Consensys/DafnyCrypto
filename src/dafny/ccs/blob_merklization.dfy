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
include "vector_commitment.dfy"
include "../util/merkle.dfy"

// An abstract vector commitment scheme which uses Merkle Tree's as the
// underlying technique.  To make a concrete scheme, one must define the type
// of messages and hashes.  However, everything else is provided (including
// proofs of correctness).
module BlobMerklization refines VectorCommitmentScheme {
    import Merkle
    // The type of a hash used in this scheme.  For example, it could be a u256
    // or something else.
    type Hash(0,==)
    // The notion of an empty hash is useful for defining witnesses, as required
    // by Dafny.  It does not have any other concrete purpose.
    const EMPTY_HASH : Hash
    // A commitment in this scheme is simply a hash (i.e. a Merkle Proof).
    type Commitment = Hash
    // An opening is a sequence of hashes which form a merkle proof.
    type Opening = s:seq<Hash> | |s| > 0 witness [EMPTY_HASH]

    // Construct a commitment by computing its Merkle root.
    function Commit(vec: seq<Message>) : Commitment {
        // Hash original vector
        var hvec := seq(|vec|, (i:nat) requires i<|vec| => Hasher(vec[i]));
        // Construct root
        Merkle.Root(hvec, HashJoin)
    }

    // Construct an opening by computing a Merkle Proof
    function Open(vec: seq<Message>, i: nat) : Opening {
        // Hash original vector
        var hvec := seq(|vec|, (i:nat) requires i<|vec| => Hasher(vec[i]));
        // Construct proof
        Merkle.Proof(hvec,i,HashJoin)
    }

    // Verify an opening using the Merkle Proof
    predicate Verify(c: Commitment, o: Opening, i: nat, m: Message) {
        i < |o| && o[i] == Hasher(m) && Merkle.Verify(o,HashJoin) == c
    }

    lemma {:verify false} Completeness(vec: seq<Message>, c: Commitment, o: Opening, i: nat, m: Message)
    {
        // FIXME: how to prove this?
    }

    // Defines the hash function used to convert messages into hashes.
    function Hasher(lhs:Message) : Hash

    // Defines the hash function used for joining hashes together.
    function HashJoin(lhs:Hash, rhs:Hash) : Hash
}