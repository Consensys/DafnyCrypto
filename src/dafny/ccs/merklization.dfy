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

module ByteMerkleCommitments refines VectorCommitmentScheme {
    import ByteMerkle

    // Instantiation commitment scheme
    type Message = ByteMerkle.Word

    // A commitment in this scheme is simply a hash.
    type Commitment = Message

    // An opening in this scheme is a merkle proof.
    type Opening = s:seq<Message> | |s| > 0
    witness [0]

    // Construct a commitment by hashing the vector.
    function Commit(vec: seq<Message>) : Commitment {
        // FIXME: does this make sense???
        if |vec| == 0 then ByteMerkle.Hash(0,0)
        else ByteMerkle.Root(vec)
    }

    function Open(vec: seq<Message>, i: nat, m: Message) : Opening {
        assert vec[i] == m; // follows from precondition of Open
        [0]
    }

    predicate Verify(c: Commitment, o: Opening, i: nat, m: Message) {
        true // haha
    }

    lemma Completeness(vec: seq<Message>, c: Commitment, o: Opening, i: nat, m: Message)
    {
        // Should be easy enough to prove :)
    }
}