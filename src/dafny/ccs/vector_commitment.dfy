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

// A abstract representation of a Cryptographic Committment Scheme (CCS).
// Specifically, given a vector of messages we can: (1) generate a committment
// to it; (2) generate and/or verify a proof that an element is included in it.
abstract module VectorCommitmentScheme {
    // The type of messages held in vectors.  This must support equality
    // comparisons, and cannot be a heap reference.
    type Message(==,!new)

    // The type of a commitment in the scheme.
    type Commitment(==,!new)

    // An opening in this scheme (which corresponds to a single-element
    // inclusion proof).
    type Opening(!new)

    // Generate a committment from a given vector.
    function Commit(vec: seq<Message>) : Commitment

    // Generate a proof that a given message is included at a given index in
    // a vector.
    function Open(vec: seq<Message>, i: nat, m: Message) : Opening
    // Element in question must be at given position in vector.
    requires i < |vec| && vec[i] == m

    // Verify a given value v was included in the original blob of data (as
    // determined by the commitment) using a given inclusion proof.
    predicate Verify(c: Commitment, o: Opening, i: nat, m: Message)

    // Completeness requires that, given a valid commitment and opening for some
    // vector, we can verify the opening against the commitment.  This provides
    // one direction of proof for the commitment scheme (in fact, the easiest).
    // It simply is a sanity check that we can, in fact, always verify our
    // openings.
    lemma Completeness(vec: seq<Message>, c: Commitment, o: Opening, i: nat, m: Message)
    // Value must be in the blob
    requires i < |vec| && vec[i] == m
    // Commitment must be valid for the given blob
    requires Commit(vec) == c
    // Opening must be valid for the given blob and value.
    requires Open(vec,i,m) == o
    // Verification must always succeed
    ensures Verify(c,o,i,m)
}