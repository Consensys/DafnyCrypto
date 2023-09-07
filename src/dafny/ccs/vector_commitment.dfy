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

// A Vector Commitment Scheme is a cryptographic commitment scheme which
// operates over message vectors (i.e. ordered sequences of data messages).  A
// vector commitment can be opened at a specific position to prove that a given
// value resided at that position in the original vector.  Opening such a
// commitment should hide information about other elements in the vector
// (including how many elements there were).  Furthermore, such commitments are
// said to exhibit "positional binding" in that an adversay cannot open a
// commitment to two different values at the same position.
//
// The scheme is parameterised over the types of messages, commitments and
// openings.  Instances of this scheme must instantiate those types, and provide
// implemenentations of the three functions for commiting, opening and verifying
// commitments.  In addition, two key lemmas are provided which establish the
// required relationship between these functions.
//
// References:
//
// * "Vector Commitments and their Applications", Dario Catalano1 and Dario
//   Fiore.  In Proceedings of the conference on Practice and Theory of
//   Public-Key Cryptography (PKC), 2013.
//
// * "SoK: Vector Commitments", Anca Nitulescu, Protocol Labs.
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
    // Cannot commit to an empty vector!
    requires |vec| > 0

    // Generate an opening for a given vector.  This is a proof that a given
    // message is at a specific index in the vector.
    function Open(vec: seq<Message>, i: nat) : Opening
    // Element in question must be at given position in vector.
    requires i < |vec|

    // Verify a given value v was included in the original vector (as determined
    // by the commitment) at a specific position using a given opening.
    predicate Verify(c: Commitment, o: Opening, i: nat, m: Message)

    // Completeness requires that, given a valid commitment and opening for some
    // vector, we can verify that opening against the commitment.  This provides
    // one direction of proof for the commitment scheme (in fact, the easiest
    // direction).  In essence, this is a sanity check that we can, in fact,
    // always verify our openings.  If we could not always do this, then
    // something would certainly be amiss.
    lemma Completeness(vec: seq<Message>, c: Commitment, o: Opening, i: nat)
    // Value must be in the blob
    requires i < |vec|
    // Commitment must be valid for the given blob
    requires Commit(vec) == c
    // Opening must be valid for the given blob and value.
    requires Open(vec,i) == o
    // Verification must always succeed
    ensures Verify(c,o,i,vec[i])
}