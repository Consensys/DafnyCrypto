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
// Specifically, given a blob of data we can: (1) generate a committment to it;
// (2) generate and/or verify a proof that an element is included in it.
module CommitmentScheme {
    // The type of data held in blobs.  This must support equality comparisons,
    // and cannot be a heap reference.
    type Word(==,!new)

    // The type of a commitment in the scheme.
    type Commitment(==,!new)

    // The type of single-element inclusion proofs in the scheme.
    type InclusionProof

    // Generate a committment from a given blob of data.
    function Commit(blob: seq<Word>) : Commitment

    // Generate a proof that a given element is included in a given data blob.
    function Generate(blob: seq<Word>, element: Word) : InclusionProof
    // Obviously, the element in question must be in the blob!
    requires element in blob

    // Verify a given value v was included in the original blob of data (as
    // determined by the commitment) using a given inclusion proof.
    predicate Verify(c: Commitment, p: InclusionProof, v: Word)
}