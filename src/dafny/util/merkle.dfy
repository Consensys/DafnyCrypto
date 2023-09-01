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

// Contains relevant algorithms for manipulating merkle roots, proofs and trees.
module Merkle {
    // Compute the Merkle root for a given blob of data.  If the data is a
    // single element, then that is returned.  Otherwise, the blob is divided
    // evenly and the has of each sub root computed:
    //
    //  0 1 2 3 4 5 6 7 8 9 A B
    // +-+-+-+-+-+-+-+-+-+-+-+-+
    // | | | | | | | | | | | | |
    // +-+-+-+-+-+-+-+-+-+-+-+-+
    // | region 1  | region 2  |
    //  \         / \         /
    //   \       /   \       /
    //    root 1      root 2
    //       \          /
    //        \        /
    //           root
    //
    function Root<T(==)>(data: seq<T>, hash: (T,T)->T) : T
    // Cannot generate commitments for empty vectors.
    requires |data| > 0 {
        if |data| == 1 then data[0]
        else
            var pivot := |data| / 2;
            hash(Root(data[..pivot],hash),Root(data[pivot..],hash))
    }

    // Construct a proof of inclusion for the value at a given index in a blob
    // of data.  This corresponds to a path through the Merkle Tree from the
    // root to the given item.  For example, the proof that C is at index 2 in
    // the array [A,B,C,D] looks like:
    //
    //        X
    //       / \
    //      /   \
    //     Y     Z
    //          / \
    //         C   D
    //
    // Thus, the proof is [Y,C,D], where Y=Hash(A,B).
    function Proof<T(==)>(data: seq<T>, i: nat, hash: (T,T)->T) : (p:seq<T>)
    // Cannot generate proofs for empty vectors.
    requires |data| > 0 && i < |data|
    // A proof always contains at least one element!
    ensures |p| > 0 {
        var pivot := |data| / 2;
        if |data| == 1 then data
        else if i < pivot then
            var lhs := Proof(data[..pivot],i,hash);
            var rhs := Root(data[pivot..],hash);
            lhs + [rhs]
        else
            var lhs := Root(data[..pivot],hash);
            var rhs := Proof(data[pivot..],i-pivot,hash);
            [lhs] + rhs
    }

    // Verify a proof of inclusion by calculating its corresponding root, such
    // that it can be checked against another committment.  The proof
    // corresponds to the _path_ from the element in question to the root of the
    // tree.  Consider this example tree:
    //
    //        X
    //       / \
    //      /   \
    //     Y     Z
    //    / \   / \
    //   A   B C   D
    //
    // The original blob was [A,B,C,D] and X, Y and Z are internal hashes with X
    // being the Merkle root.  Then, a proof that C was in the original blob
    // data is [Y,C,D].
    function Verify<T(==)>(proof: seq<T>, hash: (T,T)->T) : T
    // A proof must contain at least one element!
    requires |proof| > 0
    // Every step decreases the size of the proof by one.
    decreases |proof|
    {
        if |proof| == 1 then proof[0]
        else
            var m := |proof| - 2;
            var n := |proof| - 1;
            var acc := hash(proof[m],proof[n]);
            Verify(proof[..m]+[acc], hash)
    }
}