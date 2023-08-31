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

    // Defines the hash function used for Merklisation.
    function Hash<T(==)>(lhs:T, rhs:T) : T

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
    function Root<T(==)>(data: seq<T>) : T
    requires |data| > 0 {
        if |data| == 1 then data[0]
        else
            var pivot := |data| / 2;
            Hash(Root(data[..pivot]),Root(data[pivot..]))
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
    function Verify<T(==)>(proof: seq<T>) : T
    // A proof must contain at least one element!
    requires |proof| > 0
    decreases |proof| {
        if |proof| == 1 then proof[0]
        else
            var m := |proof| - 2;
            var n := |proof| - 1;
            var acc := Hash(proof[m],proof[n]);
            Verify(proof[..m]+[acc])
    }
}