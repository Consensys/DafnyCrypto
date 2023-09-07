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
    // Defines the type of a Merkle proof.
    type Proof<T> = p:(seq<bool>,seq<T>) | |p.0| + 1 == |p.1|
    // This isn't a "possibly empty type", but cannot otherwise show dafny.
    witness *

    // Compute the Merkle root for a given blob of data.  If the data is a
    // single element, then that is returned.  Otherwise, the blob is divided
    // evenly and the hash of each sub root computed:
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

    // Generate a proof of inclusion for the value at a given index in a blob
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
    // Thus, the proof is ([true,false],[Y,D,C]), where Y=Hash(A,B).  Note that
    // [true,false] is the path through the tree, where false (resp. true)
    // signals the left (resp. right) branch is taken.
    function Generate<T(==)>(data: seq<T>, i: nat, hash: (T,T)->T) : (p:Proof<T>)
    // Cannot generate proofs for empty vectors.
    requires |data| > 0 && i < |data|
    // Last element of proof is ith element of vector.
    ensures var last := |p.0|; data[i] == p.1[last]
    {
        var pivot := |data| / 2;
        if |data| == 1 then ([],data)
        else if i < pivot then
            var lhs := Generate(data[..pivot],i,hash);
            var rhs := Root(data[pivot..],hash);
            ([false] + lhs.0, [rhs] + lhs.1)
        else
            var lhs := Root(data[..pivot],hash);
            var rhs := Generate(data[pivot..],i-pivot,hash);
            ([true] + rhs.0, [lhs] + rhs.1)
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
    function Verify<T(==)>(proof: Proof<T>, hash: (T,T)->T) : T
    // Every step decreases the size of the proof by one.
    decreases |proof.0|
    {
        var hashes := proof.1;
        //
        if |hashes| == 1
        then
            // Base case, only one hash remaining.
            hashes[0]
        else
            var path := proof.0;
            // Extract subproof
            var subproof : Proof := (path[1..],hashes[1..]);
            // Compute hash for subproof
            var subhash := Verify(subproof, hash);
            // Apply path sign (left or right)
            if path[0] then hash(hashes[0],subhash)
            else hash(subhash,hashes[0])
    }

    lemma Completeness<T>(data: seq<T>, i: nat, hash: (T,T)->T)
    // Not applicable for empty vectors.
    requires |data| > 0 && i < |data|
    // Verifying the original proof produces the root.
    ensures Verify(Generate(data,i,hash), hash) == Root(data,hash)
    {
        // Apparently, Dafny can prove this automatically using its built-in
        // induction tactic.
    }
}