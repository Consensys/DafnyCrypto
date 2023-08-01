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
include "../dafny/util/math.dfy"
include "utils.dfy"

module IntTests {
    import MathUtils
    import opened Optional
    import opened Utils

    const TWO_8   : int := 0x1_00
    const TWO_15  : int := 0x0_8000
    const TWO_16  : int := 0x1_0000
    const TWO_24  : int := 0x1_0000_00
    const TWO_31  : int := 0x0_8000_0000
    const TWO_32  : int := 0x1_0000_0000
    const TWO_40  : int := 0x1_0000_0000_00
    const TWO_48  : int := 0x1_0000_0000_0000
    const TWO_56  : int := 0x1_0000_0000_0000_00
    const TWO_63  : int := 0x0_8000_0000_0000_0000
    const TWO_64  : int := 0x1_0000_0000_0000_0000
    const TWO_127 : int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000
    const TWO_128 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000
    const TWO_256 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000

    // Various sanity tests for exponentiation.
    method {:test} PowTests() {
        AssertAndExpect(MathUtils.Pow(2,8) == TWO_8);
        AssertAndExpect(MathUtils.Pow(2,15) == TWO_15);
        AssertAndExpect(MathUtils.Pow(2,16) == TWO_16);
        AssertAndExpect(MathUtils.Pow(2,24) == TWO_24);
        AssertAndExpect(MathUtils.Pow(2,31) == TWO_31);
        AssertAndExpect(MathUtils.Pow(2,32) == TWO_32);
        AssertAndExpect(MathUtils.Pow(2,40) == TWO_40);
        AssertAndExpect(MathUtils.Pow(2,48) == TWO_48);
        AssertAndExpect(MathUtils.Pow(2,56) == TWO_56);
        AssertAndExpect(MathUtils.Pow(2,63) == TWO_63);
        AssertAndExpect(MathUtils.Pow(2,64) == TWO_64);
        // NOTE:  I have to break the following ones up because Z3
        // cannot handle it.
        AssertAndExpect(MathUtils.Pow(2,63) * MathUtils.Pow(2,64) == TWO_127);
        AssertAndExpect(MathUtils.Pow(2,64) * MathUtils.Pow(2,64) == TWO_128);
        AssertAndExpect(MathUtils.Pow(2,64) * MathUtils.Pow(2,64) * MathUtils.Pow(2,64) * MathUtils.Pow(2,64) == TWO_256);
        AssertAndExpect((TWO_128 / TWO_64) == TWO_64);
        AssertAndExpect((TWO_256 / TWO_128) == TWO_128);
    }

    // Various sanity tests for modulo exponentiation.
    method {:test} ModPowTests() {
        AssertAndExpect(MathUtils.ModPow(1,1,2) == 1);
        AssertAndExpect(MathUtils.ModPow(2,2,2) == 0);
        AssertAndExpect(MathUtils.ModPow(2,2,3) == 1);
        AssertAndExpect(MathUtils.ModPow(2,2,4) == 0);
        AssertAndExpect(MathUtils.ModPow(2,2,5) == 4);
        AssertAndExpect(MathUtils.ModPow(2,2,6) == 4);
        AssertAndExpect(MathUtils.ModPow(3,2,2) == 1);
        AssertAndExpect(MathUtils.ModPow(3,2,3) == 0);
        AssertAndExpect(MathUtils.ModPow(3,2,4) == 1);
        AssertAndExpect(MathUtils.ModPow(3,2,5) == 4);
        AssertAndExpect(MathUtils.ModPow(3,2,6) == 3);
        AssertAndExpect(MathUtils.ModPow(3,2,7) == 2);
        AssertAndExpect(MathUtils.ModPow(3,2,8) == 1);
        AssertAndExpect(MathUtils.ModPow(3,2,9) == 0);
        AssertAndExpect(MathUtils.ModPow(2,3,2) == 0);
        AssertAndExpect(MathUtils.ModPow(2,0,256) == 1);
        AssertAndExpect(MathUtils.ModPow(2,1,256) == 2);
        AssertAndExpect(MathUtils.ModPow(2,2,256) == 4);
        AssertAndExpect(MathUtils.ModPow(2,3,256) == 8);
        AssertAndExpect(MathUtils.ModPow(2,4,256) == 16);
        AssertAndExpect(MathUtils.ModPow(2,8,256) == 0);
        AssertAndExpect(MathUtils.ModPow(2,9,256) == 0);
        AssertAndExpect(MathUtils.ModPow(3,0,256) == 1);
        AssertAndExpect(MathUtils.ModPow(3,1,256) == 3);
        AssertAndExpect(MathUtils.ModPow(3,2,256) == 9);
        AssertAndExpect(MathUtils.ModPow(3,3,256) == 27);
        AssertAndExpect(MathUtils.ModPow(3,5,256) == 243);
        AssertAndExpect(MathUtils.ModPow(3,6,256) == 217);
    }

    // Various sanity tests for multiplicative inverse
    method {:test} InverseTests() {
        AssertAndExpect(MathUtils.Inverse(0,2) == None);
        AssertAndExpect(MathUtils.Inverse(1,2) == Some(1));
        AssertAndExpect(MathUtils.Inverse(0,3) == None);
        AssertAndExpect(MathUtils.Inverse(1,3) == Some(1));
        AssertAndExpect(MathUtils.Inverse(2,3) == Some(2));
        AssertAndExpect(MathUtils.Inverse(0,4) == None);
        AssertAndExpect(MathUtils.Inverse(1,4) == Some(1));
        AssertAndExpect(MathUtils.Inverse(2,4) == None);
        AssertAndExpect(MathUtils.Inverse(3,4) == Some(3));
        AssertAndExpect(MathUtils.Inverse(0,5) == None);
        AssertAndExpect(MathUtils.Inverse(1,5) == Some(1));
        AssertAndExpect(MathUtils.Inverse(2,5) == Some(3));
        AssertAndExpect(MathUtils.Inverse(3,5) == Some(2));
        AssertAndExpect(MathUtils.Inverse(4,5) == Some(4));
        AssertAndExpect(MathUtils.Inverse(0,6) == None);
        AssertAndExpect(MathUtils.Inverse(1,6) == Some(1));
        AssertAndExpect(MathUtils.Inverse(2,6) == None);
        AssertAndExpect(MathUtils.Inverse(3,6) == None);
        AssertAndExpect(MathUtils.Inverse(4,6) == None);
        AssertAndExpect(MathUtils.Inverse(5,6) == Some(5));
        AssertAndExpect(MathUtils.Inverse(0,7) == None);
        AssertAndExpect(MathUtils.Inverse(1,7) == Some(1));
        AssertAndExpect(MathUtils.Inverse(2,7) == Some(4));
        AssertAndExpect(MathUtils.Inverse(3,7) == Some(5));
        AssertAndExpect(MathUtils.Inverse(4,7) == Some(2));
        AssertAndExpect(MathUtils.Inverse(5,7) == Some(3));
        AssertAndExpect(MathUtils.Inverse(6,7) == Some(6));
        AssertAndExpect(MathUtils.Inverse(0,8) == None);
        AssertAndExpect(MathUtils.Inverse(1,8) == Some(1));
        AssertAndExpect(MathUtils.Inverse(2,8) == None);
        AssertAndExpect(MathUtils.Inverse(3,8) == Some(3));
        AssertAndExpect(MathUtils.Inverse(4,8) == None);
        AssertAndExpect(MathUtils.Inverse(5,8) == Some(5));
        AssertAndExpect(MathUtils.Inverse(6,8) == None);
        AssertAndExpect(MathUtils.Inverse(7,8) == Some(7));
        AssertAndExpect(MathUtils.Inverse(0,9) == None);
        AssertAndExpect(MathUtils.Inverse(1,9) == Some(1));
        AssertAndExpect(MathUtils.Inverse(2,9) == Some(5));
        AssertAndExpect(MathUtils.Inverse(3,9) == None);
        AssertAndExpect(MathUtils.Inverse(4,9) == Some(7));
        AssertAndExpect(MathUtils.Inverse(5,9) == Some(2));
        AssertAndExpect(MathUtils.Inverse(6,9) == None);
        AssertAndExpect(MathUtils.Inverse(7,9) == Some(4));
        AssertAndExpect(MathUtils.Inverse(8,9) == Some(8));
        AssertAndExpect(MathUtils.Inverse(0,10) == None);
        AssertAndExpect(MathUtils.Inverse(1,10) == Some(1));
        AssertAndExpect(MathUtils.Inverse(2,10) == None);
        AssertAndExpect(MathUtils.Inverse(3,10) == Some(7));
        AssertAndExpect(MathUtils.Inverse(4,10) == None);
        AssertAndExpect(MathUtils.Inverse(5,10) == None);
        AssertAndExpect(MathUtils.Inverse(6,10) == None);
        AssertAndExpect(MathUtils.Inverse(7,10) == Some(3));
        AssertAndExpect(MathUtils.Inverse(8,10) == None);
        AssertAndExpect(MathUtils.Inverse(9,10) == Some(9));
        AssertAndExpect(MathUtils.Inverse(0,11) == None);
        AssertAndExpect(MathUtils.Inverse(1,11) == Some(1));
        AssertAndExpect(MathUtils.Inverse(2,11) == Some(6));
        AssertAndExpect(MathUtils.Inverse(3,11) == Some(4));
        AssertAndExpect(MathUtils.Inverse(4,11) == Some(3));
        AssertAndExpect(MathUtils.Inverse(5,11) == Some(9));
        AssertAndExpect(MathUtils.Inverse(6,11) == Some(2));
        AssertAndExpect(MathUtils.Inverse(7,11) == Some(8));
        AssertAndExpect(MathUtils.Inverse(8,11) == Some(7));
        AssertAndExpect(MathUtils.Inverse(9,11) == Some(5));
        AssertAndExpect(MathUtils.Inverse(10,11) == Some(10));
        AssertAndExpect(MathUtils.Inverse(0,12) == None);
        AssertAndExpect(MathUtils.Inverse(1,12) == Some(1));
        AssertAndExpect(MathUtils.Inverse(2,12) == None);
        AssertAndExpect(MathUtils.Inverse(3,12) == None);
        AssertAndExpect(MathUtils.Inverse(4,12) == None);
        AssertAndExpect(MathUtils.Inverse(5,12) == Some(5));
        AssertAndExpect(MathUtils.Inverse(6,12) == None);
        AssertAndExpect(MathUtils.Inverse(7,12) == Some(7));
        AssertAndExpect(MathUtils.Inverse(8,12) == None);
        AssertAndExpect(MathUtils.Inverse(9,12) == None);
        AssertAndExpect(MathUtils.Inverse(10,12) == None);
        AssertAndExpect(MathUtils.Inverse(11,12) == Some(11));
        AssertAndExpect(MathUtils.Inverse(0,13) == None);
        AssertAndExpect(MathUtils.Inverse(1,13) == Some(1));
        AssertAndExpect(MathUtils.Inverse(2,13) == Some(7));
        AssertAndExpect(MathUtils.Inverse(3,13) == Some(9));
        AssertAndExpect(MathUtils.Inverse(4,13) == Some(10));
        AssertAndExpect(MathUtils.Inverse(5,13) == Some(8));
        AssertAndExpect(MathUtils.Inverse(6,13) == Some(11));
        AssertAndExpect(MathUtils.Inverse(7,13) == Some(2));
        AssertAndExpect(MathUtils.Inverse(8,13) == Some(5));
        AssertAndExpect(MathUtils.Inverse(9,13) == Some(3));
        AssertAndExpect(MathUtils.Inverse(10,13) == Some(4));
        AssertAndExpect(MathUtils.Inverse(11,13) == Some(6));
        AssertAndExpect(MathUtils.Inverse(12,13) == Some(12));
        AssertAndExpect(MathUtils.Inverse(0,14) == None);
        AssertAndExpect(MathUtils.Inverse(1,14) == Some(1));
        AssertAndExpect(MathUtils.Inverse(2,14) == None);
        AssertAndExpect(MathUtils.Inverse(3,14) == Some(5));
        AssertAndExpect(MathUtils.Inverse(4,14) == None);
        AssertAndExpect(MathUtils.Inverse(5,14) == Some(3));
        AssertAndExpect(MathUtils.Inverse(6,14) == None);
        AssertAndExpect(MathUtils.Inverse(7,14) == None);
        AssertAndExpect(MathUtils.Inverse(8,14) == None);
        AssertAndExpect(MathUtils.Inverse(9,14) == Some(11));
        AssertAndExpect(MathUtils.Inverse(10,14) == None);
        AssertAndExpect(MathUtils.Inverse(11,14) == Some(9));
        AssertAndExpect(MathUtils.Inverse(12,14) == None);
        AssertAndExpect(MathUtils.Inverse(13,14) == Some(13));
        AssertAndExpect(MathUtils.Inverse(0,15) == None);
        AssertAndExpect(MathUtils.Inverse(1,15) == Some(1));
        AssertAndExpect(MathUtils.Inverse(2,15) == Some(8));
        AssertAndExpect(MathUtils.Inverse(3,15) == None);
        AssertAndExpect(MathUtils.Inverse(4,15) == Some(4));
        AssertAndExpect(MathUtils.Inverse(5,15) == None);
        AssertAndExpect(MathUtils.Inverse(6,15) == None);
        AssertAndExpect(MathUtils.Inverse(7,15) == Some(13));
        AssertAndExpect(MathUtils.Inverse(8,15) == Some(2));
        AssertAndExpect(MathUtils.Inverse(9,15) == None);
        AssertAndExpect(MathUtils.Inverse(10,15) == None);
        AssertAndExpect(MathUtils.Inverse(11,15) == Some(11));
        AssertAndExpect(MathUtils.Inverse(12,15) == None);
        AssertAndExpect(MathUtils.Inverse(13,15) == Some(7));
        AssertAndExpect(MathUtils.Inverse(14,15) == Some(14));
    }

    method {:test} IsPrimeTests() {
        // Not an efficient mechanism for primality testing :)
        assert MathUtils.GcdExtended(1,3).0 == 1;
        assert MathUtils.IsPrime(3);
        assert MathUtils.IsPrime(5);
        assert MathUtils.IsPrime(7);
        assert MathUtils.GcdExtended(1,11).0 == 1;
        assert MathUtils.GcdExtended(2,11).0 == 1;
        assert MathUtils.GcdExtended(3,11).0 == 1;
        assert MathUtils.GcdExtended(4,11).0 == 1;
        assert MathUtils.GcdExtended(5,11).0 == 1;
        assert MathUtils.GcdExtended(6,11).0 == 1;
        assert MathUtils.GcdExtended(7,11).0 == 1;
        assert MathUtils.IsPrime(11);
    }
}
