include "utils.dfy"
include "../dafny/util/galois_field.dfy"

import opened Utils

// ============================================================================
// GF2
// ============================================================================

method {:test} gf2_add() {
    AssertAndExpect(GF2.Value(0).Add(GF2.Value(0)) == GF2.Value(0));
    AssertAndExpect(GF2.Value(1).Add(GF2.Value(0)) == GF2.Value(1));
    AssertAndExpect(GF2.Value(0).Add(GF2.Value(1)) == GF2.Value(1));
    AssertAndExpect(GF2.Value(1).Add(GF2.Value(1)) == GF2.Value(0));
}

method {:test} gf2_mul() {
    AssertAndExpect(GF2.Value(0).Mul(GF2.Value(0)) == GF2.Value(0));
    AssertAndExpect(GF2.Value(0).Mul(GF2.Value(1)) == GF2.Value(0));
    AssertAndExpect(GF2.Value(0).Mul(GF2.Value(1)) == GF2.Value(0));
    AssertAndExpect(GF2.Value(1).Mul(GF2.Value(1)) == GF2.Value(1));
}

// ============================================================================
// GF3
// ============================================================================

method {:test} gf3_add() {
    AssertAndExpect(GF3.Value(0).Add(GF3.Value(0)) == GF3.Value(0));
    AssertAndExpect(GF3.Value(0).Add(GF3.Value(1)) == GF3.Value(1));
    AssertAndExpect(GF3.Value(1).Add(GF3.Value(0)) == GF3.Value(1));
    AssertAndExpect(GF3.Value(1).Add(GF3.Value(1)) == GF3.Value(2));
    AssertAndExpect(GF3.Value(1).Add(GF3.Value(2)) == GF3.Value(0));
    AssertAndExpect(GF3.Value(2).Add(GF3.Value(1)) == GF3.Value(0));
    AssertAndExpect(GF3.Value(2).Add(GF3.Value(2)) == GF3.Value(1));
}

method {:test} gf3_mul() {
    AssertAndExpect(GF3.Value(0).Mul(GF3.Value(0)) == GF3.Value(0));
    AssertAndExpect(GF3.Value(1).Mul(GF3.Value(0)) == GF3.Value(0));
    AssertAndExpect(GF3.Value(2).Mul(GF3.Value(0)) == GF3.Value(0));
    AssertAndExpect(GF3.Value(0).Mul(GF3.Value(1)) == GF3.Value(0));
    AssertAndExpect(GF3.Value(0).Mul(GF3.Value(2)) == GF3.Value(0));
    AssertAndExpect(GF3.Value(1).Mul(GF3.Value(1)) == GF3.Value(1));
    AssertAndExpect(GF3.Value(1).Mul(GF3.Value(2)) == GF3.Value(2));
    AssertAndExpect(GF3.Value(2).Mul(GF3.Value(1)) == GF3.Value(2));
    AssertAndExpect(GF3.Value(2).Mul(GF3.Value(2)) == GF3.Value(1));
}

method {:test} gf3_inverse() {
    expect Int.IsPrime(GF3.N); // Dafny cannot easily prove this
    AssertAndExpect(GF3.Value(1).Inverse() == GF3.Value(1));
    AssertAndExpect(GF3.Value(2).Inverse() == GF3.Value(2));
}

method {:test} gf3_div() {
    expect Int.IsPrime(GF3.N); // Dafny cannot easily prove this
    AssertAndExpect(GF3.Value(0).Div(GF3.Value(0)) == GF3.Value(0)); // should not exist?
    AssertAndExpect(GF3.Value(0).Div(GF3.Value(1)) == GF3.Value(0));
    AssertAndExpect(GF3.Value(0).Div(GF3.Value(2)) == GF3.Value(0));
    AssertAndExpect(GF3.Value(1).Div(GF3.Value(1)) == GF3.Value(1));
    AssertAndExpect(GF3.Value(1).Div(GF3.Value(2)) == GF3.Value(2));
    AssertAndExpect(GF3.Value(2).Div(GF3.Value(1)) == GF3.Value(2));
    AssertAndExpect(GF3.Value(2).Div(GF3.Value(2)) == GF3.Value(1));
}

// ============================================================================
// GF5
// ============================================================================

method {:test} gf5_add() {
    AssertAndExpect(GF5.Value(0).Add(GF5.Value(0)) == GF5.Value(0));
    AssertAndExpect(GF5.Value(0).Add(GF5.Value(1)) == GF5.Value(1));
    AssertAndExpect(GF5.Value(1).Add(GF5.Value(0)) == GF5.Value(1));
    AssertAndExpect(GF5.Value(1).Add(GF5.Value(1)) == GF5.Value(2));
    AssertAndExpect(GF5.Value(1).Add(GF5.Value(2)) == GF5.Value(3));
    AssertAndExpect(GF5.Value(2).Add(GF5.Value(1)) == GF5.Value(3));
    AssertAndExpect(GF5.Value(2).Add(GF5.Value(2)) == GF5.Value(4));
    AssertAndExpect(GF5.Value(2).Add(GF5.Value(3)) == GF5.Value(0));
    AssertAndExpect(GF5.Value(3).Add(GF5.Value(2)) == GF5.Value(0));
    AssertAndExpect(GF5.Value(3).Add(GF5.Value(3)) == GF5.Value(1));
    AssertAndExpect(GF5.Value(3).Add(GF5.Value(4)) == GF5.Value(2));
    AssertAndExpect(GF5.Value(4).Add(GF5.Value(3)) == GF5.Value(2));
    AssertAndExpect(GF5.Value(4).Add(GF5.Value(4)) == GF5.Value(3));
}

method {:test} gf5_mul() {
    AssertAndExpect(GF5.Value(0).Mul(GF5.Value(0)) == GF5.Value(0));
    AssertAndExpect(GF5.Value(1).Mul(GF5.Value(0)) == GF5.Value(0));
    AssertAndExpect(GF5.Value(2).Mul(GF5.Value(0)) == GF5.Value(0));
    AssertAndExpect(GF5.Value(0).Mul(GF5.Value(1)) == GF5.Value(0));
    AssertAndExpect(GF5.Value(0).Mul(GF5.Value(2)) == GF5.Value(0));
    AssertAndExpect(GF5.Value(1).Mul(GF5.Value(1)) == GF5.Value(1));
    AssertAndExpect(GF5.Value(1).Mul(GF5.Value(2)) == GF5.Value(2));
    AssertAndExpect(GF5.Value(2).Mul(GF5.Value(1)) == GF5.Value(2));
    AssertAndExpect(GF5.Value(2).Mul(GF5.Value(2)) == GF5.Value(4));
    AssertAndExpect(GF5.Value(2).Mul(GF5.Value(3)) == GF5.Value(1));
    AssertAndExpect(GF5.Value(3).Mul(GF5.Value(2)) == GF5.Value(1));
    AssertAndExpect(GF5.Value(3).Mul(GF5.Value(3)) == GF5.Value(4));
    AssertAndExpect(GF5.Value(3).Mul(GF5.Value(4)) == GF5.Value(2));
    AssertAndExpect(GF5.Value(4).Mul(GF5.Value(3)) == GF5.Value(2));
    AssertAndExpect(GF5.Value(4).Mul(GF5.Value(4)) == GF5.Value(1));
}

method {:test} gf5_inverse() {
    expect Int.IsPrime(GF5.N); // Dafny cannot easily prove this
    AssertAndExpect(GF5.Value(1).Inverse() == GF5.Value(1));
    AssertAndExpect(GF5.Value(2).Inverse() == GF5.Value(3));
    AssertAndExpect(GF5.Value(3).Inverse() == GF5.Value(2));
    AssertAndExpect(GF5.Value(4).Inverse() == GF5.Value(4));
}

method {:test} gf5_div() {
    expect Int.IsPrime(GF5.N); // Dafny cannot easily prove this
    AssertAndExpect(GF5.Value(0).Div(GF5.Value(0)) == GF5.Value(0)); // should not exist?
    AssertAndExpect(GF5.Value(0).Div(GF5.Value(1)) == GF5.Value(0));
    AssertAndExpect(GF5.Value(0).Div(GF5.Value(2)) == GF5.Value(0));
    AssertAndExpect(GF5.Value(0).Div(GF5.Value(3)) == GF5.Value(0));
    AssertAndExpect(GF5.Value(0).Div(GF5.Value(4)) == GF5.Value(0));
    AssertAndExpect(GF5.Value(1).Div(GF5.Value(1)) == GF5.Value(1));
    AssertAndExpect(GF5.Value(1).Div(GF5.Value(2)) == GF5.Value(3));
    AssertAndExpect(GF5.Value(1).Div(GF5.Value(3)) == GF5.Value(2));
    AssertAndExpect(GF5.Value(1).Div(GF5.Value(4)) == GF5.Value(4));
    AssertAndExpect(GF5.Value(2).Div(GF5.Value(1)) == GF5.Value(2));
    AssertAndExpect(GF5.Value(2).Div(GF5.Value(2)) == GF5.Value(1));
    AssertAndExpect(GF5.Value(2).Div(GF5.Value(3)) == GF5.Value(4));
    AssertAndExpect(GF5.Value(2).Div(GF5.Value(4)) == GF5.Value(3));
    AssertAndExpect(GF5.Value(3).Div(GF5.Value(1)) == GF5.Value(3));
    AssertAndExpect(GF5.Value(3).Div(GF5.Value(2)) == GF5.Value(4));
    AssertAndExpect(GF5.Value(3).Div(GF5.Value(3)) == GF5.Value(1));
    AssertAndExpect(GF5.Value(3).Div(GF5.Value(4)) == GF5.Value(2));
    AssertAndExpect(GF5.Value(4).Div(GF5.Value(1)) == GF5.Value(4));
    AssertAndExpect(GF5.Value(4).Div(GF5.Value(2)) == GF5.Value(2));
    AssertAndExpect(GF5.Value(4).Div(GF5.Value(3)) == GF5.Value(3));
    AssertAndExpect(GF5.Value(4).Div(GF5.Value(4)) == GF5.Value(1));
}