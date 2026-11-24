/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Ring homomorphisms from characteristic `p` into a quotient ring

If some ring of characteristic `p` maps to `R ⧸ I`, then `p` vanishes in `R ⧸ I`, that is,
`(p : R) ∈ I` (`Ideal.natCast_mem_of_ringHom_charP`). Mathlib's
`Ideal.natCast_mem_of_charP_quotient` is the case of the identity of `R ⧸ I`; unlike it, the
statement here does not need `R ⧸ I` to have characteristic exactly `p`, so it also covers
`I = ⊤`.
-/

public section

/-- If a ring of characteristic `p` maps to `R ⧸ I`, then `p ∈ I`. -/
theorem Ideal.natCast_mem_of_ringHom_charP (p : ℕ) {S R : Type*} [NonAssocSemiring S] [CharP S p]
    [Ring R] {I : Ideal R} [I.IsTwoSided] (f : S →+* R ⧸ I) : (p : R) ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem.mp <| by
    rw [map_natCast, ← map_natCast f, CharP.cast_eq_zero, map_zero]
