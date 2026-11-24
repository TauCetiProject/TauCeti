/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Linear independence of a pair in `R × R`

Over a domain `R`, the vectors `(1, c)` and `v` of `R × R` are linearly independent exactly when
the determinant `v.2 - c * v.1` is nonzero (`TauCeti.linearIndependent_pair_mk_one_iff`).
-/

public section

namespace TauCeti

/-- Over a domain `R`, the vectors `(1, c)` and `v` of `R × R` are linearly independent exactly
when the determinant `v.2 - c * v.1` is nonzero: the case of
`LinearIndependent.pair_add_smul_add_smul_iff` for the standard basis. -/
theorem linearIndependent_pair_mk_one_iff {R : Type*} [CommRing R] [IsDomain R] {c : R}
    {v : R × R} : LinearIndependent R ![((1 : R), c), v] ↔ v.2 - c * v.1 ≠ 0 := by
  have hbasis : LinearIndependent R ![((1 : R), (0 : R)), ((0 : R), (1 : R))] :=
    LinearIndependent.pair_iff.2 fun s t hst ↦ by simpa [Prod.ext_iff] using hst
  have key := LinearIndependent.pair_add_smul_add_smul_iff (R := R)
    (x := ((1 : R), (0 : R))) (y := ((0 : R), (1 : R))) (1 : R) c v.1 v.2
  simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero, zero_add,
    Prod.mk.eta, one_mul] at key
  rw [key]
  exact ⟨fun h ↦ sub_ne_zero.2 h.2, fun h ↦ ⟨hbasis, sub_ne_zero.1 h⟩⟩

end TauCeti
