/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Polynomial evaluation over local rings with infinite residue field

Over a local ring `R` whose residue field is infinite, any finite family of polynomials in `R[X]`
with nonzero reduction modulo the maximal ideal simultaneously evaluates to units at some element
of `R`.

## Main results

* `Polynomial.exists_forall_isUnit_eval`: simultaneous unit evaluation of finitely many polynomials
  with nonzero residue-field reductions.
-/

public section

namespace Polynomial

/-- Over a local ring with infinite residue field, finitely many polynomials with nonzero
reduction modulo the maximal ideal simultaneously evaluate to units at some ring element. -/
theorem exists_forall_isUnit_eval {R ι : Type*} [CommRing R] [IsLocalRing R]
    [Infinite (IsLocalRing.ResidueField R)] (s : Finset ι) (f : ι → R[X])
    (hf : ∀ j ∈ s, (f j).map (IsLocalRing.residue R) ≠ 0) :
    ∃ u : R, ∀ j ∈ s, IsUnit ((f j).eval u) := by
  have hev : ∀ᶠ y : IsLocalRing.ResidueField R in Filter.cofinite,
      ∀ j ∈ s, ((f j).map (IsLocalRing.residue R)).eval y ≠ 0 :=
    s.eventually_all.mpr fun j hj ↦ eventually_eval_ne_zero_cofinite (hf j hj)
  obtain ⟨y, hy⟩ := hev.exists
  obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective y
  refine ⟨u, fun j hj ↦ ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← eval_map_apply]
  exact hy j hj

end Polynomial
