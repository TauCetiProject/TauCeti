/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import TauCeti.RingTheory.Polynomial.DegreeLT

/-!
# Counting the monic polynomials that vanish at a point

Over a finite commutative ring with `q` elements, at most `q ^ (r - 1)` monic polynomials of
degree `r` vanish at a given point `a`: by the factor theorem (Mathlib's
`Polynomial.dvd_iff_isRoot`) each is `X - C a` times a monic polynomial of degree `r - 1`, and
there are `q ^ (r - 1)` of those (`Polynomial.ncard_setOf_monic_natDegree_eq`).

## Main results

* `TauCeti.Polynomial.ncard_setOf_monic_natDegree_isRoot_le`: at most `Nat.card R ^ (r - 1)`
  monic polynomials of degree `r` over a finite commutative ring vanish at a given point.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

/-- At most `q ^ (r - 1)` monic polynomials of degree `r` over a finite commutative ring with `q`
elements vanish at a given point `a`: each is `X - C a` times a monic polynomial of degree
`r - 1`. -/
theorem ncard_setOf_monic_natDegree_isRoot_le {R : Type*} [CommRing R] [Finite R] (a : R)
    (r : ℕ) :
    {f : R[X] | f.Monic ∧ f.natDegree = r ∧ f.IsRoot a}.ncard ≤ Nat.card R ^ (r - 1) := by
  cases subsingleton_or_nontrivial R
  · rw [Nat.card_unique, one_pow]
    exact Set.ncard_le_one_of_subsingleton _
  have hsub : {f : R[X] | f.Monic ∧ f.natDegree = r ∧ f.IsRoot a} ⊆
      ((X - C a) * ·) '' {g : R[X] | g.Monic ∧ g.natDegree = r - 1} := by
    rintro f ⟨hf, hr, ha⟩
    -- in degree `0` the only monic polynomial is `1`, which has no root
    have h1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr fun h0 ↦ by
      simp [eq_one_of_monic_natDegree_zero hf (hr.trans h0)] at ha
    obtain ⟨g, rfl⟩ := dvd_iff_isRoot.mpr ha
    -- the quotient by the monic linear factor is monic of degree `r - 1`
    have hg := (isMonicOfDegree_X_sub_one a).of_mul_left (n := r - 1)
      ⟨by rw [hr]; omega, hf⟩
    exact ⟨g, ⟨hg.monic, hg.natDegree_eq⟩, rfl⟩
  calc _ ≤ _ := Set.ncard_le_ncard hsub ((finite_setOf_monic_natDegree_eq R _).image _)
    _ ≤ _ := Set.ncard_image_le (finite_setOf_monic_natDegree_eq R _)
    _ = _ := ncard_setOf_monic_natDegree_eq R _

end TauCeti.Polynomial
