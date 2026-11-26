/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Gauss's lemma for multivariate polynomials over a local ring

Over a local ring `O`, a finite product of multivariate polynomials each having a unit coefficient
has a unit coefficient (`IsLocalRing.exists_isUnit_coeff_prod`). Indeed, the reductions of the
factors modulo the maximal ideal are nonzero polynomials over the residue field, a domain, so their
product is nonzero.
-/

public section

open MvPolynomial

namespace IsLocalRing

/-- **Gauss's lemma over a local ring.** A finite product of multivariate polynomials each having
a unit coefficient has a unit coefficient: the reductions modulo the maximal ideal are nonzero,
and so is their product over the residue field. -/
theorem exists_isUnit_coeff_prod {O σ B : Type*} [CommRing O] [IsLocalRing O] (s : Finset B)
    {G : B → MvPolynomial σ O} (hG : ∀ b ∈ s, ∃ t, IsUnit ((G b).coeff t)) :
    ∃ t, IsUnit ((∏ b ∈ s, G b).coeff t) := by
  have hmap : ∀ b ∈ s, map (residue O) (G b) ≠ 0 := fun b hb ↦ by
    obtain ⟨t, ht⟩ := hG b hb
    refine ne_of_apply_ne (fun p ↦ p.coeff t) ?_
    simpa [coeff_map] using (residue_ne_zero_iff_isUnit _).2 ht
  have hprod : map (residue O) (∏ b ∈ s, G b) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 hmap
  obtain ⟨t, ht⟩ := support_nonempty.2 hprod
  refine ⟨t, (residue_ne_zero_iff_isUnit _).1 ?_⟩
  rw [← coeff_map]
  exact mem_support_iff.1 ht

end IsLocalRing
