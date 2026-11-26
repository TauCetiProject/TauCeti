/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Gauss's lemma for multivariate polynomials over a discrete valuation ring

Let `O` be a discrete valuation ring with uniformizer `ϖ`. Every nonzero `F ∈ O[X_σ]` is
`ϖ^c G` with `G` of unit content, that is, with some coefficient a unit
(`IsDiscreteValuationRing.exists_eq_C_pow_mul_isUnit_coeff`). Over any local ring, products of
polynomials of unit content have unit content, since their reductions modulo the maximal ideal are
nonzero polynomials over the residue field, a domain (`IsLocalRing.exists_isUnit_coeff_prod`).
-/

public section

open MvPolynomial IsLocalRing

namespace IsDiscreteValuationRing

variable {O σ : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **Content of a multivariate polynomial over a discrete valuation ring.** A nonzero
`F ∈ O[X_σ]` is `ϖ^c G` with some coefficient of `G` a unit: `c` is the least valuation of a
coefficient of `F`. -/
theorem exists_eq_C_pow_mul_isUnit_coeff {ϖ : O} (hϖ : Irreducible ϖ) {F : MvPolynomial σ O}
    (hF : F ≠ 0) :
    ∃ (c : ℕ) (G : MvPolynomial σ O), F = C (ϖ ^ c) * G ∧ ∃ s, IsUnit (G.coeff s) := by
  have hsupp : F.support.Nonempty := support_nonempty.2 hF
  obtain ⟨s₀, hs₀, hmin⟩ := F.support.exists_min_image (fun s ↦ addVal O (F.coeff s)) hsupp
  have hne : F.coeff s₀ ≠ 0 := mem_support_iff.1 hs₀
  obtain ⟨c, u, hc⟩ := eq_unit_mul_pow_irreducible hne hϖ
  have hdvd : ∀ s, ϖ ^ c ∣ F.coeff s := fun s ↦ by
    by_cases hs : s ∈ F.support
    · refine addVal_le_iff_dvd.1 (le_of_eq_of_le ?_ (hmin s hs))
      rw [hc, addVal_mul, (addVal_eq_zero_iff).2 u.isUnit, zero_add]
    · rw [notMem_support_iff.1 hs]
      exact dvd_zero _
  obtain ⟨G, rfl⟩ := (C_dvd_iff_dvd_coeff _ _).2 hdvd
  refine ⟨c, G, rfl, s₀, ?_⟩
  rw [coeff_C_mul, mul_comm (u : O)] at hc
  rw [mul_left_cancel₀ (pow_ne_zero c hϖ.ne_zero) hc]
  exact u.isUnit

end IsDiscreteValuationRing

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
