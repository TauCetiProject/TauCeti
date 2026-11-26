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

/-!
# The content of a multivariate polynomial over a discrete valuation ring

Let `O` be a discrete valuation ring with uniformizer `ϖ`. Every nonzero `F ∈ O[X_σ]` is
`ϖ^c G` with `G` of unit content, that is, with some coefficient a unit
(`IsDiscreteValuationRing.exists_eq_C_pow_mul_isUnit_coeff`). Products of polynomials of unit
content have unit content over any local ring (`IsLocalRing.exists_isUnit_coeff_prod`, in
`TauCeti.RingTheory.LocalRing.MvPolynomial`).
-/

public section

open MvPolynomial

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
