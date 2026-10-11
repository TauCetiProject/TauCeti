/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.Window
public import TauCeti.RingTheory.WittVector.Window.Localization

/-!
# Rational presentations of Fargues–Fontaine windows

The radius inequalities defining a closed interval in `𝒴` can be combined into one rational
localisation of `Spa(𝕎 R, 𝕎 R)`. This is the valuation-theoretic presentation used to identify its
completed coordinate ring with the interval ring `B^I`.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, Arizona Winter School 2017, §3.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.29.
-/

public section

namespace TauCeti.FarguesFontaine

open TauCeti.ValuationSpectrum _root_.WittVector TauCeti.WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
  [TopologicalSpace (WittVector p R)] {ϖ : R}

local notation "𝕎" => _root_.WittVector p

/-- **A closed radius interval is one rational subset.** For positive lower endpoint `q`, the
points of `𝒴` satisfying `q ≤ κ(v) ≤ q'` form the rational subset with numerators and denominator
`windowNumerators p ϖ q q'` and `windowDenominator p ϖ q q'`. The nonvanishing conditions at `p` and
`[ϖ]` let the two defining inequalities be combined and then recovered by cancellation. -/
theorem radiusInterval_eq_rationalSubset (q q' : ℚ≥0) (hq : q ≠ 0) :
    {v : Spv (𝕎 R) | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧
      IsRadiusUpperBound p ϖ q' v} =
    {v : Spv (𝕎 R) | v ∈ rationalSubset ⊤
      (windowNumerators p ϖ q q') (windowDenominator p ϖ q q')} := by
  apply Set.ext
  intro v
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, mem_rationalSubset_iff]
  constructor
  · rintro ⟨hvY, hlow, hupp⟩
    obtain ⟨hvSpa, hp, hϖ⟩ := (mem_spaY_iff p ϖ v).mp hvY
    have hp0 : ¬ v.toValuativeRel.vle (p : 𝕎 R) 0 := by
      simpa only [mem_supp_iff] using hp
    have hϖ0 : ¬ v.toValuativeRel.vle (teichmuller p ϖ) 0 := by
      simpa only [mem_supp_iff] using hϖ
    have hϖpow : ¬ v.toValuativeRel.vle (teichmuller p ϖ ^ q'.den) 0 := by
      intro h
      apply hϖ0
      exact (mem_supp_iff v _).mp ((instIsPrimeSupp v).mem_of_pow_mem q'.den
        ((mem_supp_iff v _).mpr h))
    have hppow : ¬ v.toValuativeRel.vle ((p : 𝕎 R) ^ q.num) 0 := by
      intro h
      apply hp0
      exact (mem_supp_iff v _).mp ((instIsPrimeSupp v).mem_of_pow_mem q.num
        ((mem_supp_iff v _).mpr h))
    refine ⟨hvSpa, ?_, ?_⟩
    · intro t ht
      rw [mem_windowNumerators_iff] at ht
      rcases ht with rfl | rfl
      · have hlow' := (isRadiusLowerBound_iff_of_eq_div q.den_ne_zero
          (NNRat.num_div_den q).symm v).mp hlow
        simpa [windowDenominator_def, pow_add] using v.toValuativeRel.mul_vle_mul_left hlow'
          (teichmuller p ϖ ^ q'.den)
      · have hupp' := (isRadiusUpperBound_iff_of_eq_div q'.den_ne_zero
          (NNRat.num_div_den q').symm v).mp hupp
        simpa [windowDenominator_def, pow_add] using v.toValuativeRel.mul_vle_mul_right hupp'
          ((p : 𝕎 R) ^ q.num)
    · rw [windowDenominator_def]
      intro hs
      have hs' : (p : 𝕎 R) ^ q.num * teichmuller p ϖ ^ q'.den ∈ v.supp := by
        simpa only [mem_supp_iff] using hs
      rcases (instIsPrimeSupp v).mul_mem_iff_mem_or_mem.mp hs' with hp' | hϖ'
      · exact hppow ((mem_supp_iff v _).mp hp')
      · exact hϖpow ((mem_supp_iff v _).mp hϖ')
  · rintro ⟨hvSpa, hT, hs⟩
    have hp : (p : 𝕎 R) ∉ v.supp := by
      intro hp
      apply hs
      rw [windowDenominator_def]
      apply (mem_supp_iff v _).mp
      exact (instIsPrimeSupp v).mul_mem_iff_mem_or_mem.mpr (Or.inl
        (Ideal.pow_mem_of_mem _ hp _ (NNRat.num_pos.mpr (pos_iff_ne_zero.mpr hq))))
    have hϖ : teichmuller p ϖ ∉ v.supp := by
      intro hϖ
      apply hs
      rw [windowDenominator_def]
      apply (mem_supp_iff v _).mp
      exact (instIsPrimeSupp v).mul_mem_iff_mem_or_mem.mpr (Or.inr
        (Ideal.pow_mem_of_mem _ hϖ _ q'.den_pos))
    have hvY : v ∈ spaY p ϖ := by
      rw [mem_spaY_iff]
      exact ⟨hvSpa, hp, hϖ⟩
    have hϖpow : ¬ v.toValuativeRel.vle (teichmuller p ϖ ^ q'.den) 0 := by
      simpa only [mem_supp_iff] using
        (fun h ↦ hϖ ((instIsPrimeSupp v).mem_of_pow_mem q'.den
          ((mem_supp_iff v _).mpr h)))
    have hppow : ¬ v.toValuativeRel.vle ((p : 𝕎 R) ^ q.num) 0 := by
      simpa only [mem_supp_iff] using
        (fun h ↦ hp ((instIsPrimeSupp v).mem_of_pow_mem q.num
          ((mem_supp_iff v _).mpr h)))
    have hlower : v.toValuativeRel.vle (teichmuller p ϖ ^ q.den)
        ((p : 𝕎 R) ^ q.num) := by
      have h := hT _ (mem_windowNumerators_iff.mpr (Or.inl rfl))
      rw [windowDenominator_def] at h
      exact v.toValuativeRel.vle_mul_cancel hϖpow (by
        simpa only [pow_add, mul_comm] using h)
    have hupper : v.toValuativeRel.vle ((p : 𝕎 R) ^ q'.num)
        (teichmuller p ϖ ^ q'.den) := by
      have h := hT _ (mem_windowNumerators_iff.mpr (Or.inr rfl))
      rw [windowDenominator_def] at h
      exact v.toValuativeRel.vle_mul_cancel hppow (by
        simpa only [pow_add, mul_comm] using h)
    exact ⟨hvY, (isRadiusLowerBound_iff_of_eq_div q.den_ne_zero
      (NNRat.num_div_den q).symm v).mpr hlower,
      (isRadiusUpperBound_iff_of_eq_div q'.den_ne_zero
        (NNRat.num_div_den q').symm v).mpr hupper⟩

end TauCeti.FarguesFontaine
