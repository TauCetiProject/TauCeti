/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.Window.Basic
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
`windowNumerators p ϖ q q'` and `windowDenominator p ϖ q q'`. -/
theorem radiusInterval_eq_rationalSubset (q q' : ℚ≥0) (hq : q ≠ 0) :
    {v : Spv (𝕎 R) | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧
      IsRadiusUpperBound p ϖ q' v} =
    rationalSubset ⊤ (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') := by
  classical
  /- The window is already known to be the intersection of its endpoint rational subsets.
  Combine their inequalities over the common denominator. -/
  rw [setOf_isRadiusLowerBound_isRadiusUpperBound_eq hq]
  apply Set.ext
  intro v
  rw [Set.mem_inter_iff, mem_rationalSubset_iff, mem_rationalSubset_iff,
    mem_rationalSubset_iff]
  have hprod {x y : 𝕎 R} :
      ¬ v.toValuativeRel.vle (x * y) 0 ↔ x ∉ v.supp ∧ y ∉ v.supp := by
    rw [← mem_supp_iff, (instIsPrimeSupp v).mul_mem_iff_mem_or_mem]
    simp only [not_or]
  have hsupp {x : 𝕎 R} {k : ℕ} (hk : k ≠ 0) :
      ¬ v.toValuativeRel.vle (x ^ k) 0 ↔ x ∉ v.supp := by
    rw [← mem_supp_iff, Ideal.IsPrime.pow_mem_iff_mem inferInstance k (Nat.pos_of_ne_zero hk)]
  have hden : ¬ v.toValuativeRel.vle (windowDenominator p ϖ q q') 0 ↔
      (p : 𝕎 R) ∉ v.supp ∧ teichmuller p ϖ ∉ v.supp := by
    rw [windowDenominator_def, hprod]
    constructor
    · rintro ⟨hp, hϖ⟩
      have hp' : ¬ v.toValuativeRel.vle ((p : 𝕎 R) ^ q.num) 0 := by
        simpa only [mem_supp_iff] using hp
      have hϖ' : ¬ v.toValuativeRel.vle (teichmuller p ϖ ^ q'.den) 0 := by
        simpa only [mem_supp_iff] using hϖ
      exact ⟨(hsupp (NNRat.num_ne_zero.mpr hq)).mp hp',
        (hsupp q'.den_ne_zero).mp hϖ'⟩
    · rintro ⟨hp, hϖ⟩
      have hp' := (hsupp (NNRat.num_ne_zero.mpr hq)).mpr hp
      have hϖ' := (hsupp q'.den_ne_zero).mpr hϖ
      exact ⟨by simpa only [mem_supp_iff] using hp',
        by simpa only [mem_supp_iff] using hϖ'⟩
  constructor
  · rintro ⟨⟨hvSpa, hlowSet, hlowDen⟩, ⟨_, huppSet, huppDen⟩⟩
    have hlow' : v.toValuativeRel.vle (teichmuller p ϖ ^ q.den)
        ((p : 𝕎 R) ^ q.num) := hlowSet _ (by simp)
    have hupp' : v.toValuativeRel.vle ((p : 𝕎 R) ^ q'.num)
        (teichmuller p ϖ ^ q'.den) := huppSet _ (by simp)
    have hlow := (isRadiusLowerBound_iff_of_eq_div q.den_ne_zero
      (NNRat.num_div_den q).symm v).mpr hlow'
    have hupp := (isRadiusUpperBound_iff_of_eq_div q'.den_ne_zero
      (NNRat.num_div_den q').symm v).mpr hupp'
    refine ⟨hvSpa, ?_, ?_⟩
    · intro t ht
      rw [mem_windowNumerators_iff] at ht
      rcases ht with rfl | rfl
      · have h := v.toValuativeRel.mul_vle_mul_left hlow'
          (teichmuller p ϖ ^ q'.den)
        simpa only [windowDenominator_def, pow_add, mul_comm, mul_left_comm] using h
      · have h := v.toValuativeRel.mul_vle_mul_right hupp' ((p : 𝕎 R) ^ q.num)
        simpa only [windowDenominator_def, pow_add, mul_comm, mul_left_comm] using h
    · exact (hden).mpr ⟨(hsupp (NNRat.num_ne_zero.mpr hq)).mp hlowDen,
        (hsupp q'.den_ne_zero).mp huppDen⟩
  · rintro ⟨hvSpa, hT, hs⟩
    have hnot := hden.mp hs
    have hvY : v ∈ spaY p ϖ := by
      rw [mem_spaY_iff]
      exact ⟨hvSpa, hnot.1, hnot.2⟩
    have hϖpow := (hsupp q'.den_ne_zero).mpr hnot.2
    have hppow := (hsupp (NNRat.num_ne_zero.mpr hq)).mpr hnot.1
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
    refine ⟨⟨hvSpa, ?_, hppow⟩, ⟨hvSpa, ?_, hϖpow⟩⟩
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hlower
      · exact v.toValuativeRel.vle_refl _
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hupper
      · exact v.toValuativeRel.vle_refl _

end TauCeti.FarguesFontaine
