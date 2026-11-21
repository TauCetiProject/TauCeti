/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
import TauCeti.Analysis.InnerProductSpace.RankOne
import TauCeti.MeasureTheory.Function.RankOne

/-!
# Zeros of nearly holomorphic maps

A map `b : ℂ → N` into a finite-dimensional complex inner product space is *nearly holomorphic*
when its Cauchy–Riemann defect is controlled by its size, `‖∂ₛb + i ∂ₜb‖ ≤ M ‖b‖` for a locally
bounded `M`. Such a map solves the linear Cauchy–Riemann equation `∂ₛb + i ∂ₜb + C b = 0` for
the bounded rank-one coefficient `C = -(∂ₛb + i ∂ₜb) b* / ‖b‖²` (`TauCeti.rankOneDivNormSq`), so
by Carleman's similarity principle (`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn`)
its zeros are isolated unless it vanishes identically.

## Main results

* `TauCeti.eqOn_zero_of_frequently_eq_zero_of_norm_add_I_smul_le`: a `C¹` solution of
  `‖∂ₛb + i ∂ₜb‖ ≤ M ‖b‖` on a connected open set, `M` locally bounded above, whose zeros
  accumulate at a point of the set vanishes on the set.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section 2.3 and the proof of Lemma 2.4.3.
-/

public section

open Set Filter Complex
open scoped Topology

namespace TauCeti

variable {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N]

/-- **Accumulating zeros of a nearly holomorphic map.** Let `b : ℂ → N` be of class `C¹` on a
connected open set `Ω`, with values in a finite-dimensional complex inner product space, and
satisfy `‖∂ₛb + i ∂ₜb‖ ≤ M ‖b‖` on `Ω` for a function `M` locally bounded above. If the zeros of
`b` accumulate at a point of `Ω`, then `b` vanishes on `Ω`. In the proof of McDuff–Salamon's
Lemma 2.4.3, `b` is the normal component of a pseudoholomorphic disc in coordinates adapted to
another one. -/
theorem eqOn_zero_of_frequently_eq_zero_of_norm_add_I_smul_le {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) {b : ℂ → N} {M : ℂ → ℝ} (hb : ContDiffOn ℝ 1 b Ω)
    (hM : ∀ z ∈ Ω, ∃ K, ∀ᶠ w in 𝓝 z, M w ≤ K)
    (hineq : ∀ z ∈ Ω, ‖fderiv ℝ b z 1 + I • fderiv ℝ b z I‖ ≤ M z * ‖b z‖) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) (hfreq : ∃ᶠ z in 𝓝[≠] z₀, b z = 0) : EqOn b 0 Ω := by
  -- the defect `g = -(∂ₛb + i ∂ₜb)` is absorbed by the rank-one coefficient `C' = g b* / ‖b‖²`
  set g : ℂ → N := fun z ↦ -(fderiv ℝ b z 1 + I • fderiv ℝ b z I) with hg
  set C : ℂ → N →L[ℝ] N := fun z ↦ (rankOneDivNormSq ℂ (g z) (b z)).restrictScalars ℝ with hC
  have hDb : ContinuousOn (fderiv ℝ b) Ω := hb.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hgc : ContinuousOn g Ω :=
    ((hDb.clm_apply continuousOn_const).add
      ((hDb.clm_apply continuousOn_const).const_smul I)).neg
  have hCb (z : ℂ) (hz : z ∈ Ω) : C z (b z) = g z := by
    by_cases h0 : b z = 0
    · have h := hineq z hz
      rw [h0, norm_zero, mul_zero, norm_le_zero_iff] at h
      have hg0 : g z = 0 := by simp only [hg, h, neg_zero]
      simp [hC, h0, hg0]
    · simp only [hC, ContinuousLinearMap.coe_restrictScalars', rankOneDivNormSq_apply_self _ h0]
  have hne := setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn (C := C) hΩ hΩc hb
    ((ContinuousLinearMap.restrictScalarsL ℂ _ _ ℝ ℂ).continuous.comp_aestronglyMeasurable
      ((hgc.aestronglyMeasurable hΩ.measurableSet).rankOneDivNormSq
        (hb.continuousOn.aestronglyMeasurable hΩ.measurableSet)))
    (fun z hz ↦ ?_) (fun z hz ↦ by rw [hCb z hz, hg, add_neg_cancel])
  · -- the zeros accumulate at `z₀`, so the codiscreteness alternative fails
    by_contra hb0
    obtain ⟨z, hz, hbz⟩ : ∃ z ∈ Ω, b z ≠ 0 := by
      by_contra h
      push Not at h
      exact hb0 fun z hz ↦ h z hz
    have hdisj : ∀ᶠ w in 𝓝[≠] z₀, w ∉ Ω \ {w | b w ≠ 0} :=
      disjoint_principal_right.1 (mem_codiscreteWithin.1 (hne ⟨z, hz, hbz⟩) z₀ hz₀)
    have hΩz : ∀ᶠ w in 𝓝[≠] z₀, w ∈ Ω := nhdsWithin_le_nhds (hΩ.mem_nhds hz₀)
    obtain ⟨w, hbw, hdis, hwΩ⟩ := (hfreq.and_eventually (hdisj.and hΩz)).exists
    exact hdis ⟨hwΩ, fun h ↦ h hbw⟩
  · -- the coefficient is locally bounded, by `max K 0`
    obtain ⟨K, hK⟩ := hM z hz
    refine ⟨max K 0, ?_⟩
    filter_upwards [hK, hΩ.mem_nhds hz] with w hwK hwΩ
    rw [hC, ContinuousLinearMap.norm_restrictScalars, norm_rankOneDivNormSq]
    by_cases h0 : b w = 0
    · simp [h0]
    refine div_le_of_le_mul₀ (norm_nonneg _) (le_max_right _ _) ?_
    rw [hg, norm_neg]
    exact (hineq w hwΩ).trans (mul_le_mul_of_nonneg_right (le_max_of_le_left hwK) (norm_nonneg _))

end TauCeti
