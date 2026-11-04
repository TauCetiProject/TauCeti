/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import TauCeti.Analysis.Calculus.ContDiff.Convolution
public import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
public import TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Smoothing at a scale with derivative bounds

Mathlib's `MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`
smooths a locally integrable function `f` on a finite-dimensional real normed space at a scale
`ε > 0`: it gives a smooth `g` with `dist (g a) (f a) ≤ δ` wherever `f` oscillates by at most `δ`
on `ball a ε`. This file adds the matching derivative bounds: at such points the `k`-th
derivative of `g`, `k ≥ 1`, is at most `K k * δ / ε ^ k`, with constants `K k` depending only on
the space, not on `f`, `ε`, `a` or `δ`
(`TauCeti.exists_forall_exists_contDiff_dist_le_and_norm_iteratedFDeriv_le`).

So a function with modulus of continuity `ω` has smoothings `g_ε` with `‖g_ε - f‖ ≤ ω(ε)` and
`‖D^k g_ε‖ ≤ K k ω(ε) / ε ^ k`. This is the form in which a merely uniformly continuous datum is
compared with smooth barriers, for instance in the attainment of initial values by solutions of
parabolic equations, where the scale is `ε = √t`.

The smoothing is the mollification at scale `ε` by a fixed normalized bump: the rescaled
function `y ↦ f (ε • y)` is mollified by a bump supported in `closedBall 0 (1 / 2)`, and the
result is rescaled back. The derivative bound at scale one is
`HasCompactSupport.norm_iteratedFDeriv_convolution_left_le_of_dist_le`; rescaling by `ε⁻¹`
multiplies the `k`-th derivative by at most `ε⁻¹ ^ k`.

## References

* L. C. Evans, *Partial Differential Equations*, Appendix C.5.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set ContinuousLinearMap
open scoped Convolution ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Smoothing at scale `ε` with derivative bounds.** There are nonnegative constants `K k`,
depending only on `E` and `μ`, with the following property. For every `ε > 0` and every locally
integrable `f : E → F` there is a smooth `g : E → F` such that at every point `a` where `f`
differs from `f a` by at most `δ` on `ball a ε`, `dist (g a) (f a) ≤ δ` and the `k`-th derivative
of `g` at `a`, for `k ≥ 1`, has norm at most `K k * δ / ε ^ k`. -/
theorem exists_forall_exists_contDiff_dist_le_and_norm_iteratedFDeriv_le :
    ∃ K : ℕ → ℝ, (∀ k, 0 ≤ K k) ∧ ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃f : E → F⦄, LocallyIntegrable f μ →
      ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ a δ, (∀ x ∈ ball a ε, dist (f x) (f a) ≤ δ) →
        dist (g a) (f a) ≤ δ ∧ ∀ k, k ≠ 0 → ‖iteratedFDeriv ℝ k g a‖ ≤ K k * δ / ε ^ k := by
  let φ : ContDiffBump (0 : E) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  refine ⟨fun k ↦ ∫ y, ‖iteratedFDeriv ℝ k (φ.normed μ) y‖ ∂μ,
    fun k ↦ integral_nonneg fun _ ↦ norm_nonneg _, fun ε hε f hf ↦ ?_⟩
  -- Mollify `h = f (ε • ·)` at scale one and rescale the result by `L = ε⁻¹ • id`.
  set h : E → F := fun y ↦ f (ε • y)
  have hh : LocallyIntegrable h μ := locallyIntegrableOn_univ.mp
    ((hf.locallyIntegrableOn univ).comp_smul_of_mapsTo hε.ne' (mapsTo_univ _ _))
  set H := φ.normed μ ⋆[lsmul ℝ ℝ, μ] h
  have hH : ContDiff ℝ ∞ H :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hh
  set L : E →L[ℝ] E := ε⁻¹ • ContinuousLinearMap.id ℝ E
  have hLa (a : E) : ε • L a = a := by simp [L, smul_smul, hε.ne']
  refine ⟨H ∘ L, hH.comp L.contDiff, fun a δ hδ ↦ ?_⟩
  -- The oscillation of `h` on `ball (L a) 1` is that of `f` on `ball a ε`.
  have hδL : ∀ y ∈ ball (L a) 1, dist (h y) (h (L a)) ≤ δ := by
    intro y hy
    simp only [h, hLa]
    refine hδ _ ?_
    rw [mem_ball, dist_eq_norm] at hy ⊢
    calc ‖ε • y - a‖ = ε * ‖y - L a‖ := by
          rw [← hLa a, ← smul_sub, norm_smul, Real.norm_of_nonneg hε.le, hLa]
      _ < ε := mul_lt_of_lt_one_right hε hy
  have hha : h (L a) = f a := by simp only [h, hLa]
  have hδ0 : 0 ≤ δ := by simpa using hδ a (mem_ball_self hε)
  refine ⟨?_, fun k hk ↦ ?_⟩
  · simpa only [Function.comp_apply, hha] using φ.dist_normed_convolution_le hh.aestronglyMeasurable
      fun y hy ↦ hδL y (ball_subset_ball (by norm_num [φ]) hy)
  · have hHk : ‖iteratedFDeriv ℝ k H (L a)‖ ≤ δ * ∫ y, ‖iteratedFDeriv ℝ k (φ.normed μ) y‖ ∂μ := by
      refine φ.hasCompactSupport_normed.norm_iteratedFDeriv_convolution_left_le_of_dist_le
        (N := ⊤) φ.contDiff_normed hh hk le_top fun y hy ↦ hδL _ ?_
      rw [φ.tsupport_normed_eq, mem_closedBall_zero_iff] at hy
      rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
      exact hy.trans_lt (by norm_num [φ])
    have hL : ‖L‖ ≤ ε⁻¹ := (norm_smul_le ε⁻¹ (ContinuousLinearMap.id ℝ E)).trans <| by
      rw [Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
      exact mul_le_of_le_one_right (inv_nonneg.mpr hε.le) norm_id_le
    calc ‖iteratedFDeriv ℝ k (H ∘ L) a‖ ≤ ‖iteratedFDeriv ℝ k H (L a)‖ * ‖L‖ ^ k :=
          L.norm_iteratedFDeriv_comp_right_le hH a (WithTop.coe_le_coe.mpr le_top)
      _ ≤ (δ * ∫ y, ‖iteratedFDeriv ℝ k (φ.normed μ) y‖ ∂μ) * ε⁻¹ ^ k := by
          gcongr
      _ = (∫ y, ‖iteratedFDeriv ℝ k (φ.normed μ) y‖ ∂μ) * δ / ε ^ k := by
          rw [inv_pow, div_eq_mul_inv]
          ring

end TauCeti
