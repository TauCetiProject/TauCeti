/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Smooth approximation of continuous local `W^{1,p}` maps on compact sets

Let `Ω ⊆ ℂ` be open, let `u : ℂ → F` be continuous on `Ω` with weak derivative `Du` on `Ω`, and
suppose that `Du` is locally `Lᵖ` on `Ω` for some `1 ≤ p < ∞`. On every compact set
`K ⊆ Ω`, `u` is then approximated by smooth maps `v` on the whole plane, simultaneously uniformly
on `K` and with `fderiv v` close to `Du` in `Lᵖ(K)`
(`TauCeti.exists_contDiff_dist_le_and_eLpNorm_fderiv_sub_le`).

The approximation is a mollification: on the thickening `W` of `K` by a radius `δ` with
`cthickening δ K ⊆ Ω`, convolve the zero extension of `u` from `W` with a normalized bump of
outer radius `r < δ`. At points of `K` the bump ball stays in `W`, so the derivative of the
mollification is the mollification of the zero extension of `Du`
(`TauCeti.HasWeakFDerivOn.hasFDerivAt_indicator_convolution_normed`). Uniform continuity of `u`
on `cthickening δ K` gives the uniform estimate, and the local `Lᵖ` approximate identity
(`TauCeti.tendsto_eLpNorm_normed_convolution_sub_restrict`) gives the estimate of the derivative.

This is the first-order, vector-valued counterpart of
`TauCeti.Wkp.exists_contDiff_abs_sub_le_and_eLpNorm_fderiv_gradient_sub_le`, stated with the
local classes `TauCeti.MemLpLoc` and `TauCeti.HasWeakFDerivOn` of the plane. It is how integral
identities proved against smooth coefficients pass to continuous Sobolev coefficients.

## References

* L. C. Evans, *Partial Differential Equations*, second edition, §5.3.1.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace ContinuousLinearMap
open scoped Convolution ENNReal Topology ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} {Ω : Opens ℂ} {u : ℂ → F} {Du : ℂ → ℂ →L[ℝ] F} {K : Set ℂ}

/-- **Smooth approximation of a continuous local `W^{1,p}` map on a compact set.** Let `u` be
continuous on the open set `Ω`, with weak derivative `Du` on `Ω` that is locally `Lᵖ` on `Ω` for
`1 ≤ p < ∞`. For every compact `K ⊆ Ω` and every `η > 0` there is a smooth map
`v` on the whole plane with `dist (v z) (u z) ≤ η` on `K` and `‖fderiv v - Du‖_{Lᵖ(K)} ≤ η`. -/
theorem exists_contDiff_dist_le_and_eLpNorm_fderiv_sub_le (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hu : ContinuousOn u Ω) (hDu : HasWeakFDerivOn volume Ω u Du)
    (hDuLp : MemLpLoc p Ω Du) (hK : IsCompact K) (hKΩ : K ⊆ Ω) {η : ℝ} (hη : 0 < η) :
    ∃ v : ℂ → F, ContDiff ℝ ∞ v ∧ (∀ z ∈ K, dist (v z) (u z) ≤ η) ∧
      eLpNorm (fun z => fderiv ℝ v z - Du z) p (volume.restrict K) ≤ ENNReal.ofReal η := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen hKΩ
  obtain ⟨ρ, hρ, hucont⟩ := Metric.uniformContinuousOn_iff.1
    ((hK.cthickening (r := δ)).uniformContinuousOn_of_continuous (hu.mono hδΩ)) η hη
  -- The mollification only sees `u` on the thickening `W` of `K`.
  let W : Opens ℂ := ⟨thickening δ K, isOpen_thickening⟩
  have hWΩ : W ≤ Ω := fun z hz => hδΩ (thickening_subset_cthickening δ K hz)
  have hclW : closure (W : Set ℂ) ⊆ cthickening δ K := closure_thickening_subset_cthickening δ K
  have hWc : IsCompact (closure (W : Set ℂ)) :=
    (hK.cthickening (r := δ)).of_isClosed_subset isClosed_closure hclW
  have huW : MemLp u p (volume.restrict W) :=
    hu.memLpLoc.memLp_of_closure_subset hWc (hclW.trans hδΩ)
  have hDuW : MemLp Du p (volume.restrict W) :=
    hDuLp.memLp_of_closure_subset hWc (hclW.trans hδΩ)
  have hW : MeasurableSet (W : Set ℂ) := W.isOpen.measurableSet
  -- Mollifiers of radius `min δ ρ / (j + 2) < min δ ρ`.
  set r : ℕ → ℝ := fun j => min δ ρ / ((j : ℝ) + 2)
  have hr (j : ℕ) : 0 < r j := by have := lt_min hδ hρ; positivity
  have hrlt (j : ℕ) : r j < min δ ρ :=
    div_lt_self (lt_min hδ hρ) (by linarith [Nat.cast_nonneg (α := ℝ) j])
  let phi : ℕ → ContDiffBump (0 : ℂ) := fun j => ⟨r j / 2, r j, half_pos (hr j),
    half_lt_self (hr j)⟩
  have hphi : Tendsto (fun j => (phi j).rOut) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := min δ ρ)).div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  -- At points of `K` the bump balls stay in `W`.
  have hball (j : ℕ) {z : ℂ} (hz : z ∈ K) : closedBall z (phi j).rOut ⊆ W := by
    refine (closedBall_subset_ball ((hrlt j).trans_le (min_le_left _ _))).trans ?_
    exact ball_subset_thickening hz δ
  have : Fact (1 ≤ p) := ⟨hp⟩
  obtain ⟨j, hj⟩ := ((tendsto_eLpNorm_normed_convolution_sub_restrict hp_top hphi (s := K) hδ
    (((memLp_indicator_iff_restrict hW.nullMeasurableSet).2 hDuW).restrict
      (thickening δ K))).eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hη))).exists
  refine ⟨(W : Set ℂ).indicator u ⋆[(lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, volume]
    (phi j).normed volume, ?_, fun z hz => ?_, ?_⟩
  · exact (phi j).hasCompactSupport_normed.contDiff_convolution_right _
      (((memLp_indicator_iff_restrict hW.nullMeasurableSet).2 huW).locallyIntegrable hp)
      (phi j).contDiff_normed
  · -- The mollification at `z` averages `u` over a ball of radius less than `ρ`.
    rw [convolution_flip]
    have hzW : z ∈ (W : Set ℂ) := hball j hz (mem_closedBall_self (phi j).rOut_pos.le)
    have h := (phi j).dist_normed_convolution_le (μ := volume) (x₀ := z) (ε := η)
      (g := (W : Set ℂ).indicator u)
      ((memLp_indicator_iff_restrict hW.nullMeasurableSet).2 huW).aestronglyMeasurable
      fun x hx => by
        have hxW : x ∈ (W : Set ℂ) := hball j hz (ball_subset_closedBall hx)
        rw [indicator_of_mem hxW, indicator_of_mem hzW]
        refine (hucont x ?_ z (self_subset_cthickening K hz) ?_).le
        · exact mem_cthickening_of_dist_le x z δ K hz
            ((mem_ball.1 hx).le.trans ((hrlt j).le.trans (min_le_left _ _)))
        · exact (mem_ball.1 hx).trans ((hrlt j).trans_le (min_le_right _ _))
    rwa [indicator_of_mem hzW] at h
  · -- On `K` the derivative of the mollification is the mollified weak derivative.
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) hj
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    have hzW : z ∈ (W : Set ℂ) := hball j hz (mem_closedBall_self (phi j).rOut_pos.le)
    rw [((hDu.mono hWΩ).hasFDerivAt_indicator_convolution_normed huW hDuW hp hp (phi j) z
      (hball j hz)).fderiv, convolution_flip, Pi.sub_apply, indicator_of_mem hzW]

end TauCeti
