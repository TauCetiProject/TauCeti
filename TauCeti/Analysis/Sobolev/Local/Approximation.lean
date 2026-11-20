/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
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
at the points of `K` gives the uniform estimate, and the local `Lᵖ` approximate identity
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
  -- At points of `K`, `u` moves by less than `η` over distances less than `ρ`.
  obtain ⟨ρ, hρ, hucont⟩ := Metric.mem_uniformity_dist.1 (hK.uniformContinuousAt_of_continuousAt u
    (fun z hz => hu.continuousAt (Ω.isOpen.mem_nhds (hKΩ hz))) (Metric.dist_mem_uniformity hη))
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
  -- Mollifiers of radius at most `min δ ρ / 2 < min δ ρ`.
  have hR : 0 < min δ ρ / 2 := half_pos (lt_min hδ hρ)
  let phi : ℕ → ContDiffBump (0 : ℂ) := ContDiffBump.shrinking hR
  have hrlt (j : ℕ) : (phi j).rOut < min δ ρ :=
    (ContDiffBump.rOut_shrinking_le hR j).trans_lt (half_lt_self (lt_min hδ hρ))
  -- At points of `K` the bump balls stay in `W`.
  have hball (j : ℕ) {z : ℂ} (hz : z ∈ K) : closedBall z (phi j).rOut ⊆ W :=
    (closedBall_subset_ball ((hrlt j).trans_le (min_le_left _ _))).trans
      (ball_subset_thickening hz δ)
  have : Fact (1 ≤ p) := ⟨hp⟩
  obtain ⟨j, hj⟩ := ((tendsto_eLpNorm_normed_convolution_sub_restrict hp_top
    (ContDiffBump.tendsto_rOut_shrinking hR) (s := K) hδ
    (((memLp_indicator_iff_restrict hW.nullMeasurableSet).2 hDuW).restrict
      (thickening δ K))).eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hη))).exists
  refine ⟨(W : Set ℂ).indicator u ⋆[(lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, volume]
    (phi j).normed volume, ?_, fun z hz => ?_, ?_⟩
  · exact (phi j).hasCompactSupport_normed.contDiff_convolution_right _
      (((memLp_indicator_iff_restrict hW.nullMeasurableSet).2 huW).locallyIntegrable hp)
      (phi j).contDiff_normed
  · -- The mollification at `z` averages `u` over a ball of radius less than `ρ`.
    have hzW : z ∈ (W : Set ℂ) := hball j hz (mem_closedBall_self (phi j).rOut_pos.le)
    rw [convolution_flip, ← indicator_of_mem hzW u]
    refine (phi j).dist_normed_convolution_le
      ((memLp_indicator_iff_restrict hW.nullMeasurableSet).2 huW).aestronglyMeasurable
      fun x hx => ?_
    rw [indicator_of_mem (hball j hz (ball_subset_closedBall hx)), indicator_of_mem hzW, dist_comm]
    exact (hucont ((mem_ball'.1 hx).trans ((hrlt j).trans_le (min_le_right _ _))) hz).le
  · -- On `K` the derivative of the mollification is the mollified weak derivative.
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) hj
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    have hzW : z ∈ (W : Set ℂ) := hball j hz (mem_closedBall_self (phi j).rOut_pos.le)
    rw [((hDu.mono hWΩ).hasFDerivAt_indicator_convolution_normed huW hDuW hp hp (phi j) z
      (hball j hz)).fderiv, convolution_flip, Pi.sub_apply, indicator_of_mem hzW]

end TauCeti
