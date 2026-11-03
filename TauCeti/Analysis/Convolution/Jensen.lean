/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Jensen's inequality for convolution with a probability kernel

Let `ρ` be a probability kernel on a measurable additive group with a right-invariant measure
`μ`, that is `ρ ≥ 0` almost everywhere and `∫ ρ = 1`. Convolution with `ρ` averages the
translates of a function, so a convex integrand of the norm cannot increase. Precisely, let
`Φ : ℝ → ℝ` be convex and monotone on `[0, ∞)`. Then at every point

`Φ(‖(ρ ⋆ g)(x)‖) ≤ ∫ ρ(t) Φ(‖g(x - t)‖) dt`

(`ConvexOn.ofReal_map_norm_convolution_le_lintegral`), and integrating in `x`,

`∫ Φ(‖ρ ⋆ g‖) ≤ ∫ Φ(‖g‖)`

(`ConvexOn.lintegral_ofReal_map_norm_convolution_le`). Both sides are extended nonnegative
integrals of `ENNReal.ofReal ∘ Φ`, so no integrability of `g` or of `Φ(‖g‖)` is assumed and the
bound is informative exactly when its right side is finite. For a mollifier `ρ` and the weak
gradient `g = ∇u` of a Sobolev function this is the bound `∫ Φ(‖∇(ρ ⋆ u)‖) ≤ ∫ Φ(‖∇u‖)` that
makes mollification compatible with de la Vallée Poussin's criterion
(`MeasureTheory.Integrable.exists_convexOn_superlinear_integrable`).

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  Chapter 4 (mollification of Sobolev functions).
-/

public section

open MeasureTheory Set ContinuousLinearMap
open scoped Convolution ENNReal

variable {G F : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : ℝ → ℝ} {ρ : G → ℝ}

/-- The function `t ↦ max (Φ (max t 0)) 0`, which extends the positive part `max Φ 0` of `Φ`
restricted to `[0, ∞)` to the whole line. -/
private def posExt (Φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  max (Φ (max t 0)) 0

private lemma posExt_nonneg (t : ℝ) : 0 ≤ posExt Φ t :=
  le_max_right _ _

omit [NormedSpace ℝ F] in
private lemma ofReal_posExt_norm (v : F) :
    ENNReal.ofReal (posExt Φ ‖v‖) = ENNReal.ofReal (Φ ‖v‖) := by
  rw [posExt, max_eq_left (norm_nonneg v), ENNReal.ofReal_max, ENNReal.ofReal_zero, max_zero]

private lemma monotone_posExt (hΦm : MonotoneOn Φ (Ici 0)) : Monotone (posExt Φ) :=
  fun _ _ h => max_le_max (hΦm (le_max_right _ _) (le_max_right _ _) (max_le_max h le_rfl)) le_rfl

private lemma convexOn_posExt (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) :
    ConvexOn ℝ univ (posExt Φ) := by
  have himage : (fun t : ℝ => max t 0) '' univ = Ici 0 :=
    ext fun s => ⟨fun ⟨_, _, h⟩ => h ▸ le_max_right _ _, fun h => ⟨s, trivial, max_eq_left h⟩⟩
  have hmax : ConvexOn ℝ univ fun t : ℝ => max t 0 :=
    convexOn_id convex_univ |>.sup (convexOn_const 0 convex_univ)
  exact (ConvexOn.comp (himage ▸ hΦ) hmax (himage ▸ hΦm)).sup (convexOn_const 0 convex_univ)

private lemma continuous_posExt (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) :
    Continuous (posExt Φ) := by
  simpa [continuousOn_univ] using (convexOn_posExt hΦ hΦm).continuousOn_interior

namespace ConvexOn

/-- **Jensen's inequality for convolution.** If `Φ` is convex and monotone on `[0, ∞)` and `ρ`
is a probability kernel, then at every point `Φ(‖(ρ ⋆ g)(x)‖) ≤ ∫ ρ(t) Φ(‖g(x - t)‖) dt`, in
extended nonnegative form. -/
theorem ofReal_map_norm_convolution_le_lintegral (hΦ : ConvexOn ℝ (Ici 0) Φ)
    (hΦm : MonotoneOn Φ (Ici 0)) (hρ0 : 0 ≤ᵐ[μ] ρ) (hρ1 : ∫ t, ρ t ∂μ = 1) {g : G → F}
    (hg : AEStronglyMeasurable g μ) (x : G) :
    ENNReal.ofReal (Φ ‖(ρ ⋆[lsmul ℝ ℝ, μ] g) x‖) ≤
      ∫⁻ t, ENNReal.ofReal (ρ t) * ENNReal.ofReal (Φ ‖g (x - t)‖) ∂μ := by
  -- Apply Jensen's inequality `ConvexOn.map_integral_le` for the probability measure `ρ μ` to
  -- the convex monotone function `posExt Φ` on the whole line, after the triangle inequality
  -- `‖∫ ρ(t) g(x - t)‖ ≤ ∫ ρ(t) ‖g(x - t)‖`. Where the convolution integral does not converge,
  -- its Bochner value is zero and monotonicity gives the bound directly.
  have hρi : Integrable ρ μ := integrable_of_integral_eq_one hρ1
  have hρm : AEMeasurable (fun t => ENNReal.ofReal (ρ t)) μ := hρi.aemeasurable.ennreal_ofReal
  -- The kernel defines a probability measure `ν`, and the convolution is a `ν`-average.
  set ν := μ.withDensity fun t => ENNReal.ofReal (ρ t)
  have : IsProbabilityMeasure ν := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      TauCeti.MeasureTheory.lintegral_ofReal_eq_one hρ0 hρ1]⟩
  set h : G → F := fun t => g (x - t)
  have hh : AEStronglyMeasurable h μ :=
    hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left_of_right_invariant μ x)
  have hhν : AEStronglyMeasurable h ν := hh.mono_ac (withDensity_absolutelyContinuous _ _)
  have hconv : (ρ ⋆[lsmul ℝ ℝ, μ] g) x = ∫ t, h t ∂ν := by
    rw [convolution_def, integral_withDensity_eq_integral_toReal_smul₀ hρm
      (.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae ?_
    filter_upwards [hρ0] with t ht
    simp [ENNReal.toReal_ofReal ht, h]
  set Ψ := posExt Φ
  have hΨc := continuous_posExt hΦ hΦm
  have hΨm := monotone_posExt hΦm
  have hΨν : AEStronglyMeasurable (fun t => Ψ ‖h t‖) ν := hΨc.comp_aestronglyMeasurable hhν.norm
  have hrhs : ∫⁻ t, ENNReal.ofReal (ρ t) * ENNReal.ofReal (Φ ‖g (x - t)‖) ∂μ =
      ∫⁻ t, ENNReal.ofReal (Ψ ‖h t‖) ∂ν := by
    rw [lintegral_withDensity_eq_lintegral_mul₀ hρm
      (hΨc.comp_aestronglyMeasurable hh.norm).aemeasurable.ennreal_ofReal]
    simp only [Pi.mul_apply, h, ofReal_posExt_norm]
  rw [hrhs, ← ofReal_posExt_norm, hconv]
  calc ENNReal.ofReal (Ψ ‖∫ t, h t ∂ν‖) ≤ ENNReal.ofReal (Ψ (∫ t, ‖h t‖ ∂ν)) :=
        ENNReal.ofReal_le_ofReal (hΨm (norm_integral_le_integral_norm h))
    _ ≤ ∫⁻ t, ENNReal.ofReal (Ψ ‖h t‖) ∂ν := by
      by_cases hfin : ∫⁻ t, ENNReal.ofReal (Ψ ‖h t‖) ∂ν = ∞
      · simp [hfin]
      have hΨi : Integrable (fun t => Ψ ‖h t‖) ν :=
        ⟨hΨν, (hasFiniteIntegral_iff_ofReal (.of_forall fun _ => posExt_nonneg _)).2
          (lt_top_iff_ne_top.2 hfin)⟩
      rw [← ofReal_integral_eq_lintegral_ofReal hΨi (.of_forall fun _ => posExt_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      by_cases hni : Integrable (fun t => ‖h t‖) ν
      · exact (convexOn_posExt hΦ hΦm).map_integral_le hΨc.continuousOn isClosed_univ
          (.of_forall fun _ => mem_univ _) hni hΨi
      -- Without integrability the average is zero, and `Ψ 0 ≤ Ψ ‖h t‖` pointwise.
      rw [integral_undef hni]
      calc Ψ 0 = ∫ _, Ψ 0 ∂ν := by simp
        _ ≤ ∫ t, Ψ ‖h t‖ ∂ν := integral_mono (integrable_const _) hΨi fun _ => hΨm (norm_nonneg _)

/-- **Convolution with a probability kernel does not increase a convex integral of the norm.**
If `Φ` is convex and monotone on `[0, ∞)` and `ρ` is a probability kernel, then
`∫ Φ(‖ρ ⋆ g‖) ≤ ∫ Φ(‖g‖)`, in extended nonnegative form. -/
theorem lintegral_ofReal_map_norm_convolution_le (hΦ : ConvexOn ℝ (Ici 0) Φ)
    (hΦm : MonotoneOn Φ (Ici 0)) (hρ0 : 0 ≤ᵐ[μ] ρ) (hρ1 : ∫ t, ρ t ∂μ = 1) {g : G → F}
    (hg : AEStronglyMeasurable g μ) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖(ρ ⋆[lsmul ℝ ℝ, μ] g) x‖) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (Φ ‖g x‖) ∂μ := by
  -- Integrate the pointwise bound, then use Tonelli's theorem and right invariance of `μ`.
  have hρm : AEMeasurable (fun t => ENNReal.ofReal (ρ t)) μ :=
    (integrable_of_integral_eq_one hρ1).aemeasurable.ennreal_ofReal
  have hm : AEMeasurable (Function.uncurry fun x t =>
      ENNReal.ofReal (ρ t) * ENNReal.ofReal (Φ ‖g (x - t)‖)) (μ.prod μ) := by
    simp_rw [Function.uncurry_def, ← ofReal_posExt_norm (Φ := Φ)]
    refine AEMeasurable.mul (hρm.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))) ?_
    exact ((continuous_posExt hΦ hΦm).comp_aestronglyMeasurable
      (hg.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant μ μ)).norm).aemeasurable.ennreal_ofReal
  calc ∫⁻ x, ENNReal.ofReal (Φ ‖(ρ ⋆[lsmul ℝ ℝ, μ] g) x‖) ∂μ
      ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (ρ t) * ENNReal.ofReal (Φ ‖g (x - t)‖) ∂μ ∂μ :=
        lintegral_mono (hΦ.ofReal_map_norm_convolution_le_lintegral hΦm hρ0 hρ1 hg)
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (ρ t) * ENNReal.ofReal (Φ ‖g (x - t)‖) ∂μ ∂μ :=
        lintegral_lintegral_swap hm
    _ = ∫⁻ t, ENNReal.ofReal (ρ t) * ∫⁻ x, ENNReal.ofReal (Φ ‖g x‖) ∂μ ∂μ := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (Φ ‖g x‖)) t]
    _ = ∫⁻ x, ENNReal.ofReal (Φ ‖g x‖) ∂μ := by
        rw [lintegral_mul_const'' _ hρm, TauCeti.MeasureTheory.lintegral_ofReal_eq_one hρ0 hρ1,
          one_mul]

end ConvexOn
