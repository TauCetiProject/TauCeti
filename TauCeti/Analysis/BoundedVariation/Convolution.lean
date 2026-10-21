/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import TauCeti.Analysis.BoundedVariation.TotalVariation
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.BoundedVariation.Translation
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Total variation of a convolution

Convolving with an integrable kernel `ρ` averages the translates `u (· - t)` of a function with
weights `ρ t`. Each translate has total variation at most `|Du|(Ω)` on an open set `Ω'` with
`Ω' - tsupport ρ ⊆ Ω`, so the convolution satisfies the convolution estimate

`|D(ρ ⋆ u)|(Ω') ≤ ‖ρ‖₁ |Du|(Ω)`.

For a normalized smooth bump the factor `‖ρ‖₁` is one. On the whole space the estimate combines
with lower semicontinuity under `L¹_loc` convergence: the variations of the mollifications of a
locally integrable function converge to its variation. Since a mollification is smooth, its
variation is the integral of the norm of its gradient. Thus every locally integrable function `u`
on the whole space satisfies `|Du|(E) = lim ∫ ‖∇(ρ_ε ⋆ u)‖`, where `|Du|(E)` is the variational
supremum `TauCeti.totalVariationOn`, finite or infinite. For integrable `u` the mollifications
also converge to `u` in `L¹` (`TauCeti.tendsto_eLpNorm_normed_convolution_sub`), so they are a
strict approximation of `u` by smooth functions on the whole space.

The convolution estimate holds for every s-finite right-invariant measure. The limit statements
use an additive Haar measure, against which the normalized bumps have integral one.

## Main results

* `TauCeti.totalVariationOn_convolution_le`: the convolution estimate
  `|D(ρ ⋆ u)|(Ω') ≤ ‖ρ‖₁ |Du|(Ω)` when `Ω' - tsupport ρ ⊆ Ω`.
* `TauCeti.totalVariationOn_normed_convolution_le`: mollification by a normalized bump of outer
  radius `r` does not increase variation from `Ω` to any open set whose closed `r`-neighbourhood
  lies in `Ω`.
* `TauCeti.tendsto_totalVariationOn_normed_convolution`: on the whole space, the variations of
  mollifications with shrinking radii converge to the variation of the function.
* `TauCeti.tendsto_lintegral_enorm_fderiv_normed_convolution`: the same limit written as the
  integrals `∫ ‖∇(ρ_ε ⋆ u)‖` of the smooth mollifications.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.2.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Filter Metric Set TopologicalSpace TestFunction ContinuousLinearMap
open scoped ENNReal Convolution Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω Ω' : Opens E} {u ρ : E → ℝ}

/-- **The convolution estimate for total variation.** If `ρ` is integrable with compact support
and every translate `Ω' - t` with `t ∈ tsupport ρ` lies in `Ω`, then convolving a function locally
integrable on `Ω` with `ρ` gives `|D(ρ ⋆ u)|(Ω') ≤ ‖ρ‖₁ |Du|(Ω)`. -/
theorem totalVariationOn_convolution_le [SFinite μ] [μ.IsAddRightInvariant]
    (hρ : Integrable ρ μ) (hρc : HasCompactSupport ρ)
    (hu : LocallyIntegrableOn u Ω μ) (hΩ : ∀ t ∈ tsupport ρ, ∀ x ∈ Ω', x - t ∈ Ω) :
    totalVariationOn μ Ω' (ρ ⋆[lsmul ℝ ℝ, μ] u) ≤
      (∫⁻ t, ‖ρ t‖ₑ ∂μ) * totalVariationOn μ Ω u := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  set ψ := divergenceCLM φ
  -- For `t ∈ tsupport ρ`, the pairing of the translate `u (· - t)` with `φ` is controlled by the
  -- variation on `Ω`.
  have htrans (t : E) (ht : t ∈ tsupport ρ) :
      ‖∫ x, ψ x * u (x - t) ∂μ‖ₑ ≤ totalVariationOn μ Ω u := by
    rw [Real.enorm_eq_ofReal_abs]
    simp_rw [sub_eq_add_neg]
    exact (ofReal_abs_integral_le_totalVariationOn φ hφ).trans
      (totalVariationOn_comp_add_right_le fun x hx => by
        simpa [sub_eq_add_neg] using hΩ t ht x hx)
  -- Only the values of `u` on the compact set `L = tsupport ψ - tsupport ρ ⊆ Ω` enter the
  -- pairing, and `u` is integrable there.
  set K := tsupport ψ
  set S := tsupport ρ
  set L := (fun p : E × E => p.1 - p.2) '' (K ×ˢ S)
  have hL : IsCompact L := (ψ.hasCompactSupport.isCompact.prod hρc.isCompact).image
    (by fun_prop)
  have hLΩ : L ⊆ Ω := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact hΩ t ht x (ψ.tsupport_subset hx)
  set w := L.indicator u
  have hw : Integrable w μ :=
    (hu.integrableOn_compact_subset hLΩ hL).integrable_indicator hL.measurableSet
  have hkey (x t : E) : ψ x * (ρ t * u (x - t)) = ψ x * (ρ t * w (x - t)) := by
    by_cases hx : ψ x = 0
    · simp [hx]
    by_cases ht : ρ t = 0
    · simp [ht]
    have hxt : x - t ∈ L := mem_image_of_mem (fun p : E × E => p.1 - p.2)
      (mk_mem_prod (subset_tsupport _ hx) (subset_tsupport _ ht))
    simp only [w, indicator_of_mem hxt]
  have hint : Integrable (fun p : E × E => ψ p.1 * (ρ p.2 * w (p.1 - p.2))) (μ.prod μ) := by
    obtain ⟨C, hC⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
    exact (hρ.convolution_integrand (lsmul ℝ ℝ) hw).bdd_mul
      (ψ.continuous.comp continuous_fst).aestronglyMeasurable (.of_forall fun p => hC p.1)
  -- Fubini: `∫ ψ (ρ ⋆ u) = ∫ ρ t (∫ ψ x u (x - t) dx) dt`.
  have hfubini : ∫ x, ψ x * (ρ ⋆[lsmul ℝ ℝ, μ] u) x ∂μ =
      ∫ t, ρ t * ∫ x, ψ x * u (x - t) ∂μ ∂μ := by
    calc ∫ x, ψ x * (ρ ⋆[lsmul ℝ ℝ, μ] u) x ∂μ
        = ∫ x, ∫ t, ψ x * (ρ t * w (x - t)) ∂μ ∂μ := by
          refine integral_congr_ae (.of_forall fun x => ?_)
          simp only [convolution_lsmul, smul_eq_mul, ← integral_const_mul, hkey]
      _ = ∫ t, ∫ x, ψ x * (ρ t * w (x - t)) ∂μ ∂μ := integral_integral_swap hint
      _ = ∫ t, ρ t * ∫ x, ψ x * u (x - t) ∂μ ∂μ := by
          refine integral_congr_ae (.of_forall fun t => ?_)
          simp only [← hkey, ← integral_const_mul, mul_left_comm (ρ t)]
  rw [hfubini]
  calc ENNReal.ofReal (∫ t, ρ t * ∫ x, ψ x * u (x - t) ∂μ ∂μ)
      ≤ ‖∫ t, ρ t * ∫ x, ψ x * u (x - t) ∂μ ∂μ‖ₑ := Real.ofReal_le_enorm _
    _ ≤ ∫⁻ t, ‖ρ t‖ₑ * ‖∫ x, ψ x * u (x - t) ∂μ‖ₑ ∂μ := by
        simpa only [enorm_mul] using
          enorm_integral_le_lintegral_enorm fun t => ρ t * ∫ x, ψ x * u (x - t) ∂μ
    _ ≤ ∫⁻ t, ‖ρ t‖ₑ * totalVariationOn μ Ω u ∂μ := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ tsupport ρ
        · exact mul_le_mul_right (htrans t ht) _
        · simp [image_eq_zero_of_notMem_tsupport ht]
    _ = (∫⁻ t, ‖ρ t‖ₑ ∂μ) * totalVariationOn μ Ω u :=
        lintegral_mul_const'' _ hρ.aemeasurable.enorm

variable [μ.IsAddHaarMeasure]

/-- **Mollification does not increase variation.** For a normalized smooth bump `φ` of outer
radius `r`, if the closed ball of radius `r` about every point of `Ω'` lies in `Ω`, then
`|D(φ ⋆ u)|(Ω') ≤ |Du|(Ω)` for every `u` locally integrable on `Ω`. -/
theorem totalVariationOn_normed_convolution_le (φ : ContDiffBump (0 : E))
    (hu : LocallyIntegrableOn u Ω μ) (hΩ : ∀ x ∈ Ω', closedBall x φ.rOut ⊆ Ω) :
    totalVariationOn μ Ω' (φ.normed μ ⋆[lsmul ℝ ℝ, μ] u) ≤ totalVariationOn μ Ω u := by
  have hnorm : ∫⁻ t, ‖φ.normed μ t‖ₑ ∂μ = 1 := by
    simp_rw [Real.enorm_of_nonneg (φ.nonneg_normed _)]
    rw [← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
      (.of_forall φ.nonneg_normed), φ.integral_normed, ENNReal.ofReal_one]
  simpa [hnorm] using totalVariationOn_convolution_le φ.integrable_normed
    φ.hasCompactSupport_normed hu fun t ht x hx => hΩ x hx <| by
      rw [φ.tsupport_normed_eq, mem_closedBall_zero_iff] at ht
      simpa [dist_eq_norm] using ht

/-- **Mollification approximates the variation on the whole space.** For a locally integrable
function `u` and normalized smooth bumps `φ i` whose outer radii tend to zero, the variations of
the mollifications `φ i ⋆ u` on the whole space converge to the variation of `u`, finite or
infinite. -/
theorem tendsto_totalVariationOn_normed_convolution {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : E)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hu : LocallyIntegrable u μ) :
    Tendsto (fun i => totalVariationOn μ ⊤ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] u)) l
      (𝓝 (totalVariationOn μ ⊤ u)) := by
  rcases l.eq_or_neBot with rfl | _
  · exact tendsto_bot
  refine tendsto_of_le_liminf_of_limsup_le ?_ (limsup_le_of_le (h := .of_forall fun i =>
    totalVariationOn_normed_convolution_le (φ i) (hu.locallyIntegrableOn _) fun _ _ =>
      subset_univ _))
  exact totalVariationOn_le_liminf
    (.of_forall fun i => ((φ i).hasCompactSupport_normed.continuous_convolution_left _
      (φ i).continuous_normed hu).locallyIntegrable.locallyIntegrableOn _)
    (hu.locallyIntegrableOn _)
    fun K hK _ => tendsto_setLIntegral_enorm_normed_convolution_sub hφ hu hK

/-- **The variation as a limit of gradient integrals.** For a locally integrable function `u` on
the whole space and normalized smooth bumps `φ i` whose outer radii tend to zero, the integrals
`∫ ‖∇(φ i ⋆ u)‖` of the smooth mollifications converge to the variation `|Du|(E)`, finite or
infinite. -/
theorem tendsto_lintegral_enorm_fderiv_normed_convolution {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : E)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hu : LocallyIntegrable u μ) :
    Tendsto (fun i => ∫⁻ x, ‖fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] u) x‖ₑ ∂μ) l
      (𝓝 (totalVariationOn μ ⊤ u)) := by
  refine (tendsto_totalVariationOn_normed_convolution hφ hu).congr fun i => ?_
  have hsmooth : ContDiff ℝ 1 ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] u) :=
    (φ i).hasCompactSupport_normed.contDiff_convolution_left _
      ((φ i).contDiff_normed (n := 1)) hu
  rw [hsmooth.locallyLipschitz.locallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv,
    Opens.coe_top, Measure.restrict_univ]

end TauCeti
