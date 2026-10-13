/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Rademacher
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Calculus.LineDeriv.Measurable
import TauCeti.Analysis.Sobolev.DifferenceQuotient

/-!
# Locally Lipschitz functions are weakly differentiable

Let `u : E → F` be locally Lipschitz on an open subset `Ω` of a finite-dimensional real normed
space `E`, and let `μ` be an additive Haar measure. If `u` has line derivative `u' x` in the
direction `v` at almost every `x ∈ Ω`, then `u'` is the weak derivative of `u` in the direction
`v` on `Ω` (`LocallyLipschitzOn.hasWeakLineDerivOn`). In the same way an almost-everywhere
Fréchet derivative is the weak one (`LocallyLipschitzOn.hasWeakFDerivOn`), and when `F` is
finite-dimensional, Rademacher's theorem supplies it: `fderiv ℝ u` is the weak derivative of `u`
on `Ω` (`LocallyLipschitzOn.hasWeakFDerivOn_fderiv`). Near each point this weak derivative is
bounded by a local Lipschitz constant (`norm_fderiv_le_of_lipschitzOn`).

No regularity of `u` beyond the local Lipschitz bound is used, and the codomain `F` is an
arbitrary Banach space: the derivative is only assumed to exist almost everywhere. This is what a
change of variables by a Lipschitz map, such as the flattening of the region above a Lipschitz
graph, needs: composed with such a map, a smooth function is only locally Lipschitz.

## The argument

For a test function `φ`, the difference quotients `t⁻¹ (u (x + t • v) - u x)` paired with `φ`
converge to `-∫ ∂_v φ • u` (`TauCeti.integral_inv_mul_sub_mul_tendsto_neg_integral_lineDeriv_mul`,
for real `u`). On a compact neighbourhood of the support of `φ` inside `Ω`, `u` is Lipschitz, so
the difference quotients are bounded there by a multiple of `‖v‖`, and they converge to `u'`
almost everywhere; by dominated convergence the same pairing tends to `∫ φ • u'`. Measurability
and local integrability of `u'` come from
`LocallyLipschitzOn.locallyIntegrableOn_of_ae_hasLineDerivAt`. A vector-valued
`u` is reduced to the real case by testing the identity against continuous linear functionals.

## Main declarations

* `LocallyLipschitzOn.hasWeakLineDerivOn`: an almost-everywhere line derivative of a locally
  Lipschitz function is its weak derivative.
* `LocallyLipschitzOn.hasWeakFDerivOn`: the same for an almost-everywhere Fréchet derivative.
* `LocallyLipschitzOn.hasWeakFDerivOn_fderiv`: for a finite-dimensional codomain, `fderiv ℝ u` is
  the weak derivative.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  §4.2.3, Theorem 4.5 and §3.1.2 (Rademacher's theorem).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.2, Theorem 4.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Topology Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {v : E} {u u' : E → F}

/-- The real case of `LocallyLipschitzOn.hasWeakLineDerivOn`, as an integration-by-parts identity:
the difference quotients of `g` paired with `φ` converge both to `-∫ ∂_v φ * g` and, by dominated
convergence, to `∫ g' * φ`. -/
private theorem integral_mul_eq_neg_integral_lineDeriv_mul {g g' : E → ℝ}
    (hg : LocallyLipschitzOn Ω g) (h : ∀ᵐ x ∂μ, x ∈ Ω → HasLineDerivAt ℝ g (g' x) x v)
    (φ : 𝓓(Ω, ℝ)) :
    ∫ x, g' x * φ x ∂μ = -∫ x, lineDeriv ℝ (φ : E → ℝ) x v * g x ∂μ := by
  have hgi := hg.continuousOn.locallyIntegrableOn (μ := μ) Ω.isOpen.measurableSet
  have hK : IsCompact (tsupport (φ : E → ℝ)) := φ.hasCompactSupport.isCompact
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen φ.tsupport_subset
  obtain ⟨C, hC⟩ := (hg.mono hδΩ).exists_lipschitzOnWith_of_compact hK.cthickening
  obtain ⟨w, hw, hwS, hwt⟩ := exists_integrable_eqOn_tsupport_add hgi φ v
  refine tendsto_nhds_unique (tendsto_integral_filter_of_dominated_convergence
    (fun x => C * ‖v‖ * ‖φ x‖) ?_ ?_ ?_ ?_)
    (integral_inv_mul_sub_mul_tendsto_neg_integral_lineDeriv_mul hgi φ v)
  · -- For small `t` the difference quotient only sees `g` where it agrees with the integrable `w`.
    filter_upwards [hwt] with t ht
    have hpt : (fun x => t⁻¹ * (g (x + t • v) - g x) * φ x) =
        fun x => t⁻¹ * (w (x + t • v) - w x) * φ x := by
      funext x
      by_cases hx : x ∈ tsupport (φ : E → ℝ)
      · rw [ht x hx, hwS hx]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    rw [hpt]
    exact ((((hw.comp_add_right (t • v)).aestronglyMeasurable.sub
      hw.aestronglyMeasurable).const_mul _).mul φ.continuous.aestronglyMeasurable)
  · -- For `|t| ‖v‖ ≤ δ`, both `x` and `x + t • v` lie where `g` is `C`-Lipschitz.
    have htend : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const v
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (htend.eventually (closedBall_mem_nhds 0 hδ))] with t ht0 ht
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ tsupport (φ : E → ℝ)
    · have hxt : x + t • v ∈ cthickening δ (tsupport (φ : E → ℝ)) :=
        mem_cthickening_of_dist_le _ x δ _ hx (by simpa [dist_eq_norm] using ht)
      have hlip := hC.norm_sub_le hxt (self_subset_cthickening _ hx)
      rw [add_sub_cancel_left, norm_smul] at hlip
      have ht0' : 0 < ‖t‖ := norm_pos_iff.2 ht0
      have hq : ‖t‖⁻¹ * ‖g (x + t • v) - g x‖ ≤ C * ‖v‖ := by
        rw [inv_mul_le_iff₀ ht0']
        linarith
      rw [norm_mul, norm_mul, norm_inv]
      exact mul_le_mul_of_nonneg_right hq (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · exact ((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm.const_mul _)
  · filter_upwards [h] with x hx
    by_cases hxΩ : x ∈ (Ω : Set E)
    · simpa [smul_eq_mul] using (hx hxΩ).tendsto_slope_zero.mul_const (φ x)
    · simp [image_eq_zero_of_notMem_tsupport fun hmem => hxΩ (φ.tsupport_subset hmem)]

/-- **A locally Lipschitz function is weakly differentiable.** If `u` is locally Lipschitz on the
open set `Ω` and has line derivative `u' x` in the direction `v` at almost every `x ∈ Ω`, then
`u'` is the weak derivative of `u` in the direction `v` on `Ω`. -/
theorem _root_.LocallyLipschitzOn.hasWeakLineDerivOn [CompleteSpace F]
    (hu : LocallyLipschitzOn Ω u) (h : ∀ᵐ x ∂μ, x ∈ Ω → HasLineDerivAt ℝ u (u' x) x v) :
    HasWeakLineDerivOn μ Ω u u' v := by
  have hui := hu.continuousOn.locallyIntegrableOn (μ := μ) Ω.isOpen.measurableSet
  have hu'i := hu.locallyIntegrableOn_of_ae_hasLineDerivAt (μ := μ) Ω.isOpen h
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance, hui, hu'i, fun φ => ?_⟩
  -- Test the identity against every continuous linear functional `ℓ`, reducing to `ℓ ∘ u`.
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun ℓ => ?_
  have hℓ : LocallyLipschitzOn Ω fun x => ℓ (u x) := fun x hx => by
    obtain ⟨C, s, hs, hC⟩ := hu hx
    exact ⟨‖ℓ‖₊ * C, s, hs, ℓ.lipschitzWith.comp_lipschitzOnWith hC⟩
  have key := integral_mul_eq_neg_integral_lineDeriv_mul hℓ
    (h.mono fun x hx hxΩ => (ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hx hxΩ) :)) φ
  rw [map_neg, ← ℓ.integral_comp_comm (integrable_lineDeriv_smul_of_locallyIntegrableOn hui φ v),
    ← ℓ.integral_comp_comm (integrable_smul_of_locallyIntegrableOn hu'i φ)]
  simp only [map_smul, smul_eq_mul]
  have hc : ∫ x, (φ : E → ℝ) x * ℓ (u' x) ∂μ = ∫ x, ℓ (u' x) * (φ : E → ℝ) x ∂μ := by
    simp_rw [mul_comm]
  rw [hc, key, neg_neg]

/-- **A locally Lipschitz function is weakly differentiable.** If `u` is locally Lipschitz on the
open set `Ω` and has Fréchet derivative `U x` at almost every `x ∈ Ω`, then `U` is the weak
derivative of `u` on `Ω`. -/
theorem _root_.LocallyLipschitzOn.hasWeakFDerivOn [CompleteSpace F] {U : E → E →L[ℝ] F}
    (hu : LocallyLipschitzOn Ω u) (h : ∀ᵐ x ∂μ, x ∈ Ω → HasFDerivAt u (U x) x) :
    HasWeakFDerivOn μ Ω u U := hasWeakFDerivOn_iff.2 fun v =>
  hu.hasWeakLineDerivOn (h.mono fun _ hx hxΩ => (hx hxΩ).hasLineDerivAt v)

/-- **A locally Lipschitz function has its derivative as weak derivative.** A function between
finite-dimensional real normed spaces that is locally Lipschitz on the open set `Ω` has
`fderiv ℝ u` as its weak derivative on `Ω`; by Rademacher's theorem it is differentiable almost
everywhere there. -/
theorem _root_.LocallyLipschitzOn.hasWeakFDerivOn_fderiv [FiniteDimensional ℝ F]
    (hu : LocallyLipschitzOn Ω u) : HasWeakFDerivOn μ Ω u (fderiv ℝ u) :=
  hu.hasWeakFDerivOn ((hu.ae_differentiableAt_of_mem Ω.isOpen).mono fun _ hx hxΩ =>
    (hx hxΩ).hasFDerivAt)

end TauCeti
