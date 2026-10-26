/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Space
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.Calculus.FDeriv.NormComparison
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Lipschitz composition of functions of bounded variation

For a real function locally integrable on an arbitrary Euclidean open set and a `C`-Lipschitz
scalar map `g`, composition satisfies `|D(g ∘ u)|(Ω) ≤ C |Du|(Ω)`. This is a variation inequality;
it allows jumps and does not assert the classical chain rule for the derivative measure.

The estimate uses the variational total variation `TauCeti.totalVariationOn`. Local
mollification, its variation bound, and lower semicontinuity extend the derivative estimate
from smooth inner functions to locally integrable functions. Neither finite variation nor
finite volume is required for the inequality. BV membership additionally needs integrability
of the composite; the condition `g 0 = 0` supplies it on domains of arbitrary volume.

The central formal inputs are `ContDiffBump.totalVariationOn_normed_convolution_le` and
`TauCeti.totalVariationOn_le_liminf`. Compact localization follows the mollification argument
in `TauCeti.Analysis.BoundedVariation.Coarea`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Chapter 3 (approximation and composition).
-/

public section

noncomputable section

open MeasureTheory Filter Metric Set TopologicalSpace TestFunction ContinuousLinearMap
open scoped ENNReal NNReal Convolution Topology Distributions

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : Opens E} {u : E → ℝ} {g : ℝ → ℝ} {C : ℝ≥0}

private theorem totalVariationOn_comp_le_of_contDiff (hu : ContDiff ℝ 1 u)
    (hg : LipschitzWith C g) :
    totalVariationOn μ Ω (g ∘ u) ≤ C * totalVariationOn μ Ω u := by
  have hcomp := (hg.locallyLipschitz.comp hu.locallyLipschitz).locallyLipschitzOn (s := Ω)
  rw [hcomp.totalVariationOn_eq_setLIntegral_enorm_fderiv,
    hu.locallyLipschitz.locallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun x => ?_
  simpa only [← ofReal_norm, ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal] using
    ENNReal.ofReal_le_ofReal (hg.norm_fderiv_comp_le (hu.differentiable one_ne_zero x))

private theorem totalVariationOn_comp_le_of_isCompact_closure
    (hu : LocallyIntegrableOn u Ω μ) (hg : LipschitzWith C g) {Ω' : Opens E}
    (hc : IsCompact (closure (Ω' : Set E))) (hsub : closure (Ω' : Set E) ⊆ Ω) :
    totalVariationOn μ Ω' (g ∘ u) ≤ C * totalVariationOn μ Ω u := by
  -- Localize `u` to a compact neighbourhood of `Ω'` before mollifying it.
  obtain ⟨δ, hδ, hδΩ⟩ := hc.exists_cthickening_subset_open Ω.isOpen hsub
  set K := cthickening (δ / 2) (closure (Ω' : Set E))
  have hK : IsCompact K := hc.cthickening
  have hKΩ : K ⊆ Ω := (cthickening_mono (by linarith) _).trans hδΩ
  let V : Opens E := ⟨thickening (δ / 2) (closure (Ω' : Set E)), isOpen_thickening⟩
  have hVK : (V : Set E) ⊆ K := thickening_subset_cthickening _ _
  have hball (x : E) (hx : x ∈ Ω') : closedBall x (δ / 4) ⊆ V :=
    (closedBall_subset_ball (by linarith)).trans (ball_subset_thickening (subset_closure hx) _)
  let u' := K.indicator u
  have hu'u (x : E) (hx : x ∈ K) : u' x = u x := indicator_of_mem hx u
  have hu' : LocallyIntegrable u' μ :=
    ((hu.integrableOn_compact_subset hKΩ hK).integrable_indicator
      hK.measurableSet).locallyIntegrable
  let φ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨1 / (n + 2), 1 / (n + 1), by positivity, by gcongr; norm_num⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let w : ℕ → E → ℝ := fun n => (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] u'
  have hw (n : ℕ) : ContDiff ℝ 1 (w n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed hu'
  -- The Lipschitz estimate transports convergence in local `L¹` through `g`.
  have hlim (A : Set E) (hA : IsCompact A) (hAΩ' : A ⊆ Ω') :
      Tendsto (fun n => ∫⁻ x in A, ‖(g ∘ w n) x - (g ∘ u) x‖ₑ ∂μ) atTop (𝓝 0) := by
    have hAu : EqOn u' u A := fun x hx => hu'u x
      (self_subset_cthickening _ (subset_closure (hAΩ' hx)))
    have hlim := (tendsto_setLIntegral_enorm_normed_convolution_sub hφ hu' hA).congr
      fun n => setLIntegral_congr_fun hA.measurableSet fun x hx => by rw [hAu hx]
    have hscale := ENNReal.Tendsto.const_mul hlim (a := (C : ℝ≥0∞))
      (Or.inr ENNReal.coe_ne_top)
    rw [mul_zero] at hscale
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscale
      (fun _ => zero_le) fun n => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    exact lintegral_mono fun x => by
      simpa only [Function.comp_apply, ← edist_eq_enorm_sub] using hg (w n x) (u x)
  -- Lower semicontinuity passes the smooth-inner-function estimate to `u`.
  have hli (n : ℕ) : LocallyIntegrableOn (g ∘ w n) Ω' μ :=
    (hg.continuous.comp (hw n).continuous).locallyIntegrable.locallyIntegrableOn _
  refine (totalVariationOn_le_liminf
    (.of_forall hli)
    ((hu.mono_set (subset_closure.trans hsub)).comp_lipschitz hg Ω'.isOpen.isLocallyClosed)
    hlim).trans (liminf_le_of_frequently_le' (Filter.Eventually.frequently ?_))
  filter_upwards [hφ.eventually (ge_mem_nhds (show 0 < δ / 4 by positivity))] with n hn
  refine (totalVariationOn_comp_le_of_contDiff (hw n) hg).trans ?_
  gcongr
  calc totalVariationOn μ Ω' (w n) ≤ totalVariationOn μ V u' :=
        (φ n).totalVariationOn_normed_convolution_le (hu'.locallyIntegrableOn _)
          fun x hx => (closedBall_subset_closedBall hn).trans (hball x hx)
    _ = totalVariationOn μ V u := totalVariationOn_congr_ae <|
        (ae_restrict_mem V.isOpen.measurableSet).mono fun x hx => hu'u x (hVK hx)
    _ ≤ totalVariationOn μ Ω u := totalVariationOn_mono fun x hx => hKΩ (hVK hx)

/-- **Lipschitz composition bounds distributional variation.** For locally integrable `u` on an
open set, `|D(g ∘ u)|(Ω) ≤ C |Du|(Ω)` whenever `g` is `C`-Lipschitz. This includes infinite
variation, arbitrary open domains, and scalar maps that do not vanish at zero. -/
theorem totalVariationOn_comp_lipschitz_le (hu : LocallyIntegrableOn u Ω μ)
    (hg : LipschitzWith C g) :
    totalVariationOn μ Ω (g ∘ u) ≤ C * totalVariationOn μ Ω u := by
  refine totalVariationOn_le_iff.mpr fun ψ hψ => ?_
  obtain ⟨U, hU, hψU, hUΩ, hUc⟩ := exists_open_between_and_isCompact_closure
    ψ.hasCompactSupport.isCompact Ω.isOpen ψ.tsupport_subset
  let V : Opens E := ⟨U, hU⟩
  let ψ' : 𝓓(V, E) := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hψU⟩
  have hψ' (x : E) : divergenceCLM ψ' x = divergenceCLM ψ x := by simp [ψ']
  refine le_trans ?_ (totalVariationOn_comp_le_of_isCompact_closure (Ω' := V) hu hg hUc hUΩ)
  simpa only [hψ'] using ofReal_integral_le_totalVariationOn (μ := μ) (u := g ∘ u) ψ' hψ

/-- Lipschitz composition preserves BV provided the composite is integrable. This hypothesis
allows scalar maps with arbitrary value at zero on domains of infinite volume. -/
theorem MemBV.comp_lipschitz_of_integrable (hu : MemBV μ Ω u) (hg : LipschitzWith C g)
    (hint : IntegrableOn (g ∘ u) Ω μ) : MemBV μ Ω (g ∘ u) := by
  rcases memBV_iff.mp hu with ⟨hu, hvar⟩
  exact memBV_iff.mpr ⟨hint, (totalVariationOn_comp_lipschitz_le hu.locallyIntegrableOn hg).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hvar)⟩

/-- A Lipschitz scalar map vanishing at zero preserves BV, without a finite-volume assumption
on the domain. -/
theorem MemBV.comp_lipschitz (hu : MemBV μ Ω u) (hg : LipschitzWith C g) (hg0 : g 0 = 0) :
    MemBV μ Ω (g ∘ u) := by
  exact hu.comp_lipschitz_of_integrable hg
    (memLp_one_iff_integrable.mp
      (hg.comp_memLp hg0 (memLp_one_iff_integrable.mpr (memBV_iff.mp hu).1)))

end TauCeti
