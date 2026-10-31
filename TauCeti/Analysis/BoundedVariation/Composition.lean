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

The central formal inputs are `TauCeti.exists_mollifier_seq_of_isCompact_closure` and
`TauCeti.totalVariationOn_le_liminf`. The shared compact localization lemma extracts the
mollification argument from `TauCeti.Analysis.BoundedVariation.Coarea`.

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
  obtain ⟨w, hw, hconv, hvar⟩ := exists_mollifier_seq_of_isCompact_closure hu hc hsub
  -- The Lipschitz estimate transports convergence in local `L¹` through `g`.
  have hlim (A : Set E) (hA : IsCompact A) (hAΩ' : A ⊆ Ω') :
      Tendsto (fun n => ∫⁻ x in A, ‖(g ∘ w n) x - (g ∘ u) x‖ₑ ∂μ) atTop (𝓝 0) := by
    have hlim := hconv A hA (hAΩ'.trans subset_closure)
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
    ((hu.mono_set (subset_closure.trans hsub)).comp_lipschitz hg)
    hlim).trans (liminf_le_of_frequently_le' (Filter.Eventually.frequently ?_))
  filter_upwards [hvar] with n hn
  refine (totalVariationOn_comp_le_of_contDiff (hw n) hg).trans ?_
  gcongr

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
