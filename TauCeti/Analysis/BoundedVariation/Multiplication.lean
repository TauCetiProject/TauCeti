/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.TotalVariation

/-!
# Multiplication of a function of bounded variation by a smooth function

Let `Ω` be an open set of a finite-dimensional real inner product space `E`. For a smooth `χ`
with `|χ| ≤ c`, this file bounds the total variation of `χ u` by

`|D(χ u)|(Ω') ≤ c |Du|(Ω) + ∫_{Ω'} ‖Dχ‖ |u|`

whenever `tsupport χ ∩ Ω' ⊆ Ω`, by the product rule `div (χ φ) = χ div φ + Dχ φ` for test vector
fields. With a smooth cutoff supported in `Ω` and `Ω'` the whole space, this turns a function of
bounded variation on `Ω` into one of bounded variation on the whole space.

## Main results

* `TauCeti.totalVariationOn_mul_le`: the variation of `χ u` for a smooth bounded `χ`.
* `TauCeti.totalVariationOn_top_mul_le`: the variation on the whole space of `χ u` for a smooth
  cutoff `χ` supported in `Ω` with bounded derivative.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Function Set TopologicalSpace TestFunction
open scoped ENNReal ContDiff Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {u : E → ℝ}

/-- **Multiplication by a smooth function.** Let `χ` be smooth with `|χ| ≤ c`, and let `Ω'` be an
open set with `tsupport χ ∩ Ω' ⊆ Ω`. Every `u` locally integrable on `Ω` satisfies

`|D(χ u)|(Ω') ≤ c |Du|(Ω) + ∫_{Ω'} ‖Dχ‖ |u|`.

For `Ω' = Ω` this is the Leibniz bound on `Ω`. For a cutoff with `tsupport χ ⊆ Ω` and `Ω'` the
whole space, it bounds the variation on the whole space of `χ u`, which vanishes off `Ω`. -/
theorem totalVariationOn_mul_le {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) {c : ℝ}
    (hχc : ∀ x, |χ x| ≤ c) {Ω' : Opens E} (hΩ' : tsupport χ ∩ Ω' ⊆ Ω)
    (hu : LocallyIntegrableOn u Ω μ) :
    totalVariationOn μ Ω' (χ * u) ≤
      ENNReal.ofReal c * totalVariationOn μ Ω u + ∫⁻ x in Ω', ‖fderiv ℝ χ x‖ₑ * ‖u x‖ₑ ∂μ := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  have hφd : ContDiff ℝ ∞ (φ : E → E) := φ.contDiff
  -- The test vector field `χ φ` and the test function `Dχ φ` on `Ω`.
  let χφ : 𝓓(Ω, E) := ⟨fun x => χ x • φ x, hχ.smul hφd, φ.hasCompactSupport.smul_left,
    (subset_inter (tsupport_smul_subset_left _ _) (tsupport_smul_subset_right _ _)).trans
      ((inter_subset_inter_right _ φ.tsupport_subset).trans hΩ')⟩
  have hsupp : support (fun x => fderiv ℝ χ x (φ x)) ⊆ support (fderiv ℝ χ) ∩ support φ :=
    fun x hx => ⟨fun h0 => hx (by simp [h0]), fun h0 => hx (by simp [h0])⟩
  let a : 𝓓(Ω, ℝ) := ⟨fun x => fderiv ℝ χ x (φ x), (hχ.fderiv_right le_rfl).clm_apply hφd,
    φ.hasCompactSupport.mono fun x hx => (hsupp hx).2,
    (closure_mono hsupp |>.trans (closure_inter_subset_inter_closure _ _)).trans
      ((inter_subset_inter (tsupport_fderiv_subset ℝ) φ.tsupport_subset).trans hΩ')⟩
  have hχφ_apply : (χφ : E → E) = fun x => χ x • φ x := rfl
  have ha : (a : E → ℝ) = fun x => fderiv ℝ χ x (φ x) := rfl
  -- The product rule `div (χ φ) = χ div φ + Dχ φ`.
  have hdiv (x : E) : divergenceCLM χφ x = χ x * divergenceCLM φ x + a x := by
    rw [divergenceCLM_apply, divergenceCLM_apply, hχφ_apply, ha,
      trace_fderiv_smul (hχ.differentiable (by simp) x) (hφd.differentiable (by simp) x)]
  have hχφ (x : E) : ‖χφ x‖ ≤ c := by
    rw [hχφ_apply, norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hφ x)).trans (hχc x)
  have hint (ψ : 𝓓(Ω, ℝ)) : Integrable (fun x => ψ x * u x) μ := by
    simpa using integrable_smul_of_locallyIntegrableOn hu ψ
  have hsplit : ∫ x, divergenceCLM φ x * (χ * u) x ∂μ =
      ∫ x, divergenceCLM χφ x * u x ∂μ - ∫ x, a x * u x ∂μ := by
    rw [← integral_sub (hint _) (hint a)]
    congr 1 with x
    rw [hdiv, Pi.mul_apply]
    ring
  -- The remainder `∫ Dχ φ u` is at most `∫_{Ω'} ‖Dχ‖ |u|`.
  have hrem : ENNReal.ofReal |∫ x, a x * u x ∂μ| ≤
      ∫⁻ x in Ω', ‖fderiv ℝ χ x‖ₑ * ‖u x‖ₑ ∂μ := by
    rw [← Real.enorm_eq_ofReal_abs, ← lintegral_indicator Ω'.isOpen.measurableSet]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
    by_cases hx : x ∈ (Ω' : Set E)
    · rw [indicator_of_mem hx, enorm_mul]
      gcongr
      rw [ha, ← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal <| ((fderiv ℝ χ x).le_opNorm _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (hφ x))
    · have hφx : φ x = 0 :=
        image_eq_zero_of_notMem_tsupport fun hmem => hx (φ.tsupport_subset hmem)
      simp [ha, hφx, hx]
  rw [hsplit]
  calc ENNReal.ofReal (∫ x, divergenceCLM χφ x * u x ∂μ - ∫ x, a x * u x ∂μ)
      ≤ ENNReal.ofReal (∫ x, divergenceCLM χφ x * u x ∂μ) +
          ENNReal.ofReal |∫ x, a x * u x ∂μ| := by
        refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
        linarith [neg_abs_le (∫ x, a x * u x ∂μ)]
    _ ≤ _ := add_le_add (ofReal_integral_le_mul_totalVariationOn χφ hχφ) hrem

/-- **Variation of a cut-off function on the whole space.** If `χ` is smooth with `|χ| ≤ c`,
`‖Dχ‖ ≤ C` and `tsupport χ ⊆ Ω`, then every `u` locally integrable on `Ω` satisfies
`|D(χ u)|(E) ≤ c |Du|(Ω) + C ∫_Ω |u|`. -/
theorem totalVariationOn_top_mul_le {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) {c : ℝ}
    (hχc : ∀ x, |χ x| ≤ c) (hχΩ : tsupport χ ⊆ Ω) {C : ℝ} (hC : ∀ x, ‖fderiv ℝ χ x‖ ≤ C)
    (hu : LocallyIntegrableOn u Ω μ) :
    totalVariationOn μ ⊤ (χ * u) ≤
      ENNReal.ofReal c * totalVariationOn μ Ω u + ENNReal.ofReal C * ∫⁻ x in Ω, ‖u x‖ₑ ∂μ := by
  refine (totalVariationOn_mul_le hχ hχc (Ω' := ⊤) (by simpa using hχΩ) hu).trans
    (add_le_add le_rfl ?_)
  rw [Opens.coe_top, Measure.restrict_univ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator Ω.isOpen.measurableSet]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ (Ω : Set E)
  · rw [indicator_of_mem hx, ← ofReal_norm]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hC x)) le_rfl
  · have h0 : fderiv ℝ χ x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hmem => hx (hχΩ (tsupport_fderiv_subset ℝ hmem))
    rw [indicator_of_notMem hx, h0, ← ofReal_norm, norm_zero, ENNReal.ofReal_zero, zero_mul]

end TauCeti
