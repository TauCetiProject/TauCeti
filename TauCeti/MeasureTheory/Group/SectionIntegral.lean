/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.MeasureTheory.Integral.Prod

/-!
# Factoring integrals along a measurable additive section

Let `X` and `Y` be measurable additive commutative groups with s-finite left-invariant measures
`μ` and `ν`, where `ν` is also negation-invariant. Given measurable maps `ι : Y → X` and
`p : X → Y` satisfying `p (ι y + x) = y + p x`, the shear map
`(x, y) ↦ (ι (y - p x) + x, p x)` is a measure-preserving measurable equivalence on `X × Y`.
Consequently, for any measurable set `K ⊆ Y` of `ν`-measure `1`, if a function `f` factors as
`f (ι y + x) = c x * a (y + p x)` whenever `p x ∈ K`, then its integral over `(X, μ)` factors as
`(∫ x in p ⁻¹' K, c x ∂μ) * ∫ y, a y ∂ν` (and similarly for the Lebesgue integral).

## Main statements

* `TauCeti.sectionShearEquiv`: the measurable shear equivalence `(x, y) ↦ (ι (y - p x) + x, p x)`.
* `TauCeti.measurePreserving_sectionShearEquiv`: `sectionShearEquiv` preserves `μ.prod ν`.
* `TauCeti.lintegral_eq_mul_of_section`: factorization of the Lebesgue integral `∫⁻ x, f x ∂μ`.
* `TauCeti.integral_eq_mul_of_section`: factorization of the Bochner integral `∫ x, f x ∂μ`.

## Provenance

Adapted from `New.Floors.integral_eq_mul_of_section` in
`grh/src/Lib/SiegelWeil/OneVector/FinitePlaceDensity.lean` of `grh-lean`
(<https://github.com/lsernau/grh-lean>, commit `72fead102f663d5c7a407964a13dc0cf9d977207`),
splitting out the shear equivalence and its measure-preservation, and adding the `ℝ≥0∞` Lebesgue
integral version.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableAdd₂ X] [MeasurableNeg X]
  [MeasurableAdd₂ Y] [MeasurableNeg Y]

/-- The measurable shear equivalence `(x, y) ↦ (ι (y - p x) + x, p x)` associated to a
measurable section `ι : Y → X` of `p : X → Y` satisfying `p (ι y + x) = y + p x`. -/
def sectionShearEquiv {ι : Y → X} {p : X → Y} (hι : Measurable ι) (hp : Measurable p)
    (h_sec : ∀ (y : Y) (x : X), p (ι y + x) = y + p x) : X × Y ≃ᵐ X × Y where
  toFun q := (ι (q.snd - p q.fst) + q.fst, p q.fst)
  invFun q := (q.fst - ι (p q.fst - q.snd), p q.fst)
  left_inv q := by simp [h_sec]
  right_inv q := by
    have h_sub (x : X) (y : Y) : p (x - ι y) = p x - y := by
      simpa [eq_sub_iff_add_eq'] using (h_sec y (x - ι y)).symm
    simp [h_sub]
  measurable_toFun := by dsimp; fun_prop
  measurable_invFun := by dsimp; fun_prop

/-- The shear equivalence `sectionShearEquiv` preserves the product measure `μ.prod ν` whenever
`μ` and `ν` are s-finite left-invariant measures and `ν` is negation-invariant. -/
theorem measurePreserving_sectionShearEquiv {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] [μ.IsAddLeftInvariant] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
    {ι : Y → X} {p : X → Y} (hι : Measurable ι) (hp : Measurable p)
    (h_sec : ∀ (y : Y) (x : X), p (ι y + x) = y + p x) :
    MeasurePreserving (sectionShearEquiv hι hp h_sec) (μ.prod ν) (μ.prod ν) := by
  have shear₁ : MeasurePreserving (fun q : X × Y ↦ (q.fst, q.snd - p q.fst))
      (μ.prod ν) (μ.prod ν) :=
    (MeasurePreserving.id μ).skew_product (g := fun x y ↦ y - p x) (by fun_prop)
      (.of_forall fun x ↦ map_sub_right_eq_self ν (p x))
  have shear₂ : MeasurePreserving (fun q : Y × X ↦ (q.fst, ι q.fst + q.snd))
      (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product (g := fun y x ↦ ι y + x) (by fun_prop)
      (.of_forall fun y ↦ map_add_left_eq_self μ (ι y))
  have shear₃ : MeasurePreserving (fun q : X × Y ↦ (q.fst, p q.fst - q.snd))
      (μ.prod ν) (μ.prod ν) :=
    (MeasurePreserving.id μ).skew_product (g := fun x y ↦ p x - y) (by fun_prop)
      (.of_forall fun x ↦ ν.map_sub_left_eq_self (p x))
  have e_eq : ⇑(sectionShearEquiv hι hp h_sec) = (fun q ↦ (q.fst, p q.fst - q.snd)) ∘
      Prod.swap ∘ (fun q ↦ (q.fst, ι q.fst + q.snd)) ∘
      Prod.swap ∘ fun q ↦ (q.fst, q.snd - p q.fst) := by
    ext q <;> simp [sectionShearEquiv, h_sec]
  rw [e_eq]
  exact shear₃.comp (Measure.measurePreserving_swap.comp
    (shear₂.comp (Measure.measurePreserving_swap.comp shear₁)))

/-- Factorization of a Lebesgue integral along a measurable section `ι : Y → X` of `p : X → Y`. -/
theorem lintegral_eq_mul_of_section {μ : Measure X} (ν : Measure Y) [SFinite μ] [SFinite ν]
    [μ.IsAddLeftInvariant] [ν.IsAddLeftInvariant] [ν.IsNegInvariant] {ι : Y → X} {p : X → Y}
    (hι : Measurable ι) (hp : Measurable p) (h_sec : ∀ (y : Y) (x : X), p (ι y + x) = y + p x)
    {K : Set Y} (hK : MeasurableSet K) (K_one : ν K = 1) {f c : X → ℝ≥0∞} {a : Y → ℝ≥0∞}
    (hf_meas : Measurable f) (hc_meas : Measurable c) (ha_meas : Measurable a)
    (hf : ∀ (y : Y) (x : X), p x ∈ K → f (ι y + x) = c x * a (y + p x)) :
    ∫⁻ x : X, f x ∂μ = (∫⁻ x : X in p ⁻¹' K, c x ∂μ) * ∫⁻ y : Y, a y ∂ν := by
  have he := measurePreserving_sectionShearEquiv (μ := μ) (ν := ν) hι hp h_sec
  calc ∫⁻ x : X, f x ∂μ
      = ∫⁻ q : X × Y, f q.fst * K.indicator (fun _ ↦ (1 : ℝ≥0∞)) q.snd ∂μ.prod ν := by
        rw [lintegral_prod_mul hf_meas.aemeasurable (measurable_const.indicator hK).aemeasurable]
        simp [lintegral_indicator hK, K_one]
    _ = ∫⁻ q : X × Y, (p ⁻¹' K).indicator c q.fst * a q.snd ∂μ.prod ν := by
        rw [← he.lintegral_comp_emb (sectionShearEquiv hι hp h_sec).measurableEmbedding]
        refine lintegral_congr fun q ↦ ?_
        by_cases hq : p q.fst ∈ K <;> simp [sectionShearEquiv, hf, hq]
    _ = (∫⁻ x : X in p ⁻¹' K, c x ∂μ) * ∫⁻ y : Y, a y ∂ν := by
        rw [lintegral_prod_mul (hc_meas.indicator (hp hK)).aemeasurable ha_meas.aemeasurable,
          lintegral_indicator (hp hK)]

/-- Factorization of a Bochner integral along a measurable section `ι : Y → X` of `p : X → Y`. -/
theorem integral_eq_mul_of_section {μ : Measure X} (ν : Measure Y) [SFinite μ] [SFinite ν]
    [μ.IsAddLeftInvariant] [ν.IsAddLeftInvariant] [ν.IsNegInvariant] {ι : Y → X} {p : X → Y}
    (hι : Measurable ι) (hp : Measurable p) (h_sec : ∀ (y : Y) (x : X), p (ι y + x) = y + p x)
    {K : Set Y} (hK : MeasurableSet K) (K_one : ν K = 1) {f c : X → ℂ} {a : Y → ℂ}
    (hf : ∀ (y : Y) (x : X), p x ∈ K → f (ι y + x) = c x * a (y + p x)) :
    ∫ x : X, f x ∂μ = (∫ x : X in p ⁻¹' K, c x ∂μ) * ∫ y : Y, a y ∂ν := by
  have he := measurePreserving_sectionShearEquiv (μ := μ) (ν := ν) hι hp h_sec
  calc ∫ x : X, f x ∂μ
      = ∫ q : X × Y, f q.fst * K.indicator 1 q.snd ∂μ.prod ν := by
        simp [integral_prod_mul f, integral_indicator hK, K_one, Measure.real]
    _ = ∫ q : X × Y, (p ⁻¹' K).indicator c q.fst * a q.snd ∂μ.prod ν := by
        rw [← he.integral_comp']
        refine integral_congr_ae (.of_forall fun q ↦ ?_)
        by_cases hq : p q.fst ∈ K <;> simp [sectionShearEquiv, hf, hq]
    _ = (∫ x : X in p ⁻¹' K, c x ∂μ) * ∫ y : Y, a y ∂ν := by
        rw [integral_prod_mul, integral_indicator (hp hK)]

end TauCeti
