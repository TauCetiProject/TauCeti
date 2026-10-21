/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Densities of pushforwards under an injective change of variables

Let `ρ` be a measure on `X`, `S` a measurable set, `T : X → X` a measurable map and
`J : X → ℝ≥0∞` a measurable *Jacobian* for `T` on `S`, in the sense of the change of variables
identity

  `ρ.withDensity g (T '' s) = ∫⁻ x in s, J x * g (T x) ∂ρ`

for every measurable `s ⊆ S` and every `g`. Nothing else about `T` is assumed: the identity is the
abstract output of a change of variables formula such as Mathlib's
`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`, and this file derives the
consequences for pushforwards of measures `μ ≪ ρ` restricted to `S`.

* If `J` vanishes nowhere on `S`, then `T` pushes `μ` restricted to `S` to a measure absolutely
  continuous with respect to `ρ`.
* If moreover `T` is injective on `S`, maps measurable subsets of `S` to measurable sets, and `J`
  is finite on `S`, then the densities satisfy the Jacobian equation
  `dμ/dρ (x) = J x * d(T₊ (μ|S))/dρ (T x)` on `S`, and integrals of a function `Φ` with `Φ 0 = 0`
  of the density of the pushforward are integrals over `S`:
  `∫ Φ (d(T₊ (μ|S))/dρ) dρ = ∫_S J x * Φ (dμ/dρ (x) / J x) dρ`.

## Main statements

* `TauCeti.map_restrict_absolutelyContinuous_of_withDensity_image_eq`: the pushforward of an
  absolutely continuous measure is absolutely continuous;
* `TauCeti.restrict_eq_withDensity_indicator_rnDeriv_map_restrict`: the Jacobian equation, as an
  identity of measures;
* `TauCeti.lintegral_comp_rnDeriv_map_restrict`: integrals of functions of the density of the
  pushforward, as integrals over the source.
-/

public section

namespace TauCeti

open MeasureTheory Measure Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] (ρ : Measure X)

/-- Let `T` be a measurable map and `J` a measurable function vanishing nowhere on a measurable set
`S`, such that `ρ.withDensity g (T '' s) = ∫⁻ x in s, J x * g (T x) ∂ρ` for every measurable
`s ⊆ S` and every `g`. Then `T` pushes `μ ≪ ρ` restricted to `S` to a measure absolutely continuous
with respect to `ρ`. -/
theorem map_restrict_absolutelyContinuous_of_withDensity_image_eq {T : X → X}
    (hT : Measurable T) {S : Set X} (hSm : MeasurableSet S) {J : X → ℝ≥0∞} (hJm : Measurable J)
    (hJ : ∀ x ∈ S, J x ≠ 0)
    (hcov : ∀ s, MeasurableSet s → s ⊆ S → ∀ g : X → ℝ≥0∞,
      ρ.withDensity g (T '' s) = ∫⁻ x in s, J x * g (T x) ∂ρ)
    {μ : Measure X} (hμ : μ ≪ ρ) :
    (μ.restrict S).map T ≪ ρ := by
  refine AbsolutelyContinuous.mk fun A hA hρA => ?_
  set s := T ⁻¹' A ∩ S
  have hs : MeasurableSet s := (hT hA).inter hSm
  -- The image of `s` lies in the null set `A`, so `J` integrates to `0` over `s`, which is
  -- therefore null.
  have hint : ∫⁻ x in s, J x ∂ρ = 0 := by
    have himage := hcov s hs inter_subset_right 1
    rw [withDensity_one, measure_mono_null ((image_preimage_subset T A).trans' (image_mono
      inter_subset_left)) hρA] at himage
    simpa using himage.symm
  have hρs : ρ s = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (((setLIntegral_eq_zero_iff hs hJm).1 hint).mono
      fun x hx hxs => hJ x hxs.2 (hx hxs))
  rw [map_apply hT hA, restrict_apply (hT hA)]
  exact hμ hρs

variable [SigmaFinite ρ]

/-- Under the change of variables of `map_restrict_absolutelyContinuous_of_withDensity_image_eq`,
with `T` injective on `S` and sending measurable subsets of `S` to measurable sets, `μ` restricted
to `S` has density `J x * d((T)₊ (μ|S))/dρ (T x)` on `S`. -/
theorem restrict_eq_withDensity_indicator_rnDeriv_map_restrict {T : X → X}
    (hT : Measurable T) {S : Set X} (hSm : MeasurableSet S) (hinj : InjOn T S)
    (himage : ∀ s, MeasurableSet s → s ⊆ S → MeasurableSet (T '' s)) {J : X → ℝ≥0∞}
    (hcov : ∀ s, MeasurableSet s → s ⊆ S → ∀ g : X → ℝ≥0∞,
      ρ.withDensity g (T '' s) = ∫⁻ x in s, J x * g (T x) ∂ρ)
    {μ : Measure X} [SFinite μ] (hac : (μ.restrict S).map T ≪ ρ) :
    μ.restrict S =
      ρ.withDensity (S.indicator fun x => J x * ((μ.restrict S).map T).rnDeriv ρ (T x)) := by
  set ν := (μ.restrict S).map T
  have hν : ρ.withDensity (ν.rnDeriv ρ) = ν := withDensity_rnDeriv_eq _ _ hac
  ext s hs
  have hsS : MeasurableSet (s ∩ S) := hs.inter hSm
  have hTs := himage _ hsS inter_subset_right
  calc μ.restrict S s = ν (T '' (s ∩ S)) := by
        rw [restrict_apply hs, map_apply hT hTs, restrict_apply (hT hTs),
          hinj.preimage_image_inter inter_subset_right]
    _ = ρ.withDensity (ν.rnDeriv ρ) (T '' (s ∩ S)) := by rw [hν]
    _ = ∫⁻ x in s ∩ S, J x * ν.rnDeriv ρ (T x) ∂ρ := hcov _ hsS inter_subset_right _
    _ = _ := by rw [withDensity_apply _ hs, setLIntegral_indicator hSm, inter_comm S s]

/-- Under the hypotheses of `restrict_eq_withDensity_indicator_rnDeriv_map_restrict`, with `J`
positive and finite on `S`, integrals of a function `Φ` with `Φ 0 = 0` of the density of
`(T)₊ (μ|S)` are integrals over `S`:
`∫ Φ (d((T)₊ (μ|S))/dρ) dρ = ∫_S J x * Φ (dμ/dρ (x) / J x) dρ`. -/
theorem lintegral_comp_rnDeriv_map_restrict {T : X → X} (hT : Measurable T) {S : Set X}
    (hSm : MeasurableSet S) (hinj : InjOn T S)
    (himage : ∀ s, MeasurableSet s → s ⊆ S → MeasurableSet (T '' s)) {J : X → ℝ≥0∞}
    (hJm : Measurable J) (hJ : ∀ x ∈ S, J x ≠ 0 ∧ J x ≠ ∞)
    (hcov : ∀ s, MeasurableSet s → s ⊆ S → ∀ g : X → ℝ≥0∞,
      ρ.withDensity g (T '' s) = ∫⁻ x in s, J x * g (T x) ∂ρ)
    {μ : Measure X} [SFinite μ] (hac : (μ.restrict S).map T ≪ ρ) {Φ : ℝ≥0∞ → ℝ≥0∞}
    (hΦ : Φ 0 = 0) :
    ∫⁻ y, Φ (((μ.restrict S).map T).rnDeriv ρ y) ∂ρ =
      ∫⁻ x in S, J x * Φ (μ.rnDeriv ρ x / J x) ∂ρ := by
  set ν := (μ.restrict S).map T
  set g := ν.rnDeriv ρ
  have hν : ρ.withDensity g = ν := withDensity_rnDeriv_eq _ _ hac
  have hTS := himage S hSm subset_rfl
  -- `ν` is carried by `T '' S`, so `g` vanishes almost everywhere off it.
  have hg0 : ∀ᵐ y ∂ρ, y ∈ (T '' S)ᶜ → g y = 0 := by
    have hνc : ν (T '' S)ᶜ = 0 := by
      rw [map_apply hT hTS.compl, restrict_apply (hT hTS.compl)]
      exact measure_mono_null (fun x hx => (hx.1 (mem_image_of_mem T hx.2)).elim) measure_empty
    rw [← setLIntegral_eq_zero_iff hTS.compl (measurable_rnDeriv ν ρ), ← withDensity_apply _
      hTS.compl, hν, hνc]
  -- The Jacobian equation on `S`: `dμ/dρ (x) = J x * g (T x)`.
  have hJac : ∀ᵐ x ∂ρ, x ∈ S → g (T x) = μ.rnDeriv ρ x / J x := by
    have h₁ := rnDeriv_restrict μ ρ hSm
    rw [restrict_eq_withDensity_indicator_rnDeriv_map_restrict ρ hT hSm hinj himage hcov hac] at h₁
    filter_upwards [h₁.symm.trans (rnDeriv_withDensity ρ
      ((hJm.mul ((measurable_rnDeriv ν ρ).comp hT)).indicator hSm))] with x hx hxS
    rw [indicator_of_mem hxS, indicator_of_mem hxS] at hx
    rw [ENNReal.eq_div_iff (hJ x hxS).1 (hJ x hxS).2, hx]
  calc ∫⁻ y, Φ (g y) ∂ρ = ∫⁻ y, (T '' S).indicator (fun y => Φ (g y)) y ∂ρ := by
        refine lintegral_congr_ae (hg0.mono fun y hy => ?_)
        by_cases hyS : y ∈ T '' S
        · rw [indicator_of_mem hyS]
        · simp [indicator_of_notMem hyS, hy hyS, hΦ]
    _ = ∫⁻ x in S, J x * Φ (g (T x)) ∂ρ := by
        rw [lintegral_indicator hTS, ← withDensity_apply' _ (T '' S)]
        exact hcov S hSm subset_rfl _
    _ = _ := setLIntegral_congr_fun_ae hSm (hJac.mono fun x hx hxS => by rw [hx hxS])

end TauCeti
