/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Densities of pushforwards under an injective change of variables

Let `ρ` and `σ` be measures on `X` and `Y`, `S` a measurable set in `X`, `T : X → Y` a map and
`J : X → ℝ≥0∞` a *Jacobian* for `T` on `S`, in the sense of the change of variables identity

  `σ.withDensity g (T '' s) = ∫⁻ x in s, J x * g (T x) ∂ρ`

for every measurable `s ⊆ S` and every `g`. Beyond measurability of `T` (only almost everywhere
with respect to `μ` restricted to `S`, except for the integral formula), nothing else about `T` is
assumed: the identity is the abstract output of a change of variables formula such as Mathlib's
`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` (where `X = Y` and `ρ = σ`), and
this file derives the consequences for pushforwards of measures `μ` restricted to `S`.

* If `J` is almost everywhere measurable and almost nowhere zero on `S`, then `T` pushes `μ ≪ ρ`
  restricted to `S` to a measure absolutely continuous with respect to `σ`.
* If `T` is injective on `S`, maps measurable subsets of `S` to measurable sets, and pushes `μ`
  restricted to `S` to a measure `T₊ (μ|S) ≪ σ` with a Lebesgue decomposition with respect to `σ`
  (as when `μ` is s-finite and `σ` σ-finite), then the Jacobian equation holds as an identity
  of measures: `μ|S = ρ.withDensity (S.indicator fun x => J x * d(T₊ (μ|S))/dσ (T x))`. When `ρ`
  is σ-finite, `μ` has a Lebesgue decomposition with respect to `ρ` and this density is almost
  everywhere measurable, it follows that
  `dμ/dρ (x) = J x * d(T₊ (μ|S))/dσ (T x)` for `ρ`-almost every `x ∈ S`; the identity says
  nothing about `J` on `ρ`-null sets.
* If moreover `T` is measurable, `ρ` and `σ` are σ-finite, `μ` has a Lebesgue decomposition with
  respect to `ρ`, and `J` is almost everywhere measurable on `S` (it is then almost everywhere
  finite there), integrals of a function `Φ` with `Φ 0 = 0` of the
  density of the pushforward are integrals over `S`:
  `∫ Φ (d(T₊ (μ|S))/dσ) dσ = ∫_S J x * Φ (dμ/dρ (x) / J x) dρ`.

## Main statements

* `MeasureTheory.Measure.map_restrict_absolutelyContinuous_of_withDensity_image_eq`: the
  pushforward of an absolutely continuous measure is absolutely continuous;
* `MeasureTheory.Measure.restrict_eq_withDensity_indicator_rnDeriv_map_restrict`: the Jacobian
  equation, as an identity of measures;
* `MeasureTheory.Measure.lintegral_comp_rnDeriv_map_restrict`: integrals of functions of the
  density of the pushforward, as integrals over the source.
-/

public section

namespace MeasureTheory.Measure

open Set
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (ρ : Measure X) (σ : Measure Y)

/-- Let `T : X → Y` be a map and `J` a function, almost everywhere measurable and almost everywhere
nonzero on a measurable set `S`, such that `σ.withDensity g (T '' s) = ∫⁻ x in s, J x * g (T x) ∂ρ`
for every measurable `s ⊆ S` and every `g`. Then `T`, if almost everywhere measurable for `μ`
restricted to `S`, pushes `μ ≪ ρ` restricted to `S` to a measure absolutely continuous with respect
to `σ`. -/
theorem map_restrict_absolutelyContinuous_of_withDensity_image_eq {T : X → Y} {S : Set X}
    {μ : Measure X} (hT : AEMeasurable T (μ.restrict S)) (hSm : MeasurableSet S) {J : X → ℝ≥0∞}
    (hJm : AEMeasurable J (ρ.restrict S)) (hJ : ∀ᵐ x ∂ρ.restrict S, J x ≠ 0)
    (hcov : ∀ s, MeasurableSet s → s ⊆ S → ∀ g : Y → ℝ≥0∞,
      σ.withDensity g (T '' s) = ∫⁻ x in s, J x * g (T x) ∂ρ)
    (hμ : μ ≪ ρ) :
    (μ.restrict S).map T ≪ σ := by
  -- `T` agrees with its measurable modification `T'` off the measurable set `N`, null for `μ|S`.
  set T' := hT.mk T
  set N := toMeasurable (μ.restrict S) {x | T x ≠ T' x}
  have hN : μ (N ∩ S) = 0 := by
    rw [← Measure.restrict_apply (measurableSet_toMeasurable _ _), measure_toMeasurable]
    exact ae_iff.1 hT.ae_eq_mk
  refine AbsolutelyContinuous.mk fun A hA hσA => ?_
  set s := (T' ⁻¹' A ∩ S) \ N
  have hs : MeasurableSet s :=
    ((hT.measurable_mk hA).inter hSm).diff (measurableSet_toMeasurable _ _)
  have hsS : s ⊆ S := sdiff_subset.trans inter_subset_right
  -- `T = T'` maps `s` into the null set `A`, so `J` integrates to `0` over `s`, which is
  -- therefore null.
  have hint : ∫⁻ x in s, J x ∂ρ = 0 := by
    have hTs : T '' s ⊆ A := by
      rintro _ ⟨x, hx, rfl⟩
      rw [not_not.1 fun h => hx.2 (subset_toMeasurable _ _ h)]
      exact hx.1.1
    have himage := hcov s hs hsS 1
    rw [withDensity_one, measure_mono_null hTs hσA] at himage
    simpa using himage.symm
  have hρs : ρ s = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [(setLIntegral_eq_zero_iff' hs (hJm.mono_set hsS)).1 hint,
      (ae_restrict_iff' hSm).1 hJ] with x hx₀ hxJ hxs
    exact hxJ (hsS hxs) (hx₀ hxs)
  -- The pushforward charges `A` with the mass of `T' ⁻¹' A ∩ S ⊆ s ∪ (N ∩ S)`, a `μ`-null set.
  rw [map_congr hT.ae_eq_mk, map_apply hT.measurable_mk hA, restrict_apply (hT.measurable_mk hA)]
  exact measure_mono_null (fun x hx => (em (x ∈ N)).symm.imp (fun h => ⟨hx, h⟩) (⟨·, hx.2⟩))
    (measure_union_null (hμ hρs) hN)

/-- Under the change of variables of `map_restrict_absolutelyContinuous_of_withDensity_image_eq`,
with `T` injective on `S` and sending measurable subsets of `S` to measurable sets, if `T` pushes
`μ` restricted to `S` to a measure `T₊ (μ|S) ≪ σ` with a Lebesgue decomposition with respect to `σ`,
then `μ` restricted to `S` is `ρ` with density
`J x * d(T₊ (μ|S))/dσ (T x)` on `S` (and `0` off `S`), as an identity of measures. -/
theorem restrict_eq_withDensity_indicator_rnDeriv_map_restrict {T : X → Y} {S : Set X}
    {μ : Measure X} [HaveLebesgueDecomposition ((μ.restrict S).map T) σ]
    (hT : AEMeasurable T (μ.restrict S)) (hSm : MeasurableSet S)
    (hinj : InjOn T S) (himage : ∀ s, MeasurableSet s → s ⊆ S → MeasurableSet (T '' s))
    {J : X → ℝ≥0∞}
    (hcov : ∀ s, MeasurableSet s → s ⊆ S → ∀ g : Y → ℝ≥0∞,
      σ.withDensity g (T '' s) = ∫⁻ x in s, J x * g (T x) ∂ρ)
    (hac : (μ.restrict S).map T ≪ σ) :
    μ.restrict S =
      ρ.withDensity (S.indicator fun x => J x * ((μ.restrict S).map T).rnDeriv σ (T x)) := by
  set ν := (μ.restrict S).map T
  have hν : σ.withDensity (ν.rnDeriv σ) = ν := withDensity_rnDeriv_eq _ _ hac
  ext s hs
  have hsS : MeasurableSet (s ∩ S) := hs.inter hSm
  have hTs := himage _ hsS inter_subset_right
  calc μ.restrict S s = ν (T '' (s ∩ S)) := by
        rw [restrict_apply hs, map_apply_of_aemeasurable hT hTs, restrict_apply' hSm,
          hinj.preimage_image_inter inter_subset_right]
    _ = σ.withDensity (ν.rnDeriv σ) (T '' (s ∩ S)) := by rw [hν]
    _ = ∫⁻ x in s ∩ S, J x * ν.rnDeriv σ (T x) ∂ρ := hcov _ hsS inter_subset_right _
    _ = _ := by rw [withDensity_apply _ hs, setLIntegral_indicator hSm, inter_comm S s]

/-- Under the hypotheses of `restrict_eq_withDensity_indicator_rnDeriv_map_restrict`, with `T`
measurable, `ρ` and `σ` σ-finite, `μ` with a Lebesgue decomposition with respect to `ρ`, and `J`
almost everywhere measurable on `S`, integrals of a function `Φ` with `Φ 0 = 0` of the density of
`T₊ (μ|S)` are integrals over `S`:
`∫ Φ (d(T₊ (μ|S))/dσ) dσ = ∫_S J x * Φ (dμ/dρ (x) / J x) dρ`. -/
theorem lintegral_comp_rnDeriv_map_restrict [SigmaFinite ρ] [SigmaFinite σ] {T : X → Y}
    (hT : Measurable T) {S : Set X} (hSm : MeasurableSet S) (hinj : InjOn T S)
    (himage : ∀ s, MeasurableSet s → s ⊆ S → MeasurableSet (T '' s)) {J : X → ℝ≥0∞}
    (hJm : AEMeasurable J (ρ.restrict S))
    (hcov : ∀ s, MeasurableSet s → s ⊆ S → ∀ g : Y → ℝ≥0∞,
      σ.withDensity g (T '' s) = ∫⁻ x in s, J x * g (T x) ∂ρ)
    {μ : Measure X} [HaveLebesgueDecomposition μ ρ]
    [HaveLebesgueDecomposition ((μ.restrict S).map T) σ] (hac : (μ.restrict S).map T ≪ σ)
    {Φ : ℝ≥0∞ → ℝ≥0∞} (hΦ : Φ 0 = 0) :
    ∫⁻ y, Φ (((μ.restrict S).map T).rnDeriv σ y) ∂σ =
      ∫⁻ x in S, J x * Φ (μ.rnDeriv ρ x / J x) ∂ρ := by
  set ν := (μ.restrict S).map T
  set g := ν.rnDeriv σ
  have hν : σ.withDensity g = ν := withDensity_rnDeriv_eq _ _ hac
  have hTS := himage S hSm subset_rfl
  -- `J` is finite almost everywhere on `S`: over the part of `S` that `T` maps into a spanning set
  -- of `σ`, it integrates to the finite measure of the image.
  have hJ : ∀ᵐ x ∂ρ.restrict S, J x ≠ ∞ := by
    have hn (n : ℕ) : ∀ᵐ x ∂ρ, x ∈ T ⁻¹' spanningSets σ n ∩ S → J x ≠ ∞ := by
      have hsn := (hT (measurableSet_spanningSets σ n)).inter hSm
      have hint := hcov _ hsn inter_subset_right 1
      simp only [withDensity_one, Pi.one_apply, mul_one] at hint
      rw [← ae_restrict_iff' hsn]
      refine (ae_lt_top' (hJm.mono_set inter_subset_right) ?_).mono fun x hx => hx.ne
      rw [← hint]
      exact ((measure_mono ((image_mono inter_subset_left).trans
        (image_preimage_subset T _))).trans_lt (measure_spanningSets_lt_top σ n)).ne
    filter_upwards [ae_restrict_of_ae (ae_all_iff.2 hn), ae_restrict_mem hSm] with x hx hxS
    exact hx _ ⟨mem_spanningSetsIndex σ (T x), hxS⟩
  -- `ν` is carried by `T '' S`, so `g` vanishes almost everywhere off it.
  have hg0 : ∀ᵐ y ∂σ, y ∈ (T '' S)ᶜ → g y = 0 := by
    have hνc : ν (T '' S)ᶜ = 0 := by
      rw [map_apply hT hTS.compl, restrict_apply (hT hTS.compl)]
      exact measure_mono_null (fun x hx => (hx.1 (mem_image_of_mem T hx.2)).elim) measure_empty
    rw [← setLIntegral_eq_zero_iff hTS.compl (measurable_rnDeriv ν σ), ← withDensity_apply _
      hTS.compl, hν, hνc]
  -- The Jacobian equation `dμ/dρ (x) = J x * g (T x)`, for `ρ`-a.e. `x ∈ S`, gives
  -- `g (T x) = dμ/dρ (x) / J x` wherever `J x` is nonzero and finite; where `J x = 0`, both sides
  -- below vanish.
  have hJac : ∀ᵐ x ∂ρ.restrict S, J x * Φ (g (T x)) = J x * Φ (μ.rnDeriv ρ x / J x) := by
    have h₁ := rnDeriv_restrict μ ρ hSm
    rw [restrict_eq_withDensity_indicator_rnDeriv_map_restrict ρ σ hT.aemeasurable hSm hinj
      himage hcov hac]
      at h₁
    have hφ : AEMeasurable (S.indicator fun x => J x * g (T x)) ρ :=
      (aemeasurable_indicator_iff hSm).2 (hJm.mul ((measurable_rnDeriv ν σ).comp hT).aemeasurable)
    filter_upwards [ae_restrict_of_ae (h₁.symm.trans (rnDeriv_withDensity₀ ρ hφ)), hJ,
      ae_restrict_mem hSm] with x hx hxJ hxS
    rw [indicator_of_mem hxS, indicator_of_mem hxS] at hx
    rcases eq_or_ne (J x) 0 with h0 | h0
    · simp [h0]
    · rw [← (ENNReal.eq_div_iff h0 hxJ).2 hx.symm]
  calc ∫⁻ y, Φ (g y) ∂σ = ∫⁻ y, (T '' S).indicator (fun y => Φ (g y)) y ∂σ := by
        refine lintegral_congr_ae (hg0.mono fun y hy => ?_)
        by_cases hyS : y ∈ T '' S
        · rw [indicator_of_mem hyS]
        · simp [indicator_of_notMem hyS, hy hyS, hΦ]
    _ = ∫⁻ x in S, J x * Φ (g (T x)) ∂ρ := by
        rw [lintegral_indicator hTS, ← withDensity_apply' _ (T '' S)]
        exact hcov S hSm subset_rfl _
    _ = _ := lintegral_congr_ae hJac

end MeasureTheory.Measure
