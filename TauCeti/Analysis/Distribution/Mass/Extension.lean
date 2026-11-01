/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Measure
public import TauCeti.Analysis.Distribution.TestFunction.Lp
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Evaluation of a current of locally finite mass on integrable forms

Let `Ω` be an open set of a finite-dimensional real normed space `E` and let
`T : 𝓓^{n}(Ω, F) → ℝ` be a real-linear map on `F`-valued test functions with locally finite mass
and mass measure `‖T‖` (`Distribution.massMeasure`). With `F = E [⋀^Fin k]→L[ℝ] ℝ` this is a
`k`-current of locally finite mass. The domination `|T φ| ≤ ∫ ‖φ‖ d‖T‖` says that `T` is
continuous for the `L¹(‖T‖)` norm on test functions, and test functions are dense in
`L¹(‖T‖; F)`. So `T` extends uniquely to a continuous linear functional `extendL1 T` on
`L¹(‖T‖; F)` of norm at most one. This evaluates `T` on every `‖T‖`-integrable form: compactly
supported continuous forms, and products of test forms with bounded Borel functions.

In particular, for a measurable set `A ⊆ Ω` the **Borel restriction**
`T ⌞ A : φ ↦ extendL1 T (1_A φ)` is again a continuous linear map on test functions with locally
finite mass (`Distribution.massRestrict`). It is dominated by `‖T‖` restricted to `A`, so its mass
is at most `‖T‖ A`: a Borel restriction of a finite-mass current has finite mass. It vanishes when
`‖T‖ A = 0`, is additive on disjoint sets, and is `T` itself for `A = Ω`. Its boundary need not
have locally finite mass.

## Main declarations

* `Distribution.extendL1`: the extension of `T` to `L¹(‖T‖; F)`.
* `Distribution.extendL1_toLp`, `Distribution.norm_extendL1_le`, `Distribution.extendL1_unique`:
  it extends `T`, has norm at most one, and is the only continuous extension.
* `Distribution.massRestrict`: the Borel restriction `T ⌞ A`.
* `Distribution.enorm_massRestrict_eq_indicatorToL1_le`: `|(T ⌞ A) φ| ≤ ∫_A ‖φ‖ d‖T‖`.
* `Distribution.mass_massRestrict_le`, `Distribution.massMeasure_massRestrict_le`: the mass
  bounds `M(T ⌞ A) ≤ ‖T‖ A` and `‖T ⌞ A‖ ≤ ‖T‖ ⌞ A`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.5 and §4.1.7 (currents representable by
  integration, their extension to `‖T‖`-summable forms, and the restriction `T ⌞ A`).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (the restriction of a
  current of locally finite mass to a Borel set).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal Distributions

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {n : ℕ∞}
  {𝓕 : Type*} [FunLike 𝓕 𝓓^{n}(Ω, F) ℝ] [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, F) ℝ] {T : 𝓕}

/-! ### The extension to `L¹` of the mass measure -/

/-- The **extension of `T` to `L¹(‖T‖; F)`**: for a real-linear map `T` on test functions with
locally finite mass, the unique continuous linear functional on `L¹` of the mass measure `‖T‖`
that agrees with `T` on test functions (`Distribution.extendL1_toLp`,
`Distribution.extendL1_unique`). It has norm at most one (`Distribution.norm_extendL1_le`). If `T`
does not have locally finite mass, `‖T‖` is zero and so is this functional. -/
def extendL1 (T : 𝓕) : Lp F 1 (massMeasure T) →L[ℝ] ℝ :=
  (T : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ).extendOfNorm (TestFunction.toLp 1 (massMeasure T)).toLinearMap

private theorem extendL1_def (T : 𝓕) :
    extendL1 T =
      (T : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ).extendOfNorm (TestFunction.toLp 1 (massMeasure T)).toLinearMap :=
  (rfl)

/-- The domination of `T` by its mass measure, in `L¹` form. -/
private theorem norm_apply_le_norm_toLp (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    ‖T φ‖ ≤ ‖TestFunction.toLp 1 (massMeasure T) φ‖ := by
  rw [← enorm_le_iff_norm_le, TestFunction.enorm_toLp_one]
  exact enorm_apply_le_lintegral_massMeasure hT φ

/-- The domination of `T` by its mass measure, in the form used by `LinearMap.extendOfNorm`. -/
private theorem norm_apply_le_one_mul (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    ‖(T : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ) φ‖ ≤ 1 * ‖(TestFunction.toLp 1 (massMeasure T)).toLinearMap φ‖ :=
  (norm_apply_le_norm_toLp hT φ).trans_eq (one_mul _).symm

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [NormedSpace ℝ F] in
/-- Every element of `L¹` of the zero measure is zero. -/
private theorem eq_zero_of_measure_eq_zero {μ : Measure Ω} (hμ : μ = 0) (f : Lp F 1 μ) :
    f = 0 := by
  subst hμ
  exact Lp.eq_zero_iff_ae_eq_zero.2 (by simp [Filter.EventuallyEq])

variable {A B : Set Ω}

/-- The class in `L¹(‖T‖; F)` of `1_A φ`, for a test function `φ` and a measurable set `A`. -/
private def indicatorToL1 (T : 𝓕) (hA : MeasurableSet A) :
    𝓓^{n}(Ω, F) →ₗ[ℝ] Lp F 1 (massMeasure T) where
  toFun φ := ((TestFunction.memLp_restrict φ).indicator hA.nullMeasurableSet).toLp
    (A.indicator fun x : Ω => φ x)
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (.of_eq (by ext x; by_cases hx : x ∈ A <;> simp [hx]))
  map_smul' c φ := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (.of_eq (by ext x; by_cases hx : x ∈ A <;> simp [hx]))

private theorem enorm_indicatorToL1 (hA : MeasurableSet A) (φ : 𝓓^{n}(Ω, F)) :
    ‖indicatorToL1 T hA φ‖ₑ = ∫⁻ x in A, ‖φ x‖ₑ ∂massMeasure T := by
  rw [indicatorToL1, LinearMap.coe_mk, AddHom.coe_mk, Lp.enorm_toLp,
    eLpNorm_one_eq_lintegral_enorm, ← lintegral_indicator hA]
  · simp_rw [enorm_indicator_eq_indicator_enorm]
  · exact ((TestFunction.memLp_restrict (p := 1) φ).indicator
      hA.nullMeasurableSet).aestronglyMeasurable

private theorem norm_indicatorToL1_le (hA : MeasurableSet A) (φ : 𝓓^{n}(Ω, F)) :
    ‖indicatorToL1 T hA φ‖ ≤ ‖TestFunction.toLp 1 (massMeasure T) φ‖ := by
  rw [← enorm_le_iff_norm_le, enorm_indicatorToL1, TestFunction.enorm_toLp_one]
  exact setLIntegral_le_lintegral _ _

variable [CompleteSpace F]

/-- `extendL1 T` extends `T`: on the class of a test function it is the value of `T`. -/
@[simp]
theorem extendL1_toLp (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    extendL1 T (TestFunction.toLp 1 (massMeasure T) φ) = T φ := by
  rw [extendL1_def]
  exact LinearMap.extendOfNorm_eq (f := (T : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ))
    (TestFunction.denseRange_toLp ENNReal.one_ne_top)
    ⟨1, norm_apply_le_one_mul hT⟩ φ

/-- **Mass bound for the extension.** `|extendL1 T f| ≤ ∫ ‖f‖ d‖T‖`. -/
theorem norm_extendL1_apply_le (f : Lp F 1 (massMeasure T)) : ‖extendL1 T f‖ ≤ ‖f‖ := by
  by_cases hT : HasLocallyFiniteMass T
  · rw [extendL1_def]
    simpa using LinearMap.norm_extendOfNorm_apply_le (f := (T : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ))
      (TestFunction.denseRange_toLp ENNReal.one_ne_top) 1
      (norm_apply_le_one_mul hT) f
  · simp [eq_zero_of_measure_eq_zero (massMeasure_of_not_hasLocallyFiniteMass hT) f]

/-- The extension of `T` to `L¹(‖T‖; F)` has norm at most one. -/
theorem norm_extendL1_le : ‖extendL1 T‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    simpa using norm_extendL1_apply_le f

/-- **Uniqueness of the extension.** A continuous linear functional on `L¹(‖T‖; F)` that agrees
with `T` on test functions is `extendL1 T`. -/
theorem extendL1_unique (hT : HasLocallyFiniteMass T) (S : Lp F 1 (massMeasure T) →L[ℝ] ℝ)
    (hS : ∀ φ : 𝓓^{n}(Ω, F), S (TestFunction.toLp 1 (massMeasure T) φ) = T φ) :
    extendL1 T = S := by
  rw [extendL1_def]
  exact LinearMap.extendOfNorm_unique (f := (T : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ))
    (TestFunction.denseRange_toLp ENNReal.one_ne_top) 1 (norm_apply_le_one_mul hT) S
    (LinearMap.ext hS)

/-! ### Borel restriction -/

private theorem hasLocallyFiniteMass_comp_indicatorToL1 (hA : MeasurableSet A) :
    HasLocallyFiniteMass ((extendL1 T).toLinearMap ∘ₗ indicatorToL1 T hA) :=
  hasLocallyFiniteMass_def.2 fun K hK hKΩ => by
    obtain ⟨C, hC, hCK⟩ := hasLocallyFiniteMass_def.1
      (TestFunction.hasLocallyFiniteMass_toLp (n := n) (F := F) 1 (massMeasure T)) K hK hKΩ
    exact ⟨C, hC, fun φ hφK =>
      (norm_extendL1_apply_le _).trans ((norm_indicatorToL1_le hA φ).trans (hCK φ hφK))⟩

/-- The **Borel restriction** `T ⌞ A` of a real-linear map `T` with locally finite mass to a
measurable set `A ⊆ Ω`: the continuous linear map `φ ↦ extendL1 T (1_A φ)` on test functions,
where `1_A φ` is integrated against the mass measure `‖T‖`. It has locally finite mass
(`Distribution.hasLocallyFiniteMass_massRestrict`) and is dominated by `‖T‖` restricted to `A`
(`Distribution.enorm_massRestrict_eq_indicatorToL1_le`). -/
def massRestrict (T : 𝓕) (hA : MeasurableSet A) : 𝓓^{n}(Ω, F) →L[ℝ] ℝ :=
  ⟨(extendL1 T).toLinearMap ∘ₗ indicatorToL1 T hA,
    (hasLocallyFiniteMass_comp_indicatorToL1 hA).continuous⟩

private theorem massRestrict_eq_indicatorToL1 (hA : MeasurableSet A) (φ : 𝓓^{n}(Ω, F)) :
    massRestrict T hA φ = extendL1 T (indicatorToL1 T hA φ) :=
  (rfl)

/-- `(T ⌞ A) φ` is the value of `extendL1 T` on the class of `1_A φ` in `L¹(‖T‖; F)`. -/
theorem massRestrict_apply (hA : MeasurableSet A) (φ : 𝓓^{n}(Ω, F)) :
    massRestrict T hA φ = extendL1 T
      (((TestFunction.memLp_restrict φ).indicator hA.nullMeasurableSet).toLp
        (A.indicator fun x : Ω => φ x)) :=
  (rfl)

/-- **Domination of the Borel restriction.** `|(T ⌞ A) φ| ≤ ∫_A ‖φ‖ d‖T‖`. -/
theorem enorm_massRestrict_eq_indicatorToL1_le (hA : MeasurableSet A) (φ : 𝓓^{n}(Ω, F)) :
    ‖massRestrict T hA φ‖ₑ ≤ ∫⁻ x in A, ‖φ x‖ₑ ∂massMeasure T := by
  rw [← enorm_indicatorToL1 hA, massRestrict_eq_indicatorToL1, enorm_le_iff_norm_le]
  exact norm_extendL1_apply_le _

/-- A Borel restriction has locally finite mass. -/
theorem hasLocallyFiniteMass_massRestrict (hA : MeasurableSet A) :
    HasLocallyFiniteMass (massRestrict T hA) := by
  rw [show ⇑(massRestrict T hA) = _ from funext (massRestrict_eq_indicatorToL1 hA)]
  exact hasLocallyFiniteMass_comp_indicatorToL1 hA

/-- **Mass of a Borel restriction.** `M(T ⌞ A) ≤ ‖T‖ A`; in particular a Borel restriction to a
set of finite `‖T‖`-measure has finite mass. -/
theorem mass_massRestrict_le (hA : MeasurableSet A) :
    mass (massRestrict T hA) ≤ massMeasure T A := by
  refine mass_le_iff.2 fun φ hφ => (enorm_massRestrict_eq_indicatorToL1_le hA φ).trans ?_
  calc ∫⁻ x in A, ‖φ x‖ₑ ∂massMeasure T ≤ ∫⁻ _ in A, 1 ∂massMeasure T :=
        lintegral_mono fun x => by
          rw [← ofReal_norm, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (hφ x)
    _ = massMeasure T A := by simp

/-- **Mass measure of a Borel restriction.** `‖T ⌞ A‖ ≤ ‖T‖ ⌞ A`. -/
theorem massMeasure_massRestrict_le (hA : MeasurableSet A) :
    massMeasure (massRestrict T hA) ≤ (massMeasure T).restrict A := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  exact massMeasure_le_of_enorm_apply_le _ (enorm_massRestrict_eq_indicatorToL1_le hA)

/-- A Borel restriction to a `‖T‖`-null set is zero. -/
theorem massRestrict_eq_zero (hA : MeasurableSet A) (hA0 : massMeasure T A = 0) :
    massRestrict T hA = 0 := by
  ext φ
  have h := enorm_massRestrict_eq_indicatorToL1_le (T := T) hA φ
  rw [Measure.restrict_eq_zero.2 hA0, lintegral_zero_measure, nonpos_iff_eq_zero,
    enorm_eq_zero] at h
  simpa using h

/-- Borel restriction is additive on disjoint measurable sets. -/
theorem massRestrict_union (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    massRestrict T (hA.union hB) = massRestrict T hA + massRestrict T hB := by
  ext φ
  simp only [add_apply, massRestrict_eq_indicatorToL1, ← map_add]
  congr 1
  simp only [indicatorToL1, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← MemLp.toLp_add]
  exact MemLp.toLp_congr _ _ (.of_eq (indicator_union_of_disjoint hAB _))

/-- The restriction of `T` to all of `Ω` is `T`. -/
theorem massRestrict_univ (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    massRestrict T MeasurableSet.univ φ = T φ := by
  rw [massRestrict_eq_indicatorToL1, ← extendL1_toLp hT φ, TestFunction.toLp_apply]
  congr 1
  simp only [indicatorToL1, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.toLp_congr _ _ (.of_eq (indicator_univ _))

end Distribution
