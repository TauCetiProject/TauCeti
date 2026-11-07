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
* `Distribution.extendL1_toLp`, `Distribution.opNorm_extendL1_le`, `Distribution.extendL1_unique`:
  it extends `T`, has norm at most one, and is the only continuous extension.
* `Distribution.massRestrict`: the Borel restriction `T ⌞ A`.
* `Distribution.enorm_massRestrict_apply_le`: `|(T ⌞ A) φ| ≤ ∫_A ‖φ‖ d‖T‖`.
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
`Distribution.extendL1_unique`). It has norm at most one (`Distribution.opNorm_extendL1_le`). If `T`
does not have locally finite mass, `‖T‖` is zero and so is this functional. -/
def extendL1 (T : 𝓕) : Lp F 1 (massMeasure T) →L[ℝ] ℝ :=
  (T : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ).extendOfNorm (TestFunction.toLp 1 (massMeasure T)).toLinearMap

/-- The domination of `T` by its mass measure, in the form used by `LinearMap.extendOfNorm`. -/
private theorem norm_apply_le_one_mul (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    ‖(T : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ) φ‖ ≤ 1 * ‖(TestFunction.toLp 1 (massMeasure T)).toLinearMap φ‖ := by
  rw [one_mul, LinearMap.coe_ofClass, ContinuousLinearMap.coe_coe, ← enorm_le_iff_norm_le,
    TestFunction.enorm_toLp_one]
  exact enorm_apply_le_lintegral_massMeasure hT φ

variable {A B : Set Ω}

variable [CompleteSpace F]

/-- `extendL1 T` extends `T`: on the class of a test function it is the value of `T`. -/
@[simp]
theorem extendL1_toLp (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    extendL1 T (TestFunction.toLp 1 (massMeasure T) φ) = T φ := by
  rw [extendL1]
  exact LinearMap.extendOfNorm_eq (f := (T : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ))
    (TestFunction.denseRange_toLp ENNReal.one_ne_top)
    ⟨1, norm_apply_le_one_mul hT⟩ φ

/-- **Mass bound for the extension.** `|extendL1 T f| ≤ ∫ ‖f‖ d‖T‖`. -/
theorem norm_extendL1_apply_le (f : Lp F 1 (massMeasure T)) : ‖extendL1 T f‖ ≤ ‖f‖ := by
  by_cases hT : HasLocallyFiniteMass T
  · rw [extendL1]
    simpa using LinearMap.norm_extendOfNorm_apply_le (f := (T : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ))
      (TestFunction.denseRange_toLp ENNReal.one_ne_top) 1
      (norm_apply_le_one_mul hT) f
  · -- Without locally finite mass `‖T‖ = 0`, so `L¹(‖T‖; F)` is trivial.
    obtain rfl : f = 0 := by
      revert f
      rw [massMeasure_of_not_hasLocallyFiniteMass hT]
      exact fun f => norm_eq_zero.1 (Lp.norm_measure_zero f)
    simp

/-- The extension of `T` to `L¹(‖T‖; F)` has norm at most one. -/
theorem opNorm_extendL1_le : ‖extendL1 T‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    simpa using norm_extendL1_apply_le f

/-- **Uniqueness of the extension.** A continuous linear functional on `L¹(‖T‖; F)` that agrees
with `T` on test functions is `extendL1 T`. -/
theorem extendL1_unique (hT : HasLocallyFiniteMass T) (S : Lp F 1 (massMeasure T) →L[ℝ] ℝ)
    (hS : ∀ φ : 𝓓^{n}(Ω, F), S (TestFunction.toLp 1 (massMeasure T) φ) = T φ) :
    extendL1 T = S := by
  rw [extendL1]
  exact LinearMap.extendOfNorm_unique (f := (T : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ))
    (TestFunction.denseRange_toLp ENNReal.one_ne_top) 1 (norm_apply_le_one_mul hT) S
    (LinearMap.ext hS)

/-! ### Borel restriction -/

private theorem hasLocallyFiniteMass_comp_indicatorToLp (hA : MeasurableSet A) :
    HasLocallyFiniteMass
      ((extendL1 T).toLinearMap ∘ₗ TestFunction.indicatorToLp (n := n) 1 (massMeasure T) hA) :=
  hasLocallyFiniteMass_def.2 fun K hK hKΩ => by
    obtain ⟨C, hC, hCK⟩ := hasLocallyFiniteMass_def.1
      (TestFunction.hasLocallyFiniteMass_toLp (n := n) (F := F) 1 (massMeasure T)) K hK hKΩ
    exact ⟨C, hC, fun φ hφK =>
      (norm_extendL1_apply_le _).trans
        ((TestFunction.norm_indicatorToLp_le hA φ).trans (hCK φ hφK))⟩

/-- The **Borel restriction** `T ⌞ A` of a real-linear map `T` with locally finite mass to a
measurable set `A ⊆ Ω`: the continuous linear map `φ ↦ extendL1 T (1_A φ)` on test functions,
where `1_A φ` is integrated against the mass measure `‖T‖`. It has locally finite mass
(`Distribution.hasLocallyFiniteMass_massRestrict`) and is dominated by `‖T‖` restricted to `A`
(`Distribution.enorm_massRestrict_apply_le`). -/
def massRestrict (T : 𝓕) (hA : MeasurableSet A) : 𝓓^{n}(Ω, F) →L[ℝ] ℝ :=
  ⟨(extendL1 T).toLinearMap ∘ₗ TestFunction.indicatorToLp 1 (massMeasure T) hA,
    (hasLocallyFiniteMass_comp_indicatorToLp hA).continuous⟩

/-- `(T ⌞ A) φ` is the value of `extendL1 T` on the class of `1_A φ` in `L¹(‖T‖; F)`. -/
theorem massRestrict_apply (hA : MeasurableSet A) (φ : 𝓓^{n}(Ω, F)) :
    massRestrict T hA φ = extendL1 T (TestFunction.indicatorToLp 1 (massMeasure T) hA φ) :=
  (rfl)

/-- **Domination of the Borel restriction.** `|(T ⌞ A) φ| ≤ ∫_A ‖φ‖ d‖T‖`. -/
theorem enorm_massRestrict_apply_le (hA : MeasurableSet A) (φ : 𝓓^{n}(Ω, F)) :
    ‖massRestrict T hA φ‖ₑ ≤ ∫⁻ x in A, ‖φ x‖ₑ ∂massMeasure T := by
  rw [← TestFunction.enorm_indicatorToLp_one _ hA, massRestrict_apply, enorm_le_iff_norm_le]
  exact norm_extendL1_apply_le _

/-- A Borel restriction has locally finite mass. -/
theorem hasLocallyFiniteMass_massRestrict (hA : MeasurableSet A) :
    HasLocallyFiniteMass (massRestrict T hA) := by
  rw [funext (massRestrict_apply hA)]
  exact hasLocallyFiniteMass_comp_indicatorToLp hA

/-- **Mass measure of a Borel restriction.** `‖T ⌞ A‖ ≤ ‖T‖ ⌞ A`. -/
theorem massMeasure_massRestrict_le (hA : MeasurableSet A) :
    massMeasure (massRestrict T hA) ≤ (massMeasure T).restrict A := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  exact massMeasure_le_of_enorm_apply_le _ (enorm_massRestrict_apply_le hA)

/-- **Mass of a Borel restriction.** `M(T ⌞ A) ≤ ‖T‖ A`; in particular a Borel restriction to a
set of finite `‖T‖`-measure has finite mass. -/
theorem mass_massRestrict_le (hA : MeasurableSet A) :
    mass (massRestrict T hA) ≤ massMeasure T A := by
  rw [← massMeasure_univ (hasLocallyFiniteMass_massRestrict hA)]
  simpa using Measure.le_iff'.1 (massMeasure_massRestrict_le hA) univ

/-- A Borel restriction to a `‖T‖`-null set is zero. -/
theorem massRestrict_eq_zero (hA : MeasurableSet A) (hA0 : massMeasure T A = 0) :
    massRestrict T hA = 0 := by
  ext φ
  have h := enorm_massRestrict_apply_le (T := T) hA φ
  rw [Measure.restrict_eq_zero.2 hA0, lintegral_zero_measure, nonpos_iff_eq_zero,
    enorm_eq_zero] at h
  simpa using h

/-- Borel restriction is additive on disjoint measurable sets. -/
theorem massRestrict_union (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    massRestrict T (hA.union hB) = massRestrict T hA + massRestrict T hB := by
  ext φ
  simp only [add_apply, massRestrict_apply, TestFunction.indicatorToLp_union _ _ hA hB hAB,
    LinearMap.add_apply, map_add]

/-- The restriction of `T` to all of `Ω` is `T`. -/
@[simp]
theorem massRestrict_univ_apply (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    massRestrict T MeasurableSet.univ φ = T φ := by
  rw [massRestrict_apply, TestFunction.indicatorToLp_univ, extendL1_toLp hT]

end Distribution
