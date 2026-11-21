/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Support
public import TauCeti.Analysis.Distribution.TestFunction.Lp
public import TauCeti.Analysis.Distribution.TestFunction.Pullback
public import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
public import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Analysis.Distribution.Mass.Restriction
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Measure.Regular

/-!
# Evaluation of a current of locally finite mass on integrable forms

Let `Ω` be an open set of a real normed space `E` and let `T : 𝓓^{n}(Ω, F) → ℝ` be a real-linear map
on `F`-valued test functions with locally finite mass and mass measure `‖T‖`
(`Distribution.massMeasure`). With `F = E [⋀^Fin k]→L[ℝ] ℝ` this is a `k`-current of locally finite
mass. The domination `|T φ| ≤ ∫ ‖φ‖ d‖T‖` says that `T` is continuous for the `L¹(‖T‖)` norm on test
functions, and test functions are dense in `L¹(‖T‖; F)`: for finite-dimensional `E` by
`TestFunction.denseRange_toLp`, and trivially otherwise, since then `‖T‖ = 0`
(`Distribution.massMeasure_eq_zero_of_not_finiteDimensional`). So `T` extends uniquely to a
continuous linear functional `extendL1 T` on `L¹(‖T‖; F)` of norm at most one. This evaluates `T` on
every `‖T‖`-integrable form: compactly supported continuous forms, and products of test forms with
bounded Borel functions.

In particular, for a measurable set `A ⊆ Ω` the **Borel restriction**
`T ⌞ A : φ ↦ extendL1 T (1_A φ)` is again a continuous linear map on test functions with locally
finite mass (`Distribution.massRestrict`). For `T` of locally finite mass, its mass measure is
exactly `‖T‖` restricted to `A`, and its total mass is `‖T‖ A`, even when this value is infinite.
Thus a Borel restriction of a finite-mass current has finite mass. It vanishes exactly when
`‖T‖ A = 0`, is additive on disjoint sets, is linear in `T` on currents of locally finite mass,
satisfies `(T ⌞ A) ⌞ B = T ⌞ (A ∩ B)`, commutes with open restriction and proper smooth pushforward,
and is `T` itself for `A = Ω`. Its boundary need not have locally finite mass.

## Main declarations

* `Distribution.extendL1`: the extension of `T` to `L¹(‖T‖; F)`.
* `Distribution.extendL1_toLp`, `Distribution.opNorm_extendL1_le`, `Distribution.extendL1_unique`:
  it extends `T`, has norm at most one, and is the only continuous extension.
* `Distribution.massRestrict`: the Borel restriction `T ⌞ A`.
* `Distribution.enorm_massRestrict_apply_le`: `|(T ⌞ A) φ| ≤ ∫_A ‖φ‖ d‖T‖`.
* `Distribution.mass_massRestrict_le`, `Distribution.massMeasure_massRestrict_le`: the mass
  bounds `M(T ⌞ A) ≤ ‖T‖ A` and `‖T ⌞ A‖ ≤ ‖T‖ ⌞ A`.
* `Distribution.massMeasure_massRestrict`, `Distribution.mass_massRestrict`: exact mass-measure
  localization and total mass for `T` of locally finite mass.
* `Distribution.massRestrict_eq_zero_iff`: a restriction of `T` of locally finite mass vanishes
  exactly on sets of zero mass measure.
* `Distribution.massRestrict_apply_eq_zero_of_ae`, `Distribution.massRestrict_apply_eq_apply_of_ae`:
  `(T ⌞ A) φ` is `0` when `φ` vanishes `‖T‖`-a.e. on `A`, and `T φ` when it vanishes off `A`.
* `Distribution.dsupport_massRestrict_subset`: `T ⌞ A` is supported in the support of `T`.
* `Distribution.tendsto_apply_smulLeftCLM_massRestrict`: smooth multiples `T (fᵢ φ)` converge to
  `(T ⌞ A) φ` when the bounded smooth functions `fᵢ` converge pointwise on `Ω` to `1_A`.
* `Distribution.continuous_apply_smulLeftCLM_smoothTransition`: continuity of smooth-transition
  approximants to Borel restriction in the level parameter.
* `Distribution.massRestrict_add`, `Distribution.massRestrict_smul`,
  `Distribution.massRestrict_neg`, `Distribution.massRestrict_sub`: linearity in the current.
* `Distribution.massRestrict_massRestrict`: iterated Borel restriction `(T ⌞ A) ⌞ B = T ⌞ (A ∩ B)`.
* `Distribution.measurable_massRestrict_lt_apply`: `t ↦ (T ⌞ {u < t}) φ` is Borel measurable.
* `Distribution.massRestrict_comp_monoCLM`, `Distribution.massRestrict_comp_pullbackCLM`:
  Borel restriction commutes with open restriction and proper smooth pushforward.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.5 and §4.1.7 (currents representable by
  integration, their extension to `‖T‖`-summable forms, and the restriction `T ⌞ A`).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (the restriction of a
  current of locally finite mass to a Borel set).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped BoundedContinuousFunction ENNReal Distributions Topology

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
  rw [one_mul, LinearMap.coe_ofClass, ContinuousLinearMap.coe_coe, ← eNorm_le_iff_norm_le,
    TestFunction.enorm_toLp_one]
  exact enorm_apply_le_lintegral_massMeasure hT φ

variable {A B : Set Ω}

variable [CompleteSpace F]

/-- Test functions are dense in `L¹(‖T‖; F)`. In infinite dimension `‖T‖ = 0`, so `L¹(‖T‖; F)` is
trivial. -/
private theorem denseRange_toLp_massMeasure :
    DenseRange (TestFunction.toLp (n := n) (F := F) 1 (massMeasure T)) := by
  by_cases hE : FiniteDimensional ℝ E
  · exact TestFunction.denseRange_toLp ENNReal.one_ne_top
  have h0 : ∀ μ : Measure Ω, μ = 0 → ∀ f : Lp F 1 μ, f = 0 := by
    rintro μ rfl f
    exact norm_eq_zero.1 (Lp.norm_measure_zero f)
  exact Function.Surjective.denseRange fun f =>
    ⟨0, by rw [map_zero, h0 _ (massMeasure_eq_zero_of_not_finiteDimensional hE) f]⟩

/-- `extendL1 T` extends `T`: on the class of a test function it is the value of `T`. -/
@[simp]
theorem extendL1_toLp (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    extendL1 T (TestFunction.toLp 1 (massMeasure T) φ) = T φ := by
  rw [extendL1]
  exact LinearMap.extendOfNorm_eq (f := (T : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ))
    denseRange_toLp_massMeasure
    ⟨1, norm_apply_le_one_mul hT⟩ φ

/-- **Mass bound for the extension.** `|extendL1 T f| ≤ ∫ ‖f‖ d‖T‖`. -/
theorem norm_extendL1_apply_le (f : Lp F 1 (massMeasure T)) : ‖extendL1 T f‖ ≤ ‖f‖ := by
  by_cases hT : HasLocallyFiniteMass T
  · rw [extendL1]
    simpa using LinearMap.norm_extendOfNorm_apply_le (f := (T : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ))
      denseRange_toLp_massMeasure 1
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
    denseRange_toLp_massMeasure 1 (norm_apply_le_one_mul hT) S
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
  rw [← TestFunction.enorm_indicatorToLp_one _ hA, massRestrict_apply, eNorm_le_iff_norm_le]
  exact norm_extendL1_apply_le _

/-- A Borel restriction has locally finite mass. -/
theorem hasLocallyFiniteMass_massRestrict (hA : MeasurableSet A) :
    HasLocallyFiniteMass (massRestrict T hA) := by
  rw [funext (massRestrict_apply hA)]
  exact hasLocallyFiniteMass_comp_indicatorToLp hA

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

/-- A current is the sum of its restrictions to a measurable set and its complement. -/
theorem massRestrict_add_massRestrict_compl_apply (hT : HasLocallyFiniteMass T)
    (hA : MeasurableSet A) (φ : 𝓓^{n}(Ω, F)) :
    massRestrict T hA φ + massRestrict T hA.compl φ = T φ := by
  have h := congrArg (fun S : 𝓓^{n}(Ω, F) →L[ℝ] ℝ => S φ)
    (massRestrict_union (T := T) hA hA.compl disjoint_compl_right)
  simpa [massRestrict_univ_apply hT] using h.symm

/-- **Mass measure of a Borel restriction.** `‖T ⌞ A‖ ≤ ‖T‖ ⌞ A`. -/
theorem massMeasure_massRestrict_le (hA : MeasurableSet A) :
    massMeasure (massRestrict T hA) ≤ (massMeasure T).restrict A := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · simp [massMeasure_eq_zero_of_not_finiteDimensional hE]
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  exact massMeasure_le_of_enorm_apply_le _ (enorm_massRestrict_apply_le hA)

/-- Restricting a current of locally finite mass restricts its mass measure exactly.
No finiteness of the total mass or regularity of the boundary is required. -/
@[simp]
theorem massMeasure_massRestrict (hT : HasLocallyFiniteMass T) (hA : MeasurableSet A) :
    massMeasure (massRestrict T hA) = (massMeasure T).restrict A := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · simp [massMeasure_eq_zero_of_not_finiteDimensional hE]
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let μ := massMeasure (massRestrict T hA)
  let ν := massMeasure (massRestrict T hA.compl)
  have hsplit : massMeasure T ≤ μ + ν := by
    apply massMeasure_le_of_enorm_apply_le
    intro φ
    rw [lintegral_add_measure,
      ← massRestrict_add_massRestrict_compl_apply hT hA φ]
    exact (eNorm_add_le _ _).trans (add_le_add
      (enorm_apply_le_lintegral_massMeasure (hasLocallyFiniteMass_massRestrict hA) φ)
      (enorm_apply_le_lintegral_massMeasure (hasLocallyFiniteMass_massRestrict hA.compl) φ))
  have hzero : ν.restrict A = 0 := by
    apply le_antisymm _ bot_le
    calc ν.restrict A ≤ ((massMeasure T).restrict Aᶜ).restrict A :=
          Measure.restrict_mono_measure (massMeasure_massRestrict_le hA.compl) A
      _ = 0 := by rw [Measure.restrict_restrict hA]; simp
  apply le_antisymm (massMeasure_massRestrict_le hA)
  calc (massMeasure T).restrict A ≤ (μ + ν).restrict A :=
        Measure.restrict_mono_measure hsplit A
    _ = μ.restrict A := by rw [Measure.restrict_add, hzero, add_zero]
    _ ≤ μ := Measure.restrict_le_self

/-- **Mass of a Borel restriction.** `M(T ⌞ A) ≤ ‖T‖ A`; in particular a Borel restriction to a
set of finite `‖T‖`-measure has finite mass. -/
theorem mass_massRestrict_le (hA : MeasurableSet A) :
    mass (massRestrict T hA) ≤ massMeasure T A := by
  rw [← massMeasure_univ (hasLocallyFiniteMass_massRestrict hA)]
  simpa using Measure.le_iff'.1 (massMeasure_massRestrict_le hA) univ

/-- The total mass of a Borel restriction is the mass measure of its restricting set,
including when that value is infinite. -/
@[simp]
theorem mass_massRestrict (hT : HasLocallyFiniteMass T) (hA : MeasurableSet A) :
    mass (massRestrict T hA) = massMeasure T A := by
  rw [← massMeasure_univ (hasLocallyFiniteMass_massRestrict hA),
    massMeasure_massRestrict hT hA, Measure.restrict_apply_univ]

/-- A Borel restriction to a `‖T‖`-null set is zero. -/
theorem massRestrict_eq_zero (hA : MeasurableSet A) (hA0 : massMeasure T A = 0) :
    massRestrict T hA = 0 := by
  ext φ
  have h := enorm_massRestrict_apply_le (T := T) hA φ
  rw [Measure.restrict_eq_zero.2 hA0, lintegral_zero_measure, nonpos_iff_eq_zero,
    eNorm_eq_zero] at h
  simpa using h

/-- A Borel restriction of a locally finite-mass current vanishes if and only if the
restricting set has zero mass measure. -/
@[simp]
theorem massRestrict_eq_zero_iff (hT : HasLocallyFiniteMass T) (hA : MeasurableSet A) :
    massRestrict T hA = 0 ↔ massMeasure T A = 0 := by
  rw [← mass_massRestrict hT hA, mass_eq_zero_iff]
  exact ⟨fun h => by simp [h], fun h => ContinuousLinearMap.ext fun φ => congrFun h φ⟩

/-- The Borel restriction of the zero functional is zero. -/
@[simp]
theorem massRestrict_zero (hA : MeasurableSet A) :
    massRestrict (0 : 𝓓^{n}(Ω, F) →L[ℝ] ℝ) hA = 0 := by
  refine massRestrict_eq_zero hA (measure_mono_null (subset_univ A) ?_)
  rw [massMeasure_univ (by simpa using hasLocallyFiniteMass_zero)]
  simp [mass_zero]

/-- A Borel restriction vanishes on a test that is `‖T‖`-almost everywhere zero on the
restricting set. -/
theorem massRestrict_apply_eq_zero_of_ae (hA : MeasurableSet A) {φ : 𝓓^{n}(Ω, F)}
    (hφ : ∀ᵐ x ∂massMeasure T, x ∈ A → φ x = 0) : massRestrict T hA φ = 0 := by
  have h0 : ∫⁻ x in A, ‖φ x‖ₑ ∂massMeasure T = 0 :=
    (lintegral_congr_ae ((ae_restrict_iff' hA).2 (hφ.mono fun x hx hxA => by
      simp [hx hxA]))).trans lintegral_zero
  simpa [h0] using enorm_massRestrict_apply_le (T := T) hA φ

/-- A Borel restriction of a current of locally finite mass agrees with the current on a test
that is `‖T‖`-almost everywhere zero off the restricting set. -/
theorem massRestrict_apply_eq_apply_of_ae (hT : HasLocallyFiniteMass T) (hA : MeasurableSet A)
    {φ : 𝓓^{n}(Ω, F)} (hφ : ∀ᵐ x ∂massMeasure T, x ∉ A → φ x = 0) :
    massRestrict T hA φ = T φ := by
  rw [← massRestrict_add_massRestrict_compl_apply hT hA φ,
    massRestrict_apply_eq_zero_of_ae hA.compl hφ, add_zero]

/-- A Borel restriction is supported in the support of the current. -/
theorem dsupport_massRestrict_subset (hA : MeasurableSet A) :
    dsupport (massRestrict T hA) ⊆ dsupport T := by
  refine compl_subset_compl.1 fun x hx => (notMem_dsupport_iff x).2
    ⟨(dsupport T)ᶜ, fun φ hφ => massRestrict_apply_eq_zero_of_ae hA ?_,
      isClosed_dsupport.isOpen_compl, hx⟩
  by_cases hT : HasLocallyFiniteMass T
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (massMeasure_compl_dsupport hT)] with y hy _
    exact image_eq_zero_of_notMem_tsupport fun h => hφ h (not_not.1 hy)
  · simp [massMeasure_of_not_hasLocallyFiniteMass hT]

/-- **Smooth multiples converge to the Borel restriction.** If smooth functions `fᵢ` are
uniformly bounded on `Ω` and converge pointwise on `Ω` to the indicator of a measurable set
`A ⊆ Ω`, then `T (fᵢ φ) → (T ⌞ A) φ` for every test `φ`, by dominated convergence in
`L¹(‖T‖; F)`. -/
theorem tendsto_apply_smulLeftCLM_massRestrict (hT : HasLocallyFiniteMass T)
    (hA : MeasurableSet A) {f : ℕ → E → ℝ} (hf : ∀ i, ContDiff ℝ n (f i)) {C : ℝ}
    (hfC : ∀ i, ∀ x ∈ Ω, |f i x| ≤ C)
    (hlim : ∀ x : Ω, Tendsto (fun i => f i x) atTop (𝓝 (A.indicator 1 x)))
    (φ : 𝓓^{n}(Ω, F)) :
    Tendsto (fun i => T (TestFunction.smulLeftCLM (hf i) φ)) atTop
      (𝓝 (massRestrict T hA φ)) := by
  simp_rw [massRestrict_apply, ← extendL1_toLp hT]
  refine ((extendL1 T).continuous.tendsto _).comp ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm (i : ℕ) :
      ‖TestFunction.toLp 1 (massMeasure T) (TestFunction.smulLeftCLM (hf i) φ) -
          TestFunction.indicatorToLp 1 (massMeasure T) hA φ‖ =
        (∫⁻ x, ‖(f i x - A.indicator 1 x) • φ x‖ₑ ∂massMeasure T).toReal := by
    rw [TestFunction.toLp_apply, TestFunction.indicatorToLp_apply, ← MemLp.toLp_sub,
      Lp.norm_toLp, eLpNorm_one_eq_lintegral_eNorm]
    · refine congrArg ENNReal.toReal (lintegral_congr fun x => ?_)
      by_cases hx : x ∈ A <;> simp [hx, sub_smul]
    · exact ((TestFunction.memLp_subtype (p := 1) _).sub
        ((TestFunction.memLp_subtype φ).indicator hA.nullMeasurableSet)).aestronglyMeasurable
  simp_rw [hnorm]
  rw [← ENNReal.toReal_zero]
  refine (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ?_
  rw [← lintegral_zero (μ := massMeasure T)]
  refine tendsto_lintegral_of_dominated_convergence' (fun x => (‖C‖ₑ + 1) * ‖φ x‖ₑ)
    (fun i => ?_) (fun i => ae_of_all _ fun x => ?_) ?_ (ae_of_all _ fun x => ?_)
  · exact ((TestFunction.memLp_subtype (p := 1) (TestFunction.smulLeftCLM (hf i) φ)).sub
      ((TestFunction.memLp_subtype φ).indicator hA.nullMeasurableSet)).aestronglyMeasurable
      |>.eNorm.congr (ae_of_all _ fun x => by by_cases hx : x ∈ A <;> simp [hx, sub_smul])
  · dsimp only
    rw [eNorm_smul]
    gcongr
    refine (eNorm_sub_le).trans (add_le_add ?_ ?_)
    · rw [← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal ((hfC i x x.property).trans (le_abs_self C))
    · by_cases hx : x ∈ A <;> simp [hx]
  · rw [lintegral_const_mul' _ _ (by simp), ← TestFunction.enorm_toLp_one]
    exact ENNReal.mul_ne_top (by simp) eNorm_ne_top
  · have h := ENNReal.Tendsto.mul_const ((hlim x).sub_const (A.indicator 1 x)).eNorm
      (Or.inr eNorm_ne_top) (b := ‖φ x‖ₑ)
    simpa [sub_self, eNorm_smul] using h

/-- Continuity of `s ↦ S (ψ(c (s - u ·)) • η)` for a locally finite-mass functional `S`. -/
theorem continuous_apply_smulLeftCLM_smoothTransition {S : 𝓓^{n}(Ω, F) →L[ℝ] ℝ}
    (hS : HasLocallyFiniteMass S) {u : E → ℝ} (hu : ContDiff ℝ n u)
    (η : 𝓓^{n}(Ω, F)) (c : ℝ) :
    Continuous fun s : ℝ =>
      S (TestFunction.smulLeftCLM (hu.smoothTransition_mul_sub c s) η) := by
  have hmem (s : ℝ) : MemLp (fun x : Ω =>
      Real.smoothTransition (c * (s - u x)) • η x) 1 (massMeasure S) := by
    simpa [TestFunction.smulLeftCLM_apply] using TestFunction.memLp_subtype (p := 1)
      (μ := massMeasure S) (TestFunction.smulLeftCLM (hu.smoothTransition_mul_sub c s) η)
  simp_rw [← extendL1_toLp hS]
  refine (extendL1 S).continuous.comp (continuous_iff_continuousAt.2 fun s₀ => ?_)
  have htoLp (s : ℝ) :
      TestFunction.toLp 1 (massMeasure S)
          (TestFunction.smulLeftCLM (hu.smoothTransition_mul_sub c s) η) = (hmem s).toLp _ := by
    rw [TestFunction.toLp_apply, MemLp.toLp_eq_toLp_iff]
    exact ae_of_all _ fun x => by simp [TestFunction.smulLeftCLM_apply]
  simp_rw [ContinuousAt, htoLp]
  refine TestFunction.tendsto_toLp_smul_of_dominated ENNReal.one_ne_top hmem (hmem s₀) 2
    (.of_forall fun s x _ => (abs_sub _ _).trans <| by
      linarith [Real.smoothTransition.abs_le_one (c * (s - u x)),
        Real.smoothTransition.abs_le_one (c * (s₀ - u x))])
    fun x _ => (Real.smoothTransition.continuous.comp
      (continuous_const.mul (continuous_id.sub continuous_const))).tendsto s₀

/-! ### Linearity, iterated restriction, and open restriction -/

/-- Borel restriction depends only on the restricting set, not on its measurability proof. -/
theorem massRestrict_congr_set {A₁ A₂ : Set Ω} (hA₁ : MeasurableSet A₁)
    (hA₂ : MeasurableSet A₂) (h : A₁ = A₂) :
    massRestrict T hA₁ = massRestrict T hA₂ := by
  subst h
  rfl

/-- If measurable sets `A j ⊆ Ω` converge pointwise to `B` (membership stabilizes at each point),
then `(T ⌞ A j) φ → (T ⌞ B) φ` for every test `φ`. -/
theorem tendsto_massRestrict_of_eventually_iff {A : ℕ → Set Ω} {B : Set Ω}
    (hA : ∀ j, MeasurableSet (A j)) (hB : MeasurableSet B)
    (hlim : ∀ x : Ω, ∀ᶠ j in atTop, x ∈ A j ↔ x ∈ B) (φ : 𝓓^{n}(Ω, F)) :
    Tendsto (fun j => massRestrict T (hA j) φ) atTop (𝓝 (massRestrict T hB φ)) := by
  simp_rw [massRestrict_apply, TestFunction.indicatorToLp_apply]
  refine ((extendL1 T).continuous.tendsto _).comp ?_
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun j => (A j).indicator fun y : Ω => φ y)
    (fun j => (TestFunction.memLp_subtype (p := 1) φ).indicator (hA j).nullMeasurableSet)
    (B.indicator fun y : Ω => φ y)
    ((TestFunction.memLp_subtype (p := 1) φ).indicator hB.nullMeasurableSet)]
  refine TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (C := 2) ENNReal.one_ne_top
    (.of_forall fun j =>
      ((TestFunction.memLp_subtype (p := 1) φ).indicator
        (hA j).nullMeasurableSet).aestronglyMeasurable)
    (TestFunction.memLp_subtype (p := 1) φ)
    (.of_forall fun j => ae_of_all _ fun x => eNorm_sub_le.trans <| by
      rw [ENNReal.coe_ofNat, two_mul]
      exact add_le_add (eNorm_indicator_le_eNorm_self _ _) (eNorm_indicator_le_eNorm_self _ _))
    (ae_of_all _ fun x => tendsto_const_nhds.congr' <|
      (hlim x).mono fun j hj => by by_cases hx : x ∈ B <;> simp [hj, hx])

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
private theorem enorm_smul_sub_indicator_le {U : Opens E} (φ : 𝓓^{n}(U, F)) (B : Set U)
    (c : ℝ) (x : U) :
    ‖c • φ x - B.indicator (fun y : U => φ y) x‖ₑ ≤
      ‖c - (B ∩ (↑) ⁻¹' tsupport φ).indicator (1 : U → ℝ) x‖ₑ * ‖(φ : E →ᵇ F)‖ₑ := by
  by_cases hxK : (x : E) ∈ tsupport φ
  · have hxpre : x ∈ ((↑) ⁻¹' tsupport φ : Set U) := mem_preimage.2 hxK
    have hpoint : c • φ x - B.indicator (fun y : U => φ y) x =
        (c - (B ∩ (↑) ⁻¹' tsupport φ).indicator (1 : U → ℝ) x) • φ x := by
      by_cases hxB : x ∈ B <;> simp [hxB, hxpre, sub_smul]
    rw [hpoint, eNorm_smul]
    gcongr
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (BoundedContinuousFunction.norm_coe_le_norm (φ : E →ᵇ F) x)
  · have hφ0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hxK
    by_cases hxB : x ∈ B <;> simp [hxB, hφ0]

/-- If scalar test functions `χ m` approximate `1_{A ∩ K}` in `L¹(μ; ℝ)` on
`K = (↑) ⁻¹' tsupport φ`, then `S (χ m • φ) → (S ⌞ A) φ` for every functional `S` of locally
finite mass with `‖S‖ ≤ μ`. -/
theorem tendsto_apply_smulLeftCLM_of_tendsto_lintegral_indicator {μ : Measure Ω}
    (hA : MeasurableSet A) (φ : 𝓓^{n}(Ω, F)) {χ : ℕ → 𝓓(Ω, ℝ)}
    (hχ : Tendsto (fun m => ∫⁻ x : Ω,
      ‖χ m x - (A ∩ (↑) ⁻¹' tsupport φ).indicator (1 : Ω → ℝ) x‖ₑ ∂μ) atTop (𝓝 0))
    (hT : HasLocallyFiniteMass T) (hμ : massMeasure T ≤ μ) :
    Tendsto (fun m => T (TestFunction.smulLeftCLM
        ((χ m).contDiff.of_le (WithTop.coe_le_coe.2 le_top)) φ))
      atTop (𝓝 (massRestrict T hA φ)) := by
  simp_rw [massRestrict_apply, ← extendL1_toLp hT]
  refine ((extendL1 T).continuous.tendsto _).comp ?_
  rw [tendsto_iff_eNorm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_mul] using
      ENNReal.Tendsto.mul_const hχ (b := ‖(φ : E →ᵇ F)‖ₑ) (Or.inr eNorm_ne_top))
    (fun _ => bot_le) fun m => ?_
  rw [TestFunction.toLp_apply, TestFunction.indicatorToLp_apply, ← MemLp.toLp_sub, Lp.eNorm_toLp,
    eLpNorm_one_eq_lintegral_eNorm (((TestFunction.memLp_subtype (p := 1) _).sub
      ((TestFunction.memLp_subtype φ).indicator hA.nullMeasurableSet)).aestronglyMeasurable),
    ← lintegral_mul_const' _ _ eNorm_ne_top]
  refine (lintegral_mono fun x => ?_).trans (lintegral_mono' hμ le_rfl)
  simpa only [Pi.sub_apply, TestFunction.smulLeftCLM_apply] using
    enorm_smul_sub_indicator_le φ A (χ m x) x

/-- Borel restriction is additive in the current on currents of locally finite mass. -/
theorem massRestrict_add {T S : 𝓓^{n}(Ω, F) →L[ℝ] ℝ} (hT : HasLocallyFiniteMass T)
    (hS : HasLocallyFiniteMass S) (hA : MeasurableSet A) :
    massRestrict (T + S) hA = massRestrict T hA + massRestrict S hA := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · ext φ; simp [TestFunction.eq_zero_of_not_finiteDimensional φ hE]
  ext φ
  let μ := massMeasure (T + S) + massMeasure T + massMeasure S
  have : IsFiniteMeasureOnCompacts μ :=
    ⟨fun _ hC => ENNReal.add_lt_top.2
      ⟨ENNReal.add_lt_top.2 ⟨hC.measure_lt_top, hC.measure_lt_top⟩, hC.measure_lt_top⟩⟩
  obtain ⟨χ, hχ⟩ := TestFunction.exists_tendsto_lintegral_indicator μ hA
    (TestFunction.isCompact_preimage_tsupport φ)
  have hTS : HasLocallyFiniteMass (T + S) := by simpa using hT.add hS
  have hlimTS := tendsto_apply_smulLeftCLM_of_tendsto_lintegral_indicator hA φ hχ hTS
    (fun s => by simp [μ, add_assoc])
  have hlimT := tendsto_apply_smulLeftCLM_of_tendsto_lintegral_indicator hA φ hχ hT
    (fun s => by simp [μ, add_assoc, add_left_comm])
  have hlimS := tendsto_apply_smulLeftCLM_of_tendsto_lintegral_indicator hA φ hχ hS
    (fun s => by simp [μ])
  exact tendsto_nhds_unique hlimTS (hlimT.add hlimS)

/-- Borel restriction commutes with scalar multiplication. -/
@[simp]
theorem massRestrict_smul (a : ℝ) (T : 𝓓^{n}(Ω, F) →L[ℝ] ℝ) (hA : MeasurableSet A) :
    massRestrict (a • T) hA = a • massRestrict T hA := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · ext φ; simp [TestFunction.eq_zero_of_not_finiteDimensional φ hE]
  by_cases ha : a = 0
  · simp [ha]
  by_cases hT : HasLocallyFiniteMass T
  · ext φ
    let μ := massMeasure (a • T) + massMeasure T
    have : IsFiniteMeasureOnCompacts μ :=
      ⟨fun _ hC => ENNReal.add_lt_top.2 ⟨hC.measure_lt_top, hC.measure_lt_top⟩⟩
    obtain ⟨χ, hχ⟩ := TestFunction.exists_tendsto_lintegral_indicator μ hA
      (TestFunction.isCompact_preimage_tsupport φ)
    have haT : HasLocallyFiniteMass (a • T) := by simpa using hT.smul a
    have hlimaT := tendsto_apply_smulLeftCLM_of_tendsto_lintegral_indicator hA φ hχ haT
      (fun s => by simp [μ])
    have hlimT := tendsto_apply_smulLeftCLM_of_tendsto_lintegral_indicator hA φ hχ hT
      (fun s => by simp [μ])
    exact tendsto_nhds_unique hlimaT (hlimT.const_smul a)
  · have haT : ¬HasLocallyFiniteMass (a • T) := fun h => hT <| by
      simpa [smul_smul, inv_mul_cancel₀ ha] using h.smul a⁻¹
    rw [massRestrict_eq_zero (T := T) hA (by simp [massMeasure_of_not_hasLocallyFiniteMass hT]),
      massRestrict_eq_zero (T := a • T) hA (by simp [massMeasure_of_not_hasLocallyFiniteMass haT]),
      smul_zero]

/-- Borel restriction commutes with negation. -/
@[simp]
theorem massRestrict_neg (T : 𝓓^{n}(Ω, F) →L[ℝ] ℝ) (hA : MeasurableSet A) :
    massRestrict (-T) hA = -massRestrict T hA := by
  rw [← neg_one_smul ℝ T, massRestrict_smul]
  exact neg_one_smul ℝ (massRestrict T hA)

/-- Borel restriction commutes with subtraction on currents of locally finite mass. -/
theorem massRestrict_sub {T S : 𝓓^{n}(Ω, F) →L[ℝ] ℝ} (hT : HasLocallyFiniteMass T)
    (hS : HasLocallyFiniteMass S) (hA : MeasurableSet A) :
    massRestrict (T - S) hA = massRestrict T hA - massRestrict S hA := by
  rw [sub_eq_add_neg, massRestrict_add hT (by simpa using hS.neg) hA, massRestrict_neg,
    sub_eq_add_neg]

/-- **Iterated Borel restriction.** Restricting `T ⌞ A` to `B` is restricting `T` to `A ∩ B`. -/
@[simp]
theorem massRestrict_massRestrict (hA : MeasurableSet A) (hB : MeasurableSet B) :
    massRestrict (massRestrict T hA) hB = massRestrict T (hA.inter hB) := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · ext φ; simp [TestFunction.eq_zero_of_not_finiteDimensional φ hE]
  by_cases hT : HasLocallyFiniteMass T
  · ext φ
    obtain ⟨χ, hχ⟩ := TestFunction.exists_tendsto_lintegral_indicator (massMeasure T) hB
      (TestFunction.isCompact_preimage_tsupport φ)
    refine tendsto_nhds_unique (tendsto_apply_smulLeftCLM_of_tendsto_lintegral_indicator hB φ hχ
      (hasLocallyFiniteMass_massRestrict hA)
      ((massMeasure_massRestrict_le hA).trans Measure.restrict_le_self)) ?_
    simp_rw [massRestrict_apply]
    refine ((extendL1 T).continuous.tendsto _).comp ?_
    rw [tendsto_iff_eNorm_sub_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [zero_mul] using
        ENNReal.Tendsto.mul_const hχ (b := ‖(φ : E →ᵇ F)‖ₑ) (Or.inr eNorm_ne_top))
      (fun _ => bot_le) fun m => ?_
    rw [TestFunction.indicatorToLp_apply, TestFunction.indicatorToLp_apply, ← MemLp.toLp_sub,
      Lp.eNorm_toLp, eLpNorm_one_eq_lintegral_eNorm
        ((((TestFunction.memLp_subtype (p := 1) _).indicator hA.nullMeasurableSet).sub
          ((TestFunction.memLp_subtype φ).indicator
            (hA.inter hB).nullMeasurableSet)).aestronglyMeasurable),
      ← lintegral_mul_const' _ _ eNorm_ne_top]
    refine lintegral_mono fun x => ?_
    by_cases hxA : x ∈ A
    · have hAB : (A ∩ B).indicator (fun y : Ω => φ y) x = B.indicator (fun y : Ω => φ y) x := by
        by_cases hxB : x ∈ B <;> simp [hxA, hxB]
      simpa [Pi.sub_apply, hxA, hAB] using enorm_smul_sub_indicator_le φ B (χ m x) x
    · simp [hxA]
  · rw [massRestrict_eq_zero hA (by simp [massMeasure_of_not_hasLocallyFiniteMass hT]),
      massRestrict_zero,
      massRestrict_eq_zero (hA.inter hB) (by simp [massMeasure_of_not_hasLocallyFiniteMass hT])]

/-- **Borel restriction commutes with open restriction.** For `Ω' ≤ Ω` and `T` of locally finite
mass on `Ω`, restricting `T ⌞ A` to tests on `Ω'` is restricting `T|_{Ω'}` to `A ∩ Ω'`. -/
theorem massRestrict_comp_monoCLM {Ω' : Opens E} {T : 𝓓^{n}(Ω, F) →L[ℝ] ℝ}
    (hT : HasLocallyFiniteMass T) (h : Ω' ≤ Ω) (hA : MeasurableSet A) :
    massRestrict T hA ∘L (TestFunction.monoCLM ℝ : 𝓓^{n}(Ω', F) →L[ℝ] 𝓓^{n}(Ω, F)) =
      massRestrict (T ∘L TestFunction.monoCLM ℝ)
        (hA.preimage (continuous_inclusion h).measurable) := by
  -- Approximate `1_{A' ∩ supp φ}` in `L¹(‖T'‖)` by smooth scalar tests `χ m` on `Ω'`,
  -- then compare the limits of `T' (χ m • φ) = T (χΩ m • φΩ)` via `extendL1 T`.
  by_cases hE : FiniteDimensional ℝ E
  swap
  · ext φ; simp [TestFunction.eq_zero_of_not_finiteDimensional φ hE]
  let A' : Set Ω' := Set.inclusion h ⁻¹' A
  have hA' : MeasurableSet A' := hA.preimage (continuous_inclusion h).measurable
  let T' : 𝓓^{n}(Ω', F) →L[ℝ] ℝ := T ∘L TestFunction.monoCLM ℝ
  have hT' : HasLocallyFiniteMass T' := hT.comp_monoCLM
  ext φ
  let φΩ : 𝓓^{n}(Ω, F) := TestFunction.monoCLM ℝ φ
  obtain ⟨χ, hχ⟩ := TestFunction.exists_tendsto_lintegral_indicator (massMeasure T') hA'
    (TestFunction.isCompact_preimage_tsupport φ)
  have hχc (m : ℕ) : ContDiff ℝ n (χ m) := (χ m).contDiff.of_le (WithTop.coe_le_coe.2 le_top)
  refine tendsto_nhds_unique ?_
    (tendsto_apply_smulLeftCLM_of_tendsto_lintegral_indicator hA' φ hχ hT' le_rfl)
  let χΩ (m : ℕ) : 𝓓(Ω, ℝ) := TestFunction.monoCLM ℝ (χ m)
  have hχΩc (m : ℕ) : ContDiff ℝ n (χΩ m) := (χΩ m).contDiff.of_le (WithTop.coe_le_coe.2 le_top)
  have heval (m : ℕ) : T' (TestFunction.smulLeftCLM (hχc m) φ) =
      extendL1 T (TestFunction.toLp 1 (massMeasure T)
        (TestFunction.smulLeftCLM (hχΩc m) φΩ)) := by
    rw [extendL1_toLp hT, ContinuousLinearMap.comp_apply]
    exact congrArg T <| DFunLike.ext _ _ fun x => by simp [φΩ, χΩ, TestFunction.monoCLM_apply, h]
  rw [ContinuousLinearMap.comp_apply, massRestrict_apply]
  refine (tendsto_congr heval).2 (((extendL1 T).continuous.tendsto _).comp ?_)
  -- Reduce the `L¹(‖T‖)` error on `Ω` to the `L¹(‖T'‖)` error on `Ω'` via
  -- `map_massMeasure_comp_monoCLM`.
  rw [tendsto_iff_eNorm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_mul] using
      ENNReal.Tendsto.mul_const hχ (b := ‖(φ : E →ᵇ F)‖ₑ) (Or.inr eNorm_ne_top))
    (fun _ => bot_le) fun m => ?_
  rw [TestFunction.toLp_apply, TestFunction.indicatorToLp_apply, ← MemLp.toLp_sub, Lp.eNorm_toLp,
    eLpNorm_one_eq_lintegral_eNorm (((TestFunction.memLp_subtype (p := 1) _).sub
      ((TestFunction.memLp_subtype φΩ).indicator hA.nullMeasurableSet)).aestronglyMeasurable),
    ← lintegral_mul_const' _ _ eNorm_ne_top]
  have hvanish : ∫⁻ x : Ω, ‖TestFunction.smulLeftCLM (hχΩc m) φΩ x -
        A.indicator (fun z : Ω => φΩ z) x‖ₑ ∂massMeasure T =
      ∫⁻ x in (↑) ⁻¹' (Ω' : Set E), ‖TestFunction.smulLeftCLM (hχΩc m) φΩ x -
        A.indicator (fun z : Ω => φΩ z) x‖ₑ ∂massMeasure T :=
    (setLIntegral_eq_of_support_subset fun x hx => by
      by_contra hxΩ'
      have hφ0 : φΩ x = 0 := image_eq_zero_of_notMem_tsupport fun hts => hxΩ' <|
        φ.tsupport_subset (by simpa [φΩ, TestFunction.monoCLM_apply, h] using hts)
      exact hx (by by_cases hxA : x ∈ A <;> simp [hxA, hφ0])).symm
  have hmap : (massMeasure T').map (Set.inclusion h) =
      (massMeasure T).restrict ((↑) ⁻¹' (Ω' : Set E)) := by
    rw [← massMeasure_coe_linearMap T', ← massMeasure_coe_linearMap T]
    exact map_massMeasure_comp_monoCLM (T := (T : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ)) hT h
  simp_rw [Pi.sub_apply]
  rw [hvanish, ← hmap]
  refine ((Opens.isOpenEmbedding_of_le h).measurableEmbedding.lintegral_map (f := _)).trans_le
    (lintegral_mono fun (y : Ω') => ?_)
  have hyA_iff : Set.inclusion h y ∈ A ↔ y ∈ A' := mem_preimage.symm
  have hpt : TestFunction.smulLeftCLM (hχΩc m) φΩ (Set.inclusion h y) -
      A.indicator (fun z : Ω => φΩ z) (Set.inclusion h y) =
      χ m y • φ y - A'.indicator (fun z : Ω' => φ z) y := by
    by_cases hyA : y ∈ A' <;>
      simp [A', hyA, hyA_iff, φΩ, χΩ, TestFunction.monoCLM_apply, h]
  simpa only [hpt] using enorm_smul_sub_indicator_le φ A' (χ m y) y

/-- For any functional `S`, `t ↦ (S ⌞ {u < t}) φ` is left-continuous in `t`, hence Borel
measurable as a pointwise limit of dyadic step functions from below. -/
theorem measurable_massRestrict_lt_apply (S : 𝓓^{n}(Ω, F) →L[ℝ] ℝ) {u : E → ℝ}
    (hu : Measurable fun x : Ω => u x) (φ : 𝓓^{n}(Ω, F)) :
    Measurable fun t : ℝ =>
      massRestrict S (measurableSet_lt hu (measurable_const (a := t))) φ := by
  let hA (s : ℝ) : MeasurableSet {x : Ω | u x < s} :=
    measurableSet_lt hu (measurable_const (a := s))
  let step (m : ℕ) (t : ℝ) : ℝ := ((⌊(2 : ℝ) ^ m * t⌋ : ℝ) - 1) / (2 : ℝ) ^ m
  have hstep_meas (m : ℕ) : Measurable fun t : ℝ => massRestrict S (hA (step m t)) φ :=
    (measurable_of_countable (fun k : ℤ =>
      massRestrict S (hA (((k : ℝ) - 1) / (2 : ℝ) ^ m)) φ)).comp
      (measurable_const.mul measurable_id).floor
  refine measurable_of_tendsto_metrizable hstep_meas (tendsto_pi_nhds.2 fun t => ?_)
  have hstep_lt (m : ℕ) : step m t < t := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ m)]
    linarith [Int.floor_le ((2 : ℝ) ^ m * t)]
  have hstep_tendsto : Tendsto (fun m => step m t) atTop (𝓝 t) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using tendsto_const_nhds.sub ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (by positivity : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).const_mul 2))
      tendsto_const_nhds (fun m => ?_) (fun m => (hstep_lt m).le)
    have hpow : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    have hlhs : t - 2 * ((2 : ℝ) ^ m)⁻¹ = ((2 : ℝ) ^ m * t - 2) / (2 : ℝ) ^ m := by field_simp
    rw [hlhs, div_le_div_iff_of_pos_right hpow]
    linarith [Int.sub_one_lt_floor ((2 : ℝ) ^ m * t)]
  refine tendsto_massRestrict_of_eventually_iff (fun m => hA (step m t)) (hA t) (fun x => ?_) φ
  by_cases hxt : u x < t
  · filter_upwards [(tendsto_order.1 hstep_tendsto).1 _ hxt] with m hm
    exact ⟨fun _ => hxt, fun _ => hm⟩
  · exact .of_forall fun m => ⟨fun h => (hxt (h.trans (hstep_lt m))).elim, fun h => (hxt h).elim⟩

/-- **Borel restriction commutes with proper smooth pushforward.** For `T` of locally finite mass
on `Ω`, a smooth map `Φ` on `Ω` proper over `Ω'`, and a measurable set `B ⊆ Ω'`,
`(Φ_# T) ⌞ B = Φ_# (T ⌞ Φ⁻¹(B))`. -/
theorem massRestrict_comp_pullbackCLM {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] {Ω' : Opens E'} {k : ℕ}
    {Φ : E → E'} {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}
    {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)}
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ} (hT : HasLocallyFiniteMass T)
    {B : Set Ω'} (hB : MeasurableSet B) :
    massRestrict (T ∘L TestFunction.pullbackCLM Φ hΦ hΦp) hB =
      massRestrict T
        ((Ω'.isOpen.measurableSet.subtype_image hB).preimage
          hΦ.continuousOn.domRestrict.measurable) ∘L
        TestFunction.pullbackCLM Φ hΦ hΦp := by
  set P : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) :=
    TestFunction.pullbackCLM Φ hΦ hΦp
  by_cases hE : FiniteDimensional ℝ E
  swap
  · have hP : P = 0 := by ext1 φ; exact TestFunction.eq_zero_of_not_finiteDimensional (P φ) hE
    simp [hP]
  have hΦc : Continuous fun x : Ω => Φ x := hΦ.continuousOn.domRestrict
  set A : Set Ω := (Ω : Set E).domRestrict Φ ⁻¹' ((↑) '' B : Set E')
  have hA : MeasurableSet A :=
    (Ω'.isOpen.measurableSet.subtype_image hB).preimage hΦ.continuousOn.domRestrict.measurable
  rw [massRestrict_congr_set (T := T) _ hA rfl]
  ext φ
  cases isEmpty_or_nonempty Ω' with
  | inl hE =>
    have hφ0 : φ = 0 := DFunLike.ext _ _ fun z =>
      image_eq_zero_of_notMem_tsupport fun h => hE.false ⟨z, φ.tsupport_subset h⟩
    simp [hφ0]
  | inr hne =>
  classical
  let g : Ω → Ω' := fun x => if hx : Φ x ∈ Ω' then ⟨Φ x, hx⟩ else hne.some
  have hg : Measurable g := Measurable.dite (s := {x : Ω | Φ x ∈ (Ω' : Set E')})
    ((hΦc.comp continuous_subtypeVal).subtype_mk fun p => p.property).measurable
    measurable_const (Ω'.isOpen.preimage hΦc).measurableSet
  let CΩ : Set Ω := (↑) ⁻¹' ((Ω : Set E) ∩ Φ ⁻¹' tsupport φ)
  have hCΩ : IsCompact CΩ :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage'
      (hΦp _ φ.hasCompactSupport φ.tsupport_subset)
      (by rw [Subtype.range_coe]; exact inter_subset_left)
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  have : IsFiniteMeasure ((massMeasure T).restrict CΩ) := ⟨by simp [hCΩ.measure_lt_top]⟩
  let ν : Measure Ω' := ((massMeasure T).restrict CΩ).map g
  have : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ g
  let μ' : Measure Ω' := massMeasure (T ∘L P) + ν
  have : IsFiniteMeasureOnCompacts μ' :=
    ⟨fun _ hK => ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, measure_lt_top ν _⟩⟩
  let K' : Set Ω' := (↑) ⁻¹' tsupport φ
  have hK' : IsCompact K' := TestFunction.isCompact_preimage_tsupport φ
  -- Approximate `1_{B ∩ supp φ}` in `L¹(μ')` (where `μ' = ‖T ∘L P‖ + g_*(‖T‖ ⌞ CΩ)`) by smooth
  -- scalar test functions `χ m`, then compare the limits of `(T ∘L P)(χ m • φ)` via `extendL1 T`.
  obtain ⟨χ, hχ⟩ := TestFunction.exists_tendsto_lintegral_indicator μ' hB hK'
  have hχc (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (χ m) :=
    (χ m).contDiff.of_le (WithTop.coe_le_coe.2 le_top)
  refine tendsto_nhds_unique (tendsto_apply_smulLeftCLM_of_tendsto_lintegral_indicator hB φ hχ
    hT.comp_pullbackCLM (fun s => by simp [μ', P])) ?_
  rw [ContinuousLinearMap.comp_apply, massRestrict_apply]
  refine (tendsto_congr fun m =>
    (ContinuousLinearMap.comp_apply T P _).trans (extendL1_toLp hT _).symm).2
    (((extendL1 T).continuous.tendsto _).comp ?_)
  -- Bound the `L¹(‖T‖)` error on `Ω` by the `L¹(ν)` error on `Ω'` via `CΩ = Ω ∩ Φ⁻¹(tsupport φ)`.
  rw [tendsto_iff_eNorm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_mul] using (ENNReal.Tendsto.mul_const hχ
      (b := ‖(P φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ) (Or.inr eNorm_ne_top)))
    (fun _ => bot_le) fun m => ?_
  rw [TestFunction.toLp_apply, TestFunction.indicatorToLp_apply, ← MemLp.toLp_sub, Lp.eNorm_toLp,
    eLpNorm_one_eq_lintegral_eNorm (((TestFunction.memLp_subtype (p := 1) _).sub
      ((TestFunction.memLp_subtype (P φ)).indicator hA.nullMeasurableSet)).aestronglyMeasurable),
    ← lintegral_mul_const' _ _ eNorm_ne_top]
  have hvanish : ∫⁻ x : Ω, ‖P (TestFunction.smulLeftCLM (hχc m) φ) x -
        A.indicator (fun z : Ω => P φ z) x‖ₑ ∂massMeasure T =
      ∫⁻ x in CΩ, ‖P (TestFunction.smulLeftCLM (hχc m) φ) x -
        A.indicator (fun z : Ω => P φ z) x‖ₑ ∂massMeasure T :=
    (setLIntegral_eq_of_support_subset fun x hx => by
      by_contra hxC
      have hφx : φ (Φ x) = 0 := image_eq_zero_of_notMem_tsupport fun h => hxC ⟨x.property, h⟩
      have hP1 : P (TestFunction.smulLeftCLM (hχc m) φ) x = 0 := by
        ext v; simp [P, TestFunction.pullbackCLM_apply_of_mem _ x.property, hφx]
      have hP2 : P φ x = 0 := by
        ext v; simp [P, TestFunction.pullbackCLM_apply_of_mem _ x.property, hφx]
      exact hx (by by_cases hxA : x ∈ A <;> simp [hxA, hP1, hP2, ← ofReal_norm])).symm
  have hpoint : ∀ x ∈ CΩ,
      ‖P (TestFunction.smulLeftCLM (hχc m) φ) x -
          A.indicator (fun z : Ω => P φ z) x‖ₑ ≤
        ‖χ m (g x) - (B ∩ K').indicator (1 : Ω' → ℝ) (g x)‖ₑ *
          ‖(P φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ := fun x hxC => by
    have hxΩ' : Φ x ∈ Ω' := φ.tsupport_subset hxC.2
    have hgx : g x = ⟨Φ x, hxΩ'⟩ := by simp [g, hxΩ']
    have hgK : g x ∈ K' := by simpa [K', hgx] using hxC.2
    have hΦg : Φ x = (g x : E') := by simp [hgx]
    have hxAB : x ∈ A ↔ g x ∈ B := by
      simp only [A, mem_preimage, Set.domRestrict_apply, hΦg, Subtype.val_injective.mem_set_image]
    have hP1 : P (TestFunction.smulLeftCLM (hχc m) φ) x = χ m (g x) • P φ x := by
      rw [TestFunction.pullbackCLM_apply_of_mem _ x.property,
        TestFunction.pullbackCLM_apply_of_mem _ x.property, hgx]
      ext v; simp
    have hsub : P (TestFunction.smulLeftCLM (hχc m) φ) x -
        A.indicator (fun z : Ω => P φ z) x =
        (χ m (g x) - (B ∩ K').indicator (1 : Ω' → ℝ) (g x)) • P φ x := by
      rw [hP1]
      by_cases hgB : g x ∈ B
      · simp [hxAB.2 hgB, hgB, hgK, sub_smul]
      · simp [mt hxAB.1 hgB, hgB]
    rw [hsub, eNorm_smul]
    gcongr
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal
      (BoundedContinuousFunction.norm_coe_le_norm (P φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F) x)
  have hf_meas : AEMeasurable (fun y : Ω' =>
      ‖χ m y - (B ∩ K').indicator (1 : Ω' → ℝ) y‖ₑ *
        ‖(P φ : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ) ν :=
    (((χ m).continuous.comp continuous_subtypeVal).aestronglyMeasurable.sub
      (aestronglyMeasurable_const.indicator
        (hB.inter hK'.isClosed.measurableSet))).eNorm.mul_const _
  exact hvanish.trans_le (((setLIntegral_mono' hCΩ.isClosed.measurableSet hpoint).trans_eq
    (lintegral_map' hf_meas hg.aemeasurable).symm).trans
    (lintegral_mono' (fun s => by simp [μ', ν]) le_rfl))

end Distribution
