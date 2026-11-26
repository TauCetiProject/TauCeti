/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Support
public import TauCeti.Analysis.Distribution.TestFunction.Lp
public import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.Distribution.TestFunction.Approximation
import TauCeti.Topology.Instances.ENNReal
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
`‖T‖ A = 0`, is additive on disjoint sets, and is `T` itself for `A = Ω`. Its boundary need not
have locally finite mass. Conversely, a splitting `T = R + R'` into maps of locally finite mass
whose mass measures are `‖T‖ ⌞ A` and `‖T‖ ⌞ Aᶜ` has `R = T ⌞ A`.

## Main declarations

* `Distribution.extendL1`: the extension of `T` to `L¹(‖T‖; F)`.
* `Distribution.extendL1_toLp`, `Distribution.opNorm_extendL1_le`, `Distribution.extendL1_unique`:
  it extends `T`, has norm at most one, and is the only continuous extension.
* `Distribution.extendContinuous`: the extension of `T` to compactly supported continuous tests,
  `φ ↦ extendL1 T φ`, which extends `T` (`Distribution.extendContinuous_monoCLM`) and has mass
  measure `‖T‖` (`Distribution.massMeasure_extendContinuous`).
* `Distribution.apply_eq_zero_of_forall_monoCLM_eq_zero`: a map of locally finite mass that vanishes
  on smooth tests vanishes.
* `Distribution.extendContinuous_unique`: `Distribution.extendContinuous T` is the only extension
  of `T` of locally finite mass.
* `Distribution.massRestrict`: the Borel restriction `T ⌞ A`.
* `Distribution.enorm_massRestrict_apply_le`: `|(T ⌞ A) φ| ≤ ∫_A ‖φ‖ d‖T‖`.
* `Distribution.mass_massRestrict_le`, `Distribution.massMeasure_massRestrict_le`: the mass
  bounds `M(T ⌞ A) ≤ ‖T‖ A` and `‖T ⌞ A‖ ≤ ‖T‖ ⌞ A`.
* `Distribution.massMeasure_massRestrict`, `Distribution.mass_massRestrict`: exact mass-measure
  localization and total mass for `T` of locally finite mass.
* `Distribution.massRestrict_eq_of_massMeasure_eq`: `T = R + R'` with `R`, `R'` of locally finite
  mass, `‖R‖ = ‖T‖ ⌞ A` and `‖R'‖ = ‖T‖ ⌞ Aᶜ` forces `T ⌞ A = R`.
* `Distribution.massRestrict_eq_zero_iff`: a restriction of `T` of locally finite mass vanishes
  exactly on sets of zero mass measure.
* `Distribution.massRestrict_apply_eq_zero_of_ae`, `Distribution.massRestrict_apply_eq_apply_of_ae`:
  `(T ⌞ A) φ` is `0` when `φ` vanishes `‖T‖`-a.e. on `A`, and `T φ` when it vanishes off `A`.
* `Distribution.dsupport_massRestrict_subset`: `T ⌞ A` is supported in the support of `T`.
* `Distribution.tendsto_apply_smulLeftCLM_massRestrict`: smooth multiples `T (fᵢ φ)` converge to
  `(T ⌞ A) φ` when the bounded smooth functions `fᵢ` converge pointwise on `Ω` to `1_A`.
* `Distribution.tendsto_massRestrict_apply`: `(T ⌞ Aᵢ) φ → (T ⌞ B) φ` when `‖T‖`-almost every point
  eventually lies in `Aᵢ` exactly when it lies in `B`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.5 and §4.1.7 (currents representable by
  integration, their extension to `‖T‖`-summable forms, and the restriction `T ⌞ A`).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (the restriction of a
  current of locally finite mass to a Borel set).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Distributions Topology

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

/-! ### Extension to compactly supported continuous tests -/

section Continuous

open TestFunction

omit [CompleteSpace F] in
/-- The **extension of `T` to compactly supported continuous tests**: for a real-linear map `T` on
tests of class `C^n` with locally finite mass, the continuous linear map `φ ↦ extendL1 T φ` on the
compactly supported continuous `F`-valued tests, through the extension `Distribution.extendL1` of
`T` to `L¹(‖T‖; F)`. It extends `T` (`Distribution.extendContinuous_monoCLM`) and its mass measure
is `‖T‖` (`Distribution.massMeasure_extendContinuous`). If `T` does not have locally finite mass,
it is `0`. For finite-dimensional inner product spaces `E` and `F`,
`TauCeti.Analysis.Distribution.Mass.Polar.Vector` shows that it is `φ ↦ ∫ ⟪η x, φ x⟫ d‖T‖` for the
polar vector field `η` of `T`. On a finite-dimensional `E` it is the only linear extension of `T`
with locally finite mass (`Distribution.extendContinuous_unique`). -/
def extendContinuous (T : 𝓕) : 𝓓^{0}(Ω, F) →L[ℝ] ℝ :=
  (extendL1 T).comp (TestFunction.toLp 1 (massMeasure T))

omit [CompleteSpace F] in
/-- Unfolding lemma for `Distribution.extendContinuous`. -/
theorem extendContinuous_apply (φ : 𝓓^{0}(Ω, F)) :
    extendContinuous T φ = extendL1 T (TestFunction.toLp 1 (massMeasure T) φ) :=
  (rfl)

/-- **The extension extends `T`.** On a test of class `C^n`, the extension of a map `T` of locally
finite mass is the value of `T`. -/
@[simp]
theorem extendContinuous_monoCLM (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    extendContinuous T (monoCLM ℝ φ) = T φ := by
  rw [extendContinuous_apply, ← extendL1_toLp hT φ, TestFunction.toLp_apply,
    TestFunction.toLp_apply]
  exact congrArg _ (MemLp.toLp_congr _ _ (.of_eq (funext fun x => by
    simp [coe_monoCLM_of_le zero_le le_rfl])))

/-- **Domination of the extension by the mass measure.** `|extendContinuous T φ| ≤ ∫ ‖φ‖ d‖T‖`. -/
theorem enorm_extendContinuous_apply_le (φ : 𝓓^{0}(Ω, F)) :
    ‖extendContinuous T φ‖ₑ ≤ ∫⁻ x, ‖φ x‖ₑ ∂massMeasure T := by
  rw [extendContinuous_apply, ← TestFunction.enorm_toLp_one]
  exact eNorm_le_iff_norm_le.2 (norm_extendL1_apply_le _)

/-- The extension of `T` to compactly supported continuous tests has locally finite mass. -/
theorem hasLocallyFiniteMass_extendContinuous : HasLocallyFiniteMass (extendContinuous T) :=
  hasLocallyFiniteMass_def.2 fun K hK hKΩ => by
    obtain ⟨C, hC, h⟩ := hasLocallyFiniteMass_def.1
      (TestFunction.hasLocallyFiniteMass_toLp (n := 0) (F := F) 1 (massMeasure T)) K hK hKΩ
    exact ⟨C, hC, fun φ hφ => (norm_extendL1_apply_le _).trans (h φ hφ)⟩

/-- **The mass measure of the extension** of `T` to compactly supported continuous tests is the
mass measure `‖T‖`. -/
@[simp]
theorem massMeasure_extendContinuous : massMeasure (extendContinuous T) = massMeasure T := by
  refine le_antisymm (massMeasure_le_of_enorm_apply_le _ enorm_extendContinuous_apply_le) ?_
  by_cases hT : HasLocallyFiniteMass T
  · refine massMeasure_le_of_enorm_apply_le _ fun φ => ?_
    have h := enorm_apply_le_lintegral_massMeasure (hasLocallyFiniteMass_extendContinuous (T := T))
      (monoCLM ℝ φ : 𝓓^{0}(Ω, F))
    rwa [extendContinuous_monoCLM hT, coe_monoCLM_of_le zero_le le_rfl] at h
  · rw [massMeasure_of_not_hasLocallyFiniteMass hT]
    exact Measure.zero_le _

/-- **The local mass of the extension.** For `T` of locally finite mass and `U` open, the local
mass of the extension on `U`, a supremum over continuous tests, is the local mass of `T` on `U`, a
supremum over tests of class `C^n`. -/
theorem localMass_extendContinuous (hT : HasLocallyFiniteMass T) {U : Set E} (hU : IsOpen U) :
    localMass (extendContinuous T) U = localMass T U := by
  rw [← massMeasure_preimage_coe hasLocallyFiniteMass_extendContinuous hU,
    massMeasure_extendContinuous, massMeasure_preimage_coe hT hU]

/-- If `T` does not have locally finite mass, its extension to compactly supported continuous tests
is `0`. -/
@[simp]
theorem extendContinuous_of_not_hasLocallyFiniteMass (hT : ¬HasLocallyFiniteMass T) :
    extendContinuous T = 0 := by
  ext φ
  have h := enorm_extendContinuous_apply_le (T := T) φ
  simpa [massMeasure_of_not_hasLocallyFiniteMass hT] using h

/-- A test `φ` of class `C^n` is approximated by smooth tests in a compact set of finite local
mass: there is a compact `K ⊆ Ω` with `localMass T K` finite and compact, measurable preimage in
`Ω`, and for every `ε > 0` a smooth test `ψ` such that `φ - ψ` is supported in `K` and bounded by
`ε`, so that `‖T (φ - ψ)‖ₑ ≤ localMass T K * ε`. -/
theorem exists_isCompact_localMass_ne_top_approx [FiniteDimensional ℝ E]
    (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    ∃ K : Set E, localMass T K ≠ ⊤ ∧ IsCompact ((↑) ⁻¹' K : Set Ω) ∧
      MeasurableSet ((↑) ⁻¹' K : Set Ω) ∧ ∀ ε : ℝ, 0 < ε → ∃ ψ : 𝓓(Ω, F),
        tsupport (⇑φ - ⇑ψ) ⊆ K ∧ (∀ x, ‖φ x - ψ x‖ ≤ ε) ∧
          ‖T (φ - monoCLM ℝ ψ)‖ₑ ≤ localMass T K * ENNReal.ofReal ε := by
  obtain ⟨K, hK, hKΩ, hφK, happrox⟩ := exists_isCompact_forall_exists_dist_le φ
  have hKc := Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKΩ)
  refine ⟨K, (hasLocallyFiniteMass_iff_localMass_ne_top T).1 hT K hK hKΩ, hKc, hKc.measurableSet,
    fun ε hε => ?_⟩
  obtain ⟨ψ, hψK, hψφ⟩ := happrox ε hε
  have hsub : tsupport (⇑φ - ⇑ψ) ⊆ K := (tsupport_sub _ _).trans (union_subset hφK hψK)
  have hε' (x : E) : ‖φ x - ψ x‖ ≤ ε := by
    rw [← dist_eq_norm_sub']
    exact hψφ x
  refine ⟨ψ, hsub, hε', enorm_apply_le_localMass_mul_of_forall_enorm_le T
    (by simpa [coe_monoCLM_of_le le_top le_rfl] using hsub) fun x => ?_⟩
  rw [← ofReal_norm]
  simpa [coe_monoCLM_of_le le_top le_rfl] using ENNReal.ofReal_le_ofReal (hε' x)

/-- **Smooth tests determine a map of locally finite mass.** A real-linear map on tests of class
`C^n` with locally finite mass that vanishes on smooth tests vanishes: smooth tests approximate a
test uniformly, with supports in a fixed compact set of finite local mass. -/
theorem apply_eq_zero_of_forall_monoCLM_eq_zero [FiniteDimensional ℝ E]
    (hT : HasLocallyFiniteMass T) (h : ∀ ψ : 𝓓(Ω, F), T (monoCLM ℝ ψ) = 0)
    (φ : 𝓓^{n}(Ω, F)) : T φ = 0 := by
  obtain ⟨K, hKT, -, -, happrox⟩ := exists_isCompact_localMass_ne_top_approx hT φ
  refine eNorm_eq_zero.1 (nonpos_iff_eq_zero.1
    (ENNReal.le_of_forall_pos_le_add_ofReal_mul hKT fun ε hε => ?_))
  obtain ⟨ψ, -, -, hψ⟩ := happrox ε hε
  rw [map_sub, h ψ, sub_zero, mul_comm] at hψ
  rwa [zero_add]

/-- **Uniqueness of the extension.** A real-linear map on compactly supported continuous tests
with locally finite mass that agrees with `T` on the tests of class `C^n` is the extension
`Distribution.extendContinuous T`. -/
theorem extendContinuous_unique [FiniteDimensional ℝ E] {L : 𝓓^{0}(Ω, F) →ₗ[ℝ] ℝ}
    (hL : HasLocallyFiniteMass L) (h : ∀ φ : 𝓓^{n}(Ω, F), L (monoCLM ℝ φ) = T φ) :
    L = (extendContinuous T : 𝓓^{0}(Ω, F) →ₗ[ℝ] ℝ) := by
  have hT : HasLocallyFiniteMass T := by
    convert hL.comp_monoCLM (Ω' := Ω) (m := n) using 1
    exact funext fun φ => (h φ).symm
  have hsub : HasLocallyFiniteMass (L - (extendContinuous T : 𝓓^{0}(Ω, F) →ₗ[ℝ] ℝ)) :=
    hL.sub hasLocallyFiniteMass_extendContinuous
  refine LinearMap.ext fun φ => sub_eq_zero.1 ?_
  refine apply_eq_zero_of_forall_monoCLM_eq_zero hsub (fun ψ => ?_) φ
  have hψ : (monoCLM ℝ ψ : 𝓓^{0}(Ω, F)) = monoCLM ℝ (monoCLM ℝ ψ : 𝓓^{n}(Ω, F)) :=
    TestFunction.ext fun x => by
      simp [coe_monoCLM_of_le le_top le_rfl, coe_monoCLM_of_le zero_le le_rfl]
  rw [LinearMap.sub_apply, hψ, h, ContinuousLinearMap.coe_coe, extendContinuous_monoCLM hT,
    sub_self]

end Continuous

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

/-- **Recognizing a Borel restriction.** If `T = R + R'` for maps `R`, `R'` of locally finite mass
whose mass measures are `‖T‖ ⌞ A` and `‖T‖ ⌞ Aᶜ`, then `T ⌞ A = R`. -/
theorem massRestrict_eq_of_massMeasure_eq {T R R' : 𝓓^{n}(Ω, F) →L[ℝ] ℝ}
    (hR : HasLocallyFiniteMass R) (hR' : HasLocallyFiniteMass R')
    (hsum : T = R + R') (hA : MeasurableSet A)
    (hRm : massMeasure R = (massMeasure T).restrict A)
    (hR'm : massMeasure R' = (massMeasure T).restrict Aᶜ) :
    massRestrict T hA = R := by
  -- The difference `T ⌞ A - R = R' - T ⌞ Aᶜ` has mass measure dominated both by `2 ‖T‖ ⌞ A` and
  -- by `2 ‖T‖ ⌞ Aᶜ`, hence zero.
  have hT : HasLocallyFiniteMass T := by rw [hsum, FunLike.coe_add]; exact hR.add hR'
  have hD : massRestrict T hA - R = R' - massRestrict T hA.compl := by
    ext φ
    have h := massRestrict_add_massRestrict_compl_apply hT hA φ
    have h' : T φ = R φ + R' φ := by rw [hsum, add_apply]
    simp only [sub_apply]
    linarith
  have h₁ := massMeasure_sub_le (hasLocallyFiniteMass_massRestrict (T := T) hA) hR
  rw [massMeasure_massRestrict hT hA, hRm] at h₁
  have h₂ := massMeasure_sub_le hR' (hasLocallyFiniteMass_massRestrict (T := T) hA.compl)
  rw [massMeasure_massRestrict hT hA.compl, hR'm, ← hD] at h₂
  have h0 : massMeasure (massRestrict T hA - R) = 0 := by
    refine Measure.measure_univ_eq_zero.1 (le_antisymm ?_ bot_le)
    calc massMeasure (massRestrict T hA - R) univ
        ≤ massMeasure (massRestrict T hA - R) A + massMeasure (massRestrict T hA - R) Aᶜ := by
          rw [← measure_union disjoint_compl_right hA.compl, union_compl_self]
      _ ≤ 0 + 0 := add_le_add ((h₂ _).trans (by simp [Measure.restrict_apply hA]))
          ((h₁ _).trans (by simp [Measure.restrict_apply hA.compl]))
      _ = 0 := add_zero 0
  ext φ
  have h := enorm_apply_le_lintegral_massMeasure (T := massRestrict T hA - R)
    (by rw [FunLike.coe_sub]; exact (hasLocallyFiniteMass_massRestrict hA).sub hR) φ
  rw [h0, lintegral_zero_measure, nonpos_iff_eq_zero, eNorm_eq_zero,
    sub_apply, sub_eq_zero] at h
  exact h

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

open scoped symmDiff in
/-- **Borel restrictions converge with their restricting sets.** If at `‖T‖`-almost every point
`x`, eventually along `l` the point `x` lies in `Aᵢ` exactly when it lies in `B`, then
`(T ⌞ Aᵢ) φ → (T ⌞ B) φ` for every test `φ`. -/
theorem tendsto_massRestrict_apply {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i)) (hB : MeasurableSet B)
    (hlim : ∀ᵐ x ∂massMeasure T, ∀ᶠ i in l, (x ∈ A i ↔ x ∈ B)) (φ : 𝓓^{n}(Ω, F)) :
    Tendsto (fun i => massRestrict T (hA i) φ) l (𝓝 (massRestrict T hB φ)) := by
  simp_rw [massRestrict_apply]
  refine ((extendL1 T).continuous.tendsto _).comp ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- The `L¹` distance is the integral of `‖φ‖` over the symmetric difference `Aᵢ ∆ B`.
  have hpt (i : ι) (x : Ω) :
      ‖(A i).indicator (fun y : Ω => φ y) x - B.indicator (fun y => φ y) x‖ₑ =
        (A i ∆ B).indicator (fun y => ‖φ y‖ₑ) x := by
    by_cases hx : x ∈ A i <;> by_cases hx' : x ∈ B <;> simp [hx, hx', mem_symmDiff]
  have hnorm (i : ι) :
      ‖TestFunction.indicatorToLp 1 (massMeasure T) (hA i) φ -
          TestFunction.indicatorToLp 1 (massMeasure T) hB φ‖ =
        (∫⁻ x, (A i ∆ B).indicator (fun y => ‖φ y‖ₑ) x ∂massMeasure T).toReal := by
    rw [TestFunction.indicatorToLp_apply, TestFunction.indicatorToLp_apply, ← MemLp.toLp_sub,
      Lp.norm_toLp, eLpNorm_one_eq_lintegral_eNorm]
    · exact congrArg ENNReal.toReal (lintegral_congr (hpt i))
    · exact (((TestFunction.memLp_subtype (p := 1) φ).indicator (hA i).nullMeasurableSet).sub
        ((TestFunction.memLp_subtype φ).indicator hB.nullMeasurableSet)).aestronglyMeasurable
  simp_rw [hnorm]
  rw [← ENNReal.toReal_zero]
  refine (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ?_
  rw [← lintegral_zero (μ := massMeasure T)]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun x => ‖φ x‖ₑ)
    (.of_forall fun i => ?_) (.of_forall fun i => ae_of_all _ fun x => ?_) ?_ ?_
  · exact (continuous_eNorm.comp (φ.continuous.comp continuous_subtypeVal)).measurable.indicator
      ((hA i).symmDiff hB)
  · exact indicator_le_self _ _ x
  · rw [← TestFunction.enorm_toLp_one]
    exact eNorm_ne_top
  · filter_upwards [hlim] with x hx
    refine tendsto_const_nhds.congr' (hx.mono fun i hi => ?_)
    simp [mem_symmDiff, hi]

end Distribution
