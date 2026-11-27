/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import TauCeti.Analysis.Distribution.Mass.Extension
public import TauCeti.Analysis.Distribution.Mass.Measure
import TauCeti.Analysis.Distribution.AELeOfIntegral
import TauCeti.Analysis.Distribution.Mass.Polar.Density
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.MeasureTheory.Integral.DualPairing
import TauCeti.MeasureTheory.Integral.Lebesgue.Support
import TauCeti.Topology.Instances.ENNReal

/-!
# Riesz representation for vector fields

Let `Ω` be an open set of a finite-dimensional real normed space `E`, let `F` be a
finite-dimensional real inner product space, and let `T : 𝓓^{n}(Ω, F) → ℝ` be a real-linear map
on the `F`-valued test functions of class `C^n` (`n = 0` gives the compactly supported continuous
vector fields) with locally finite mass (`Distribution.HasLocallyFiniteMass`): for each compact
`K ⊆ Ω`, `sup {T φ : ‖φ‖ ≤ 1, spt φ ⊆ K} < ∞`. Then there are a Radon measure `‖T‖` on `Ω`, the
mass measure `Distribution.massMeasure T`, and a strongly measurable field `η : Ω → F` with
`‖η‖ = 1` at `‖T‖`-almost every point, such that

`T φ = ∫ ⟪η x, φ x⟫ d‖T‖(x)` for every test `φ`,

and `‖T‖ (Ω ∩ U) = sup {T φ : ‖φ‖ ≤ 1, spt φ ⊆ U}` for every open `U`
(`Distribution.massMeasure_preimage_coe`, `Distribution.localMass_eq_iSup_ofReal_apply`). The
measure `‖T‖` is the only Radon measure with such a representation, and `η` is unique
`‖T‖`-almost everywhere. The field `η = Distribution.polarVector T` is the **polar vector field**
of `T`. On a Euclidean space `E`, with `F = E`, `T` is a linear functional on the compactly
supported `C^n` vector fields on `Ω`, and this is the Riesz representation theorem for such
functionals; the case `n = 0` is the version for compactly supported continuous vector fields.

For smooth tests the representation is `Distribution.polarDensity`, with values in the dual of
`F`. The restriction of `T` to smooth tests is continuous, and smooth tests approximate a test of
class `C^n` uniformly with supports in a fixed compact set
(`TestFunction.exists_isCompact_forall_exists_dist_le`), so the restriction has the same mass
measure and the same representation. The Riesz isomorphism `InnerProductSpace.toDual` turns the
dual-valued density into a vector field. For uniqueness of the measure, a Radon measure `μ` with a
representation `T φ = ∫ ⟪η' x, φ x⟫ dμ`, by a `μ`-almost everywhere strongly measurable field `η'`
with `‖η'‖ = 1` at `μ`-almost every point, gives through `InnerProductSpace.toDual` a
representation of the restriction of `T` to smooth tests by a density of dual norm one, so `μ` is
the mass measure of that restriction (`Distribution.massMeasure_eq_of_apply_eq_integral`), which
is the mass measure of `T`. Measurability of `η'` is needed: the integral of a
pairing that is not almost everywhere strongly measurable is `0` by convention.

## Main declarations

* `Distribution.polarVector T`: the polar vector field `η : Ω → F` of `T`.
* `Distribution.apply_eq_integral_inner_polarVector`: the representation
  `T φ = ∫ ⟪η x, φ x⟫ d‖T‖`.
* `Distribution.ae_norm_polarVector_eq_one`: `‖η‖ = 1` at `‖T‖`-almost every point.
* `Distribution.locallyIntegrable_polarVector`: `η` is locally integrable for `‖T‖`.
* `Distribution.ae_eq_polarVector`: a locally integrable field representing `T` against `‖T‖`
  is `η` almost everywhere.
* `Distribution.hasLocallyFiniteMass_of_apply_eq_integral_inner`: a map represented against a
  measure finite on compact sets by a field of norm one almost everywhere has locally finite mass.
* `Distribution.massMeasure_eq_of_apply_eq_integral_inner`: a Radon measure `μ` against which
  `T` is represented by an almost everywhere strongly measurable field of norm one
  `μ`-almost everywhere is the mass measure of `T`.
* `Distribution.extendContinuous_apply_eq_integral_inner`: the extension
  `Distribution.extendContinuous T` of `T` to compactly supported continuous tests is
  `φ ↦ ∫ ⟪η x, φ x⟫ d‖T‖`.

## References

* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 1, §4 (Theorem 4.1, the Riesz
  representation theorem for functionals on vector-valued functions).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §1.8.
* H. Federer, *Geometric Measure Theory*, §2.5.
-/

public section

noncomputable section

namespace Distribution

open MeasureTheory TopologicalSpace TestFunction Set Filter Metric
open scoped ENNReal Distributions RealInnerProductSpace Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {Ω : Opens E} {n : ℕ∞}
  {𝓕 : Type*} [FunLike 𝓕 𝓓^{n}(Ω, F) ℝ] [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, F) ℝ] {T : 𝓕}

section Smooth

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] in
/-- The restriction of `T` to smooth tests, a continuous linear map when `T` has locally finite
mass. -/
private def smoothRestrict (T : 𝓕) (hT : HasLocallyFiniteMass T) : 𝓓(Ω, F) →L[ℝ] ℝ :=
  ⟨(LinearMap.ofClass T).comp (monoCLM ℝ : 𝓓(Ω, F) →L[ℝ] 𝓓^{n}(Ω, F)).toLinearMap,
    HasLocallyFiniteMass.continuous (L := (LinearMap.ofClass T).comp
      (monoCLM ℝ : 𝓓(Ω, F) →L[ℝ] 𝓓^{n}(Ω, F)).toLinearMap) hT.comp_monoCLM⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] in
private theorem smoothRestrict_apply (hT : HasLocallyFiniteMass T) (ψ : 𝓓(Ω, F)) :
    smoothRestrict T hT ψ = T (monoCLM ℝ ψ) :=
  rfl

/-- The restriction of `T` to smooth tests has the same mass measure as `T`. -/
private theorem massMeasure_smoothRestrict (hT : HasLocallyFiniteMass T) :
    massMeasure (smoothRestrict T hT) = massMeasure T := by
  have := Ω.isOpen.locallyCompactSpace
  set T' := smoothRestrict T hT
  refine le_antisymm (massMeasure_le_of_enorm_apply_le _ fun ψ => ?_)
    (massMeasure_le_of_enorm_apply_le _ fun φ => ?_)
  · simpa [T', smoothRestrict_apply, coe_monoCLM_of_le le_top le_rfl] using
      enorm_apply_le_lintegral_massMeasure hT (monoCLM ℝ ψ)
  -- Approximate `φ` by smooth tests `ψ` supported in a compact `K`.
  obtain ⟨K, hKT, hKc, hKm, happrox⟩ := exists_isCompact_localMass_ne_top_approx hT φ
  have hKT' : massMeasure T' ((↑) ⁻¹' K) ≠ ⊤ := hKc.measure_lt_top.ne
  refine ENNReal.le_of_forall_pos_le_add_ofReal_mul (ENNReal.add_ne_top.2 ⟨hKT', hKT⟩)
    fun ε hε => ?_
  obtain ⟨ψ, hsub', hψφ, hTψ⟩ := happrox ε hε
  have hφm : Measurable fun x : Ω => ‖φ x‖ₑ :=
    (φ.continuous.comp continuous_subtypeVal).eNorm.measurable
  calc ‖T φ‖ₑ = ‖T' ψ + T (φ - monoCLM ℝ ψ)‖ₑ := by simp [T', smoothRestrict_apply]
    _ ≤ ‖T' ψ‖ₑ + ‖T (φ - monoCLM ℝ ψ)‖ₑ := eNorm_add_le _ _
    _ ≤ ∫⁻ x, ‖φ x‖ₑ + ‖ψ x - φ x‖ₑ ∂massMeasure T' + localMass T K * ENNReal.ofReal ε := by
        refine add_le_add ((enorm_apply_le_lintegral_massMeasure hT.comp_monoCLM ψ).trans
          (lintegral_mono fun x => ?_)) hTψ
        simpa using eNorm_add_le (φ x) (ψ x - φ x)
    _ ≤ ∫⁻ x, ‖φ x‖ₑ ∂massMeasure T' + ENNReal.ofReal ε * massMeasure T' ((↑) ⁻¹' K) +
          localMass T K * ENNReal.ofReal ε := by
        rw [lintegral_add_left hφm]
        gcongr
        refine lintegral_enorm_le_ofReal_mul_measure _ (f := fun x : Ω => ψ x - φ x) hKm
          (fun x hx => hsub' (subset_tsupport _ ?_)) fun x => ?_
        · rw [Function.mem_support] at hx ⊢
          rw [Pi.sub_apply, ← neg_sub, neg_ne_zero]
          exact hx
        · rw [norm_sub_rev]
          exact hψφ x
    _ = _ := by ring

/-- The polar density of the restriction of `T` to smooth tests represents `T` on all tests. -/
private theorem apply_eq_integral_polarDensity_smoothRestrict (hT : HasLocallyFiniteMass T)
    (φ : 𝓓^{n}(Ω, F)) :
    T φ = ∫ x, polarDensity (smoothRestrict T hT) x (φ x) ∂massMeasure T := by
  have := Ω.isOpen.locallyCompactSpace
  set τ := polarDensity (smoothRestrict T hT)
  have hT' : HasLocallyFiniteMass (smoothRestrict T hT) := hT.comp_monoCLM
  have hτ1 := ae_norm_polarDensity_eq_one hT'
  have hτi := locallyIntegrable_polarDensity hT'
  rw [massMeasure_smoothRestrict hT] at hτ1 hτi
  have hint (f : 𝓓^{n}(Ω, F)) : Integrable (fun x : Ω => τ x (f x)) (massMeasure T) :=
    f.integrable_bilin_subtype (ContinuousLinearMap.apply ℝ ℝ) hτi
  have hrep (ψ : 𝓓(Ω, F)) : T (monoCLM ℝ ψ) = ∫ x, τ x (ψ x) ∂massMeasure T := by
    rw [← smoothRestrict_apply hT, apply_eq_integral_polarDensity hT',
      massMeasure_smoothRestrict hT]
  obtain ⟨K, hKT, hKc, hKm, happrox⟩ := exists_isCompact_localMass_ne_top_approx hT φ
  have hKμ : massMeasure T ((↑) ⁻¹' K) ≠ ⊤ := hKc.measure_lt_top.ne
  rw [← sub_eq_zero, ← eNorm_eq_zero, ← nonpos_iff_eq_zero]
  refine ENNReal.le_of_forall_pos_le_add_ofReal_mul (ENNReal.add_ne_top.2 ⟨hKT, hKμ⟩)
    fun ε hε => ?_
  obtain ⟨ψ, hsub, hψφ, hTfε⟩ := happrox ε hε
  set f : 𝓓^{n}(Ω, F) := φ - monoCLM ℝ ψ
  have hf (x : E) : f x = φ x - ψ x := by simp [f]
  have hfK : tsupport f ⊆ K := by simpa [f, coe_monoCLM_of_le le_top le_rfl] using hsub
  have hfε (x : E) : ‖f x‖ ≤ ε := by
    rw [hf]
    exact hψφ x
  have hTf : T f = T φ - ∫ x, τ x (ψ x) ∂massMeasure T := by rw [map_sub, hrep]
  have hIf : ∫ x, τ x (f x) ∂massMeasure T =
      ∫ x, τ x (φ x) ∂massMeasure T - ∫ x, τ x (ψ x) ∂massMeasure T := by
    have hψi : Integrable (fun x : Ω => τ x (ψ x)) (massMeasure T) :=
      ψ.integrable_bilin_subtype (ContinuousLinearMap.apply ℝ ℝ) hτi
    rw [← integral_sub (hint φ) hψi]
    simp [hf, map_sub]
  have hdiff : T φ - ∫ x, τ x (φ x) ∂massMeasure T =
      T f - ∫ x, τ x (f x) ∂massMeasure T := by
    rw [hTf, hIf]
    ring
  rw [hdiff, zero_add]
  calc ‖T f - ∫ x, τ x (f x) ∂massMeasure T‖ₑ
      ≤ ‖T f‖ₑ + ‖∫ x, τ x (f x) ∂massMeasure T‖ₑ := eNorm_sub_le
    _ ≤ localMass T K * ENNReal.ofReal ε + ENNReal.ofReal ε * massMeasure T ((↑) ⁻¹' K) := by
        refine add_le_add hTfε <| (eNorm_integral_le_lintegral_eNorm _).trans <|
          (lintegral_mono_ae ?_).trans (lintegral_enorm_le_ofReal_mul_measure _
            (f := fun x : Ω => f x) hKm (fun x hx => hfK (subset_tsupport _ hx)) fun x => hfε x)
        filter_upwards [hτ1] with x hx
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (((τ x).le_opNorm _).trans (by rw [hx, one_mul]))
    _ = _ := by ring

private theorem exists_polarVector (hT : HasLocallyFiniteMass T) :
    ∃ η : Ω → F, StronglyMeasurable η ∧ (∀ᵐ x ∂massMeasure T, ‖η x‖ = 1) ∧
      ∀ φ : 𝓓^{n}(Ω, F), T φ = ∫ x, ⟪η x, φ x⟫ ∂massMeasure T := by
  have hT' : HasLocallyFiniteMass (smoothRestrict T hT) := hT.comp_monoCLM
  have hτ1 := ae_norm_polarDensity_eq_one hT'
  rw [massMeasure_smoothRestrict hT] at hτ1
  refine ⟨fun x => (InnerProductSpace.toDual ℝ F).symm (polarDensity (smoothRestrict T hT) x),
    (InnerProductSpace.toDual ℝ F).symm.continuous.comp_stronglyMeasurable
      measurable_polarDensity.stronglyMeasurable,
    ?_, fun φ => ?_⟩
  · filter_upwards [hτ1] with x hx
    rwa [LinearIsometryEquiv.norm_map]
  · simp_rw [InnerProductSpace.toDual_symm_apply]
    exact apply_eq_integral_polarDensity_smoothRestrict hT φ

end Smooth

open scoped Classical in
/-- The **polar vector field** `η` of a real-linear map `T` on `F`-valued test functions of class
`C^n` on `Ω`, with respect to its mass measure `‖T‖`: if `T` has locally finite mass, it is a
strongly measurable vector field `η : Ω → F` of norm one at `‖T‖`-almost every point
(`Distribution.ae_norm_polarVector_eq_one`) such that `T φ = ∫ ⟪η x, φ x⟫ d‖T‖` for every test
`φ` (`Distribution.apply_eq_integral_inner_polarVector`). It is determined `‖T‖`-almost
everywhere (`Distribution.ae_eq_polarVector`). If no such field exists it is `0` by convention. -/
def polarVector (T : 𝓕) : Ω → F :=
  if h : ∃ η : Ω → F, StronglyMeasurable η ∧ (∀ᵐ x ∂massMeasure T, ‖η x‖ = 1) ∧
      ∀ φ : 𝓓^{n}(Ω, F), T φ = ∫ x, ⟪η x, φ x⟫ ∂massMeasure T then h.choose
  else 0

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The polar vector field is strongly measurable. -/
@[fun_prop]
theorem stronglyMeasurable_polarVector : StronglyMeasurable (polarVector T) := by
  unfold polarVector
  split_ifs with h
  exacts [h.choose_spec.1, stronglyMeasurable_const]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The polar vector field of a map without locally finite mass is `0`, by convention. -/
@[simp]
theorem polarVector_of_not_hasLocallyFiniteMass (hT : ¬HasLocallyFiniteMass T) :
    polarVector T = 0 := by
  unfold polarVector
  split_ifs with h
  · obtain ⟨η, -, -, h⟩ := h
    have hT0 : ⇑T = 0 := funext fun φ => by
      simp [h φ, massMeasure_of_not_hasLocallyFiniteMass hT]
    have h0 : HasLocallyFiniteMass ⇑T := by
      rw [hT0]
      exact hasLocallyFiniteMass_zero
    exact absurd h0 hT
  · rfl

private theorem polarVector_spec (hT : HasLocallyFiniteMass T) :
    (∀ᵐ x ∂massMeasure T, ‖polarVector T x‖ = 1) ∧
      ∀ φ : 𝓓^{n}(Ω, F), T φ = ∫ x, ⟪polarVector T x, φ x⟫ ∂massMeasure T := by
  rw [polarVector, dite_eq_left (exists_polarVector hT)]
  exact (exists_polarVector hT).choose_spec.2

/-- **Riesz representation for vector fields.** A real-linear map `T` on vector-valued test
functions with locally finite mass is integration of `⟪η x, φ x⟫` against its mass measure, where
`η` is its polar vector field. -/
theorem apply_eq_integral_inner_polarVector (hT : HasLocallyFiniteMass T) (φ : 𝓓^{n}(Ω, F)) :
    T φ = ∫ x, ⟪polarVector T x, φ x⟫ ∂massMeasure T :=
  (polarVector_spec hT).2 φ

/-- The polar vector field has norm one at `‖T‖`-almost every point. Without locally finite
mass, `‖T‖` is the zero measure. -/
theorem ae_norm_polarVector_eq_one : ∀ᵐ x ∂massMeasure T, ‖polarVector T x‖ = 1 := by
  by_cases hT : HasLocallyFiniteMass T
  · exact (polarVector_spec hT).1
  · simp [massMeasure_of_not_hasLocallyFiniteMass hT]

/-- The polar vector field is locally integrable with respect to the mass measure. -/
theorem locallyIntegrable_polarVector :
    LocallyIntegrable (polarVector T) (massMeasure T) := by
  have := Ω.isOpen.locallyCompactSpace
  exact (memLp_top_of_bound stronglyMeasurable_polarVector.aestronglyMeasurable 1
    (ae_norm_polarVector_eq_one.mono fun _ hx => hx.le)).locallyIntegrable le_top

/-- **Uniqueness of the polar vector field.** A locally integrable vector field `η` with
`T φ = ∫ ⟪η x, φ x⟫ d‖T‖` for every test `φ` agrees with the polar vector field of `T` at
`‖T‖`-almost every point. -/
theorem ae_eq_polarVector {η : Ω → F} (hη : LocallyIntegrable η (massMeasure T))
    (h : ∀ φ : 𝓓^{n}(Ω, F), T φ = ∫ x, ⟪η x, φ x⟫ ∂massMeasure T) :
    η =ᵐ[massMeasure T] polarVector T := by
  by_cases hT : HasLocallyFiniteMass T
  swap
  · simp [massMeasure_of_not_hasLocallyFiniteMass hT, EventuallyEq]
  have hpv := locallyIntegrable_polarVector (T := T)
  filter_upwards [TauCeti.ae_eq_zero_of_forall_integral_inner_eq_zero (hη.sub hpv) fun φ => by
    simp only [Pi.sub_apply, inner_sub_right]
    rw [integral_sub (integrable_inner_subtype φ hη) (integrable_inner_subtype φ hpv)]
    have h₁ := h (monoCLM ℝ φ)
    have h₂ := apply_eq_integral_inner_polarVector hT (monoCLM ℝ φ)
    simp only [coe_monoCLM_of_le le_top le_rfl, real_inner_comm (φ _)] at h₁ h₂ ⊢
    rw [← h₁, ← h₂, sub_self]] with x hx
  simpa [sub_eq_zero] using hx

section Uniqueness

variable {μ : Measure Ω} {η : Ω → F}

omit [FiniteDimensional ℝ E] in
/-- A map represented against a measure `μ` finite on compact sets by a field of norm one at
`μ`-almost every point has locally finite mass. -/
theorem hasLocallyFiniteMass_of_apply_eq_integral_inner [IsFiniteMeasureOnCompacts μ]
    (hη1 : ∀ᵐ x ∂μ, ‖η x‖ = 1) (h : ∀ φ : 𝓓^{n}(Ω, F), T φ = ∫ x, ⟪η x, φ x⟫ ∂μ) :
    HasLocallyFiniteMass T := by
  refine (hasLocallyFiniteMass_iff_localMass_ne_top T).2 fun K hK hKΩ => ?_
  have hKc := Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKΩ)
  refine ne_top_of_le_ne_top (hKc.measure_lt_top (μ := μ)).ne
    (localMass_le_iff.2 fun φ hφK hφ => ?_)
  simpa [h φ] using TauCeti.enorm_integral_apply_le_measure
    (τ := fun x => InnerProductSpace.toDual ℝ F (η x)) (hη1.mono fun x hx => by simp [hx])
    hKc.measurableSet (f := fun x : Ω => φ x) (fun x hx => hφK (subset_tsupport _ hx)) fun x => hφ x

/-- **Uniqueness of the mass measure.** If a real-linear map `T` on vector-valued test functions
is represented as `T φ = ∫ ⟪η x, φ x⟫ dμ` by a measure `μ` finite on compact subsets of `Ω` and a
`μ`-almost everywhere strongly measurable field `η` of norm one at `μ`-almost every point, then `μ`
is the mass measure of `T`. In particular `T` has locally finite mass, and `η` is its polar vector
field `μ`-almost everywhere (`Distribution.ae_eq_polarVector`). -/
theorem massMeasure_eq_of_apply_eq_integral_inner [IsFiniteMeasureOnCompacts μ]
    (hηm : AEStronglyMeasurable η μ) (hη1 : ∀ᵐ x ∂μ, ‖η x‖ = 1)
    (h : ∀ φ : 𝓓^{n}(Ω, F), T φ = ∫ x, ⟪η x, φ x⟫ ∂μ) : massMeasure T = μ := by
  have hT := hasLocallyFiniteMass_of_apply_eq_integral_inner hη1 h
  rw [← massMeasure_smoothRestrict hT]
  refine massMeasure_eq_of_apply_eq_integral
    ((InnerProductSpace.toDual ℝ F).continuous.comp_aestronglyMeasurable hηm)
    (hη1.mono fun x hx => by simpa using hx) fun ψ => ?_
  simp [smoothRestrict_apply, h, coe_monoCLM_of_le le_top le_rfl]

end Uniqueness

/-! ### Extension to compactly supported continuous tests -/

section Continuous

/-- **The extension is integration against the polar vector field.** For every compactly
supported continuous test `φ`, `extendContinuous T φ = ∫ ⟪η x, φ x⟫ d‖T‖`, where `η` is the polar
vector field of `T`. -/
theorem extendContinuous_apply_eq_integral_inner (φ : 𝓓^{0}(Ω, F)) :
    extendContinuous T φ = ∫ x, ⟪polarVector T x, φ x⟫ ∂massMeasure T := by
  by_cases hT : HasLocallyFiniteMass T
  swap
  · simp [hT]
  have hS := hasLocallyFiniteMass_extendContinuous (T := T)
  have hμ := massMeasure_extendContinuous (T := T)
  have hη : polarVector (extendContinuous T) =ᵐ[massMeasure T] polarVector T := by
    refine ae_eq_polarVector (hμ ▸ locallyIntegrable_polarVector) fun ψ => ?_
    rw [← extendContinuous_monoCLM hT, apply_eq_integral_inner_polarVector hS, hμ,
      coe_monoCLM_of_le zero_le le_rfl]
  rw [apply_eq_integral_inner_polarVector hS, hμ]
  refine integral_congr_ae ?_
  filter_upwards [hη] with x hx
  rw [hx]

end Continuous

end Distribution
