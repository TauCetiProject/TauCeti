/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.Distribution.Mass.Polar.Density
import TauCeti.Analysis.Distribution.Mass.Polar.Vector
import TauCeti.Analysis.Distribution.TestFunction.Approximation
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.MeasureTheory.Integral.DualPairing
import TauCeti.Topology.ContinuousMap.CompactlySupported
import TauCeti.Topology.Sets.Opens

/-!
# The Riesz representation theorem for vector fields

Let `Ω` be an open set of a finite-dimensional real normed space `E` and `F` a finite-dimensional
real normed space. A linear functional `L` on the compactly supported continuous vector fields
`C_c(Ω, F)` that is bounded on each compact set,

`sup { L f | ‖f x‖ ≤ 1 for all x, tsupport f ⊆ K } < ∞` for every compact `K ⊆ Ω`,

is integration against a Radon measure with a density of dual norm one:
there are a regular measure `‖L‖` on `Ω` and a measurable field `τ : Ω → StrongDual ℝ F` with
`‖τ x‖ = 1` for `‖L‖`-almost every `x`, such that

`L f = ∫ τ(x) (f x) d‖L‖(x)` for every `f ∈ C_c(Ω, F)`,

and `‖L‖ (U) = sup { L f | ‖f x‖ ≤ 1 for all x, tsupport f ⊆ U }` for every open `U ⊆ Ω`
(`TauCeti.RealRMK.exists_apply_eq_integral_dual`). Conversely, a functional represented by a
measure finite on compact sets and a density of dual norm at most one satisfies the bound
(`TauCeti.RealRMK.exists_le_of_apply_eq_integral`). The measure and the density are unique: any two
representing pairs with measures finite on compact sets and densities of dual norm one almost
everywhere have the same measure
(`TauCeti.RealRMK.measure_eq_of_apply_eq_integral_dual`) and densities that agree almost everywhere
(`TauCeti.RealRMK.ae_eq_of_apply_eq_integral_dual`).
When `F` is an inner product space the density is a unit vector field `η : Ω → F`, with
`L f = ∫ ⟪η x, f x⟫ d‖L‖(x)` (`TauCeti.RealRMK.exists_apply_eq_integral_inner`, with uniqueness
`TauCeti.RealRMK.measure_eq_of_apply_eq_integral_inner` and
`TauCeti.RealRMK.ae_eq_of_apply_eq_integral_inner`).

This is the form in which the first variation of a varifold of locally bounded first variation
becomes a vector-valued Radon measure, and in which its total variation `‖δV‖` is defined.

## The argument

The restriction of `L` to the test vector fields `𝓓(Ω, F)` has locally finite mass, so it has a
mass measure `‖L‖ = Distribution.massMeasure` and a polar density
`τ = Distribution.polarDensity` representing it on test fields. A compactly supported continuous
field is a uniform limit of test fields supported in a fixed compact subset of `Ω`
(`CompactlySupportedContinuousMap.exists_isCompact_forall_exists_testFunction_dist_le`), along
which both `L` and the integral against `τ` converge, so the representation extends to
`C_c(Ω, F)`. Every test field restricts to a continuous field, and the representation bounds
`L f` by `‖L‖ (U)` for `f` supported in `U` with `‖f‖ ≤ 1`, which gives the formula on open
sets.

For uniqueness, every representing pair `(μ, τ')` also represents the restriction of `L` to test
fields, so `μ` is its mass measure (`Distribution.massMeasure_eq_of_apply_eq_integral`) and `τ'`
is its polar density almost everywhere (`Distribution.ae_eq_polarDensity_of_apply_eq_integral`).
In the inner product form the restriction is taken to the test fields of class `C^0`, whose mass
measure and polar vector field are unique (`Distribution.massMeasure_eq_of_apply_eq_integral_inner`,
`Distribution.ae_eq_polarVector`).

## References

* L. Simon, *Lectures on Geometric Measure Theory*, Theorems 4.1 and 4.2 (the Riesz
  representation theorem for vector-valued functionals).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §1.8.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter Metric Set Distribution
open scoped ENNReal Distributions Topology CompactlySupported BoundedContinuousFunction
  RealInnerProductSpace

namespace TauCeti.RealRMK

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {L : C_c(Ω, F) →ₗ[ℝ] ℝ}

section Pairing

variable [MeasurableSpace E] [BorelSpace E]

/-- **The converse of the Riesz representation theorem for vector fields.** A representation of `L`
against a measure finite on compact sets, with a density of dual norm at most one, bounds `L` on
the fields of norm at most one supported in each compact set. -/
theorem exists_le_of_apply_eq_integral {μ : Measure Ω} [IsFiniteMeasureOnCompacts μ]
    {τ : Ω → StrongDual ℝ F} (hτ : ∀ᵐ x ∂μ, ‖τ x‖ ≤ 1)
    (h : ∀ f : C_c(Ω, F), L f = ∫ x, τ x (f x) ∂μ) (K : Set Ω) (hK : IsCompact K) :
    ∃ C : ℝ, ∀ f : C_c(Ω, F), tsupport f ⊆ K → (∀ x, ‖f x‖ ≤ 1) → L f ≤ C := by
  refine ⟨μ.real K, fun f hfK hf => ?_⟩
  rw [h f, ← one_mul (μ.real K)]
  exact (le_abs_self _).trans (abs_integral_apply_le_mul_measureReal hτ hK.measurableSet
    hK.measure_lt_top.ne ((subset_tsupport f).trans hfK) hf)

end Pairing

section Representation

variable [NormedSpace ℝ E]
  (hL : ∀ K : Set Ω, IsCompact K → ∃ C : ℝ, ∀ f : C_c(Ω, F), tsupport f ⊆ K →
    (∀ x, ‖f x‖ ≤ 1) → L f ≤ C)

/-- The restriction of `L` to test vector fields of class `C^n`. -/
private def restrictTest (n : ℕ∞) (L : C_c(Ω, F) →ₗ[ℝ] ℝ) : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ where
  toFun φ := L φ.toCompactlySupportedContinuousMap
  map_add' φ ψ := by simp
  map_smul' c φ := by simp

include hL

/-- The restriction of `L` to test vector fields has locally finite mass. -/
private lemma hasLocallyFiniteMass_restrictTest : HasLocallyFiniteMass (restrictTest ⊤ L) := by
  refine hasLocallyFiniteMass_def.2 fun K hK hKΩ => ?_
  obtain ⟨C, hC0, hC⟩ := CompactlySupportedContinuousMap.exists_abs_le_mul_of_forall_le (hL _
    (Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK (by simpa using hKΩ)))
  refine ⟨C, hC0, fun φ hφK => ?_⟩
  rw [Real.norm_eq_abs]
  exact hC _ ((TestFunction.tsupport_toCompactlySupportedContinuousMap_subset φ).trans
    (preimage_mono hφK)) _ (norm_nonneg _) fun x => by
      rw [TestFunction.toCompactlySupportedContinuousMap_apply]
      exact (φ : E →ᵇ F).norm_coe_le_norm x

/-- The restriction of `L` to test vector fields, a distribution of order zero. -/
private def testCLM : 𝓓(Ω, F) →L[ℝ] ℝ :=
  ⟨restrictTest ⊤ L, (hasLocallyFiniteMass_restrictTest hL).continuous⟩

private lemma testCLM_apply (φ : 𝓓(Ω, F)) :
    testCLM hL φ = L φ.toCompactlySupportedContinuousMap :=
  (rfl)

private lemma hasLocallyFiniteMass_testCLM : HasLocallyFiniteMass (testCLM hL) :=
  hasLocallyFiniteMass_restrictTest hL

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ E]

/-- The polar density of the restriction of `L` to test fields represents `L` on all of
`C_c(Ω, F)`. -/
private lemma apply_eq_integral_testCLM (f : C_c(Ω, F)) :
    L f = ∫ x, polarDensity (testCLM hL) x (f x) ∂massMeasure (testCLM hL) := by
  have hT := hasLocallyFiniteMass_testCLM hL
  have hτ : ∀ᵐ x ∂massMeasure (testCLM hL), ‖polarDensity (testCLM hL) x‖ ≤ 1 :=
    (ae_norm_polarDensity_eq_one hT).mono fun _ hx => hx.le
  have hτm := (measurable_polarDensity (T := testCLM hL)).aestronglyMeasurable
    (μ := massMeasure (testCLM hL))
  -- A compact `K ⊆ Ω` containing the supports of `f` and of test fields approximating it.
  obtain ⟨K, hK, hKΩ, hfK, happrox⟩ :=
    f.exists_isCompact_forall_exists_testFunction_dist_le
  have hK₁ : IsCompact (((↑) : Ω → E) ⁻¹' K) :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK (by simpa using hKΩ)
  obtain ⟨C, -, hC⟩ := CompactlySupportedContinuousMap.exists_abs_le_mul_of_forall_le (hL _ hK₁)
  set M := (massMeasure (testCLM hL)).real (((↑) : Ω → E) ⁻¹' K)
  -- Approximating `f` within `ε` by a test field supported in `K` gives an error `(C + M) ε`.
  have key (ε : ℝ) (hε : ε ∈ Ioi 0) :
      |L f - ∫ x, polarDensity (testCLM hL) x (f x) ∂massMeasure (testCLM hL)| ≤ (C + M) * ε := by
    obtain ⟨φ, hφK, hφ⟩ := happrox ε hε
    set g := f - φ.toCompactlySupportedContinuousMap
    have hgK : tsupport g ⊆ ((↑) : Ω → E) ⁻¹' K :=
      closure_minimal ((Function.support_sub _ _).trans (union_subset
        ((subset_tsupport _).trans (image_subset_iff.1 hfK)) ((subset_tsupport _).trans
          ((TestFunction.tsupport_toCompactlySupportedContinuousMap_subset φ).trans
            (preimage_mono hφK))))) hK₁.isClosed
    have hg (x : Ω) : ‖g x‖ ≤ ε := by
      simpa [g, dist_eq_norm, norm_sub_rev] using hφ x
    have hφ' : L φ.toCompactlySupportedContinuousMap = ∫ x, polarDensity (testCLM hL) x
        (φ.toCompactlySupportedContinuousMap x) ∂massMeasure (testCLM hL) := by
      rw [← testCLM_apply hL, apply_eq_integral_polarDensity hT φ]
      simp only [TestFunction.toCompactlySupportedContinuousMap_apply]
    have hint : ∫ x, polarDensity (testCLM hL) x (g x) ∂massMeasure (testCLM hL) =
        ∫ x, polarDensity (testCLM hL) x (f x) ∂massMeasure (testCLM hL) -
          ∫ x, polarDensity (testCLM hL) x (φ.toCompactlySupportedContinuousMap x)
            ∂massMeasure (testCLM hL) := by
      rw [← integral_sub (f.integrable_dual_apply hτm hτ)
        (φ.toCompactlySupportedContinuousMap.integrable_dual_apply hτm hτ)]
      simp [g]
    have hsplit : L f - ∫ x, polarDensity (testCLM hL) x (f x) ∂massMeasure (testCLM hL) =
        L g - ∫ x, polarDensity (testCLM hL) x (g x) ∂massMeasure (testCLM hL) := by
      rw [hint, map_sub, hφ']
      ring
    rw [hsplit, add_mul]
    refine (abs_sub _ _).trans (add_le_add (hC g hgK ε (le_of_lt hε) hg) ?_)
    rw [mul_comm]
    exact abs_integral_apply_le_mul_measureReal hτ hK₁.measurableSet hK₁.measure_lt_top.ne
      ((subset_tsupport g).trans hgK) hg
  have hlim : Tendsto (fun ε : ℝ => (C + M) * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_id'.2 (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))).const_mul (C + M)
  have h0 := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

/-- The mass measure of the restriction of `L` to test fields is the supremum of `L` over the unit
fields supported in each open set. -/
private lemma massMeasure_testCLM_eq_iSup {U : Set Ω} (hU : IsOpen U) :
    massMeasure (testCLM hL) U =
      ⨆ (f : C_c(Ω, F)) (_ : tsupport f ⊆ U) (_ : ∀ x, ‖f x‖ ≤ 1), ENNReal.ofReal (L f) := by
  have hT := hasLocallyFiniteMass_testCLM hL
  refine le_antisymm ?_ (iSup₂_le fun f hfU => iSup_le fun hf => ?_)
  · obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.1 hU
    rw [massMeasure_preimage_coe hT hU', localMass_le_iff]
    intro φ hφU hφ
    have hle (f : C_c(Ω, F)) (hfU : tsupport f ⊆ (↑) ⁻¹' U') (hf : ∀ x, ‖f x‖ ≤ 1) :
        ENNReal.ofReal (L f) ≤ ⨆ (f : C_c(Ω, F)) (_ : tsupport f ⊆ (↑) ⁻¹' U')
          (_ : ∀ x, ‖f x‖ ≤ 1), ENNReal.ofReal (L f) :=
      le_iSup₂_of_le f hfU (le_iSup_of_le hf le_rfl)
    have hφU' := (TestFunction.tsupport_toCompactlySupportedContinuousMap_subset φ).trans
      (preimage_mono hφU)
    have hφ' (x : Ω) : ‖φ.toCompactlySupportedContinuousMap x‖ ≤ 1 := by
      rw [TestFunction.toCompactlySupportedContinuousMap_apply]
      exact hφ x
    rw [testCLM_apply, Real.eNorm_eq_ofReal_abs, abs_eq_max_neg, ENNReal.ofReal_max, ← map_neg]
    refine max_le (hle _ hφU' hφ') (hle _ ?_ fun x => by simpa using hφ' x)
    rwa [CompactlySupportedContinuousMap.coe_neg, tsupport_neg]
  · rw [apply_eq_integral_testCLM hL f]
    exact (Real.ofReal_le_eNorm _).trans (enorm_integral_apply_le_measure
      ((ae_norm_polarDensity_eq_one hT).mono fun _ hx => hx.le) hU.measurableSet
      ((subset_tsupport f).trans hfU) hf)

/-- **The Riesz representation theorem for vector fields.** A linear functional `L` on the
compactly supported continuous fields `C_c(Ω, F)` that is bounded above on the fields of norm at
most one supported in each compact set is integration against a regular measure `μ` with a
measurable density `τ` of dual norm one `μ`-almost everywhere: `L f = ∫ τ(x) (f x) dμ(x)`. The
measure is the total variation of `L`: on an open set `U` it is the supremum of `L f` over the
fields `f` with `‖f x‖ ≤ 1` supported in `U`. The pair is unique
(`TauCeti.RealRMK.measure_eq_of_apply_eq_integral_dual`,
`TauCeti.RealRMK.ae_eq_of_apply_eq_integral_dual`). -/
theorem exists_apply_eq_integral_dual :
    ∃ (μ : Measure Ω) (τ : Ω → StrongDual ℝ F), μ.Regular ∧ Measurable τ ∧
      (∀ᵐ x ∂μ, ‖τ x‖ = 1) ∧ (∀ f : C_c(Ω, F), L f = ∫ x, τ x (f x) ∂μ) ∧
      ∀ U : Set Ω, IsOpen U → μ U =
        ⨆ (f : C_c(Ω, F)) (_ : tsupport f ⊆ U) (_ : ∀ x, ‖f x‖ ≤ 1), ENNReal.ofReal (L f) :=
  ⟨massMeasure (testCLM hL), polarDensity (testCLM hL), inferInstance, measurable_polarDensity,
    ae_norm_polarDensity_eq_one (hasLocallyFiniteMass_testCLM hL), apply_eq_integral_testCLM hL,
    fun _ hU => massMeasure_testCLM_eq_iSup hL hU⟩

end Representation

section Uniqueness

variable [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] {μ₁ μ₂ : Measure Ω} [IsFiniteMeasureOnCompacts μ₁]
  [IsFiniteMeasureOnCompacts μ₂] {τ₁ τ₂ : Ω → StrongDual ℝ F}

omit [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A representation of `L` on `C_c(Ω, F)` represents its restriction to test fields. -/
private lemma testCLM_apply_eq_integral
    (hL : ∀ K : Set Ω, IsCompact K → ∃ C : ℝ, ∀ f : C_c(Ω, F), tsupport f ⊆ K →
      (∀ x, ‖f x‖ ≤ 1) → L f ≤ C)
    {μ : Measure Ω} {τ : Ω → StrongDual ℝ F} (h : ∀ f : C_c(Ω, F), L f = ∫ x, τ x (f x) ∂μ)
    (φ : 𝓓(Ω, F)) : testCLM hL φ = ∫ x, τ x (φ x) ∂μ := by
  rw [testCLM_apply, h]
  simp only [TestFunction.toCompactlySupportedContinuousMap_apply]

/-- **Uniqueness of the measure in the Riesz representation.** Two measures finite on compact sets
that represent the same functional on `C_c(Ω, F)` with densities of dual norm one are equal. -/
theorem measure_eq_of_apply_eq_integral_dual (hτ₁m : AEStronglyMeasurable τ₁ μ₁)
    (hτ₂m : AEStronglyMeasurable τ₂ μ₂) (hτ₁ : ∀ᵐ x ∂μ₁, ‖τ₁ x‖ = 1)
    (hτ₂ : ∀ᵐ x ∂μ₂, ‖τ₂ x‖ = 1) (h₁ : ∀ f : C_c(Ω, F), L f = ∫ x, τ₁ x (f x) ∂μ₁)
    (h₂ : ∀ f : C_c(Ω, F), L f = ∫ x, τ₂ x (f x) ∂μ₂) : μ₁ = μ₂ := by
  have hL := exists_le_of_apply_eq_integral (hτ₁.mono fun _ hx => hx.le) h₁
  exact (massMeasure_eq_of_apply_eq_integral hτ₁m hτ₁ (testCLM_apply_eq_integral hL h₁)).symm.trans
    (massMeasure_eq_of_apply_eq_integral hτ₂m hτ₂ (testCLM_apply_eq_integral hL h₂))

/-- **Uniqueness of the density in the Riesz representation.** Densities of dual norm one that
represent the same functional on `C_c(Ω, F)` against measures finite on compact sets agree almost
everywhere. -/
theorem ae_eq_of_apply_eq_integral_dual (hτ₁m : AEStronglyMeasurable τ₁ μ₁)
    (hτ₂m : AEStronglyMeasurable τ₂ μ₂) (hτ₁ : ∀ᵐ x ∂μ₁, ‖τ₁ x‖ = 1)
    (hτ₂ : ∀ᵐ x ∂μ₂, ‖τ₂ x‖ = 1) (h₁ : ∀ f : C_c(Ω, F), L f = ∫ x, τ₁ x (f x) ∂μ₁)
    (h₂ : ∀ f : C_c(Ω, F), L f = ∫ x, τ₂ x (f x) ∂μ₂) : τ₁ =ᵐ[μ₁] τ₂ := by
  have hL := exists_le_of_apply_eq_integral (hτ₁.mono fun _ hx => hx.le) h₁
  have h₂' := ae_eq_polarDensity_of_apply_eq_integral hτ₂m hτ₂ (testCLM_apply_eq_integral hL h₂)
  rw [measure_eq_of_apply_eq_integral_dual hτ₂m hτ₁m hτ₂ hτ₁ h₂ h₁] at h₂'
  exact (ae_eq_polarDensity_of_apply_eq_integral hτ₁m hτ₁
    (testCLM_apply_eq_integral hL h₁)).trans h₂'.symm

end Uniqueness

section Inner

variable [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {G : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {L : C_c(Ω, G) →ₗ[ℝ] ℝ}

/-- **The Riesz representation theorem for vector fields, inner product form.** A linear
functional `L` on the compactly supported continuous vector fields `C_c(Ω, G)` that is bounded
above on the fields of norm at most one supported in each compact set is
`L f = ∫ ⟪η x, f x⟫ dμ(x)` for a regular measure `μ` and a measurable unit vector field `η`
(`‖η‖ = 1` `μ`-almost everywhere). On an open set `U`, `μ U` is the supremum of `L f` over the
fields `f` with `‖f x‖ ≤ 1` supported in `U`. -/
theorem exists_apply_eq_integral_inner [MeasurableSpace G] [BorelSpace G]
    (hL : ∀ K : Set Ω, IsCompact K → ∃ C : ℝ, ∀ f : C_c(Ω, G), tsupport f ⊆ K →
      (∀ x, ‖f x‖ ≤ 1) → L f ≤ C) :
    ∃ (μ : Measure Ω) (η : Ω → G), μ.Regular ∧ Measurable η ∧ (∀ᵐ x ∂μ, ‖η x‖ = 1) ∧
      (∀ f : C_c(Ω, G), L f = ∫ x, ⟪η x, f x⟫ ∂μ) ∧
      ∀ U : Set Ω, IsOpen U → μ U =
        ⨆ (f : C_c(Ω, G)) (_ : tsupport f ⊆ U) (_ : ∀ x, ‖f x‖ ≤ 1), ENNReal.ofReal (L f) := by
  obtain ⟨μ, τ, hμ, hτm, hτ, hrep, hU⟩ := exists_apply_eq_integral_dual hL
  refine ⟨μ, fun x => (InnerProductSpace.toDual ℝ G).symm (τ x), hμ,
    (InnerProductSpace.toDual ℝ G).symm.continuous.measurable.comp hτm,
    hτ.mono fun x hx => by simpa using hx, fun f => ?_, hU⟩
  simp only [InnerProductSpace.toDual_symm_apply, hrep f]

variable {μ₁ μ₂ : Measure Ω} [IsFiniteMeasureOnCompacts μ₁] [IsFiniteMeasureOnCompacts μ₂]
  {η₁ η₂ : Ω → G}

omit [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- A representation of `L` on `C_c(Ω, G)` by a vector field represents its restriction to
test fields of class `C^0`. -/
private lemma restrictTest_apply_eq_integral_inner {μ : Measure Ω} {η : Ω → G}
    (h : ∀ f : C_c(Ω, G), L f = ∫ x, ⟪η x, f x⟫ ∂μ) (φ : 𝓓^{0}(Ω, G)) :
    restrictTest 0 L φ = ∫ x, ⟪η x, φ x⟫ ∂μ := by
  simp [restrictTest, h]

/-- **Uniqueness of the measure in the Riesz representation, inner product form.** Two measures
finite on compact sets that represent the same functional on `C_c(Ω, G)` with unit vector fields
are equal. -/
theorem measure_eq_of_apply_eq_integral_inner (hη₁m : AEStronglyMeasurable η₁ μ₁)
    (hη₂m : AEStronglyMeasurable η₂ μ₂) (hη₁ : ∀ᵐ x ∂μ₁, ‖η₁ x‖ = 1)
    (hη₂ : ∀ᵐ x ∂μ₂, ‖η₂ x‖ = 1) (h₁ : ∀ f : C_c(Ω, G), L f = ∫ x, ⟪η₁ x, f x⟫ ∂μ₁)
    (h₂ : ∀ f : C_c(Ω, G), L f = ∫ x, ⟪η₂ x, f x⟫ ∂μ₂) : μ₁ = μ₂ :=
  (massMeasure_eq_of_apply_eq_integral_inner hη₁m hη₁
    (restrictTest_apply_eq_integral_inner h₁)).symm.trans
    (massMeasure_eq_of_apply_eq_integral_inner hη₂m hη₂ (restrictTest_apply_eq_integral_inner h₂))

/-- **Uniqueness of the vector field in the Riesz representation, inner product form.** Unit
vector fields that represent the same functional on `C_c(Ω, G)` against measures finite on compact
sets agree almost everywhere. -/
theorem ae_eq_of_apply_eq_integral_inner (hη₁m : AEStronglyMeasurable η₁ μ₁)
    (hη₂m : AEStronglyMeasurable η₂ μ₂) (hη₁ : ∀ᵐ x ∂μ₁, ‖η₁ x‖ = 1)
    (hη₂ : ∀ᵐ x ∂μ₂, ‖η₂ x‖ = 1) (h₁ : ∀ f : C_c(Ω, G), L f = ∫ x, ⟪η₁ x, f x⟫ ∂μ₁)
    (h₂ : ∀ f : C_c(Ω, G), L f = ∫ x, ⟪η₂ x, f x⟫ ∂μ₂) : η₁ =ᵐ[μ₁] η₂ := by
  have hμ₁ := massMeasure_eq_of_apply_eq_integral_inner hη₁m hη₁
    (restrictTest_apply_eq_integral_inner h₁)
  have hμ₂ := massMeasure_eq_of_apply_eq_integral_inner hη₂m hη₂
    (restrictTest_apply_eq_integral_inner h₂)
  subst hμ₁
  rw [← hμ₂] at hη₂m hη₂ h₂
  have hl {η : Ω → G} (hηm : AEStronglyMeasurable η (massMeasure (restrictTest 0 L)))
      (hη : ∀ᵐ x ∂massMeasure (restrictTest 0 L), ‖η x‖ = 1) :
      LocallyIntegrable η (massMeasure (restrictTest 0 L)) :=
    (memLp_top_of_bound hηm 1 (hη.mono fun _ hx => hx.le)).locallyIntegrable le_top
  exact (ae_eq_polarVector (hl hη₁m hη₁) (restrictTest_apply_eq_integral_inner h₁)).trans
    (ae_eq_polarVector (hl hη₂m hη₂) (restrictTest_apply_eq_integral_inner h₂)).symm

end Inner

end TauCeti.RealRMK
