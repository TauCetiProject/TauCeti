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
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import TauCeti.Analysis.Distribution.AELeOfIntegral
import TauCeti.Analysis.Distribution.Mass.PolarDensity
import TauCeti.Analysis.Distribution.TestFunction.Approximation
import TauCeti.Analysis.Distribution.TestFunction.Integral
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
(`TauCeti.RealRMK.exists_apply_eq_integral_dual`). The measure and the density are unique: any two
such pairs, with measures finite on compact sets, have the same measure
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

For uniqueness, a second pair `(μ, τ')` dominates evaluation, so `‖L‖ ≤ μ` by the minimality of
the mass measure (`Distribution.massMeasure_le_of_enorm_apply_le`). Writing `‖L‖ = k μ` with
`k ≤ 1`, both `τ'` and `k τ` represent `L` against `μ`, so they agree `μ`-almost everywhere
(`TauCeti.ae_enorm_le_of_forall_enorm_integral_apply_le`), and `‖τ'‖ = 1` forces `k = 1`.

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

section Bounds

/-- A one-sided bound of `L` on the unit fields supported in `K` bounds `|L f|` by a constant times
any pointwise bound on a field `f` supported in `K`. -/
private lemma exists_abs_le {K : Set Ω}
    (hK : ∃ C : ℝ, ∀ f : C_c(Ω, F), tsupport f ⊆ K → (∀ x, ‖f x‖ ≤ 1) → L f ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : C_c(Ω, F), tsupport f ⊆ K → ∀ c : ℝ, 0 ≤ c → (∀ x, ‖f x‖ ≤ c) →
      |L f| ≤ C * c := by
  obtain ⟨C, hC⟩ := hK
  refine ⟨max C 0, le_max_right _ _, fun f hfK c hc hfc => ?_⟩
  -- Rescaling to unit fields gives the bound for every `c' > c`; then let `c' → c`.
  have hpos (c' : ℝ) (hc' : c < c') : |L f| ≤ max C 0 * c' := by
    have hc'0 : 0 < c' := hc.trans_lt hc'
    have hunit (s : ℝ) (hs : |s| = c'⁻¹) : s * L f ≤ max C 0 := by
      rw [← smul_eq_mul, ← map_smul]
      refine (hC (s • f) ?_ fun x => ?_).trans (le_max_left _ _)
      · rw [CompactlySupportedContinuousMap.coe_smul]
        exact (closure_mono (Function.support_const_smul_subset s _)).trans hfK
      rw [CompactlySupportedContinuousMap.smul_apply, norm_smul, Real.norm_eq_abs, hs,
        inv_mul_le_one₀ hc'0]
      exact (hfc x).trans hc'.le
    have h₁ := hunit c'⁻¹ (abs_of_pos (inv_pos.2 hc'0))
    have h₂ := hunit (-c'⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.2 hc'0)])
    have h₁' := (inv_mul_le_iff₀ hc'0).1 h₁
    have h₂' := (inv_mul_le_iff₀ hc'0).1 (by simpa using h₂ : c'⁻¹ * -L f ≤ max C 0)
    rw [abs_le]
    constructor <;> linarith
  exact ge_of_tendsto ((tendsto_id'.2 nhdsWithin_le_nhds).const_mul (max C 0))
    (eventually_nhdsWithin_of_forall (s := Ioi c) fun c' hc' => hpos c' hc')

end Bounds

section Pairing

variable [MeasurableSpace E]

/-- A density of dual norm at most one bounds its pairing with `f` by `∫ ‖f‖`. -/
private lemma enorm_integral_le_lintegral {μ : Measure Ω} {τ : Ω → StrongDual ℝ F}
    (hτ : ∀ᵐ x ∂μ, ‖τ x‖ ≤ 1) (f : Ω → F) :
    ‖∫ x, τ x (f x) ∂μ‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := by
  refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono_ae (hτ.mono fun x hx => ?_))
  refine ((τ x).le_opENorm (f x)).trans (mul_le_of_le_one_left zero_le ?_)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_one.2 hx

omit [NormedSpace ℝ F] in
/-- A field of norm at most one supported in `U` has `∫ ‖f‖ ≤ μ U`. -/
private lemma lintegral_enorm_le_measure (μ : Measure Ω) {f : Ω → F} {U : Set Ω}
    (hU : MeasurableSet U) (hfU : tsupport f ⊆ U) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∫⁻ x, ‖f x‖ₑ ∂μ ≤ μ U := by
  rw [← lintegral_indicator_one hU]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx, Pi.one_apply, ← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 (hf x)
  · simp [image_eq_zero_of_notMem_tsupport fun h => hx (hfU h)]

variable [BorelSpace E] [FiniteDimensional ℝ F]

/-- The pairing of a compactly supported continuous field with an essentially bounded density is
integrable. -/
private lemma integrable_apply {μ : Measure Ω} [IsFiniteMeasureOnCompacts μ]
    {τ : Ω → StrongDual ℝ F} (hτm : AEStronglyMeasurable τ μ) (hτ : ∀ᵐ x ∂μ, ‖τ x‖ ≤ 1)
    (f : C_c(Ω, F)) : Integrable (fun x => τ x (f x)) μ :=
  (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).norm.mono'
    (Continuous.comp_aestronglyMeasurable₂ (g := fun (ℓ : StrongDual ℝ F) v => ℓ v) (by fun_prop)
      hτm f.continuous.aestronglyMeasurable)
    (hτ.mono fun x hx => ((τ x).le_opNorm (f x)).trans (mul_le_of_le_one_left (norm_nonneg _) hx))

omit [FiniteDimensional ℝ F] in
/-- The pairing of a field bounded by `c` and supported in a compact `K` with a density of dual
norm at most one is at most `c μ(K)`. -/
private lemma abs_integral_apply_le {μ : Measure Ω} [IsFiniteMeasureOnCompacts μ]
    {τ : Ω → StrongDual ℝ F} (hτ : ∀ᵐ x ∂μ, ‖τ x‖ ≤ 1) {K : Set Ω} (hK : IsCompact K)
    {f : Ω → F} (hfK : tsupport f ⊆ K) {c : ℝ} (hf : ∀ x, ‖f x‖ ≤ c) :
    |∫ x, τ x (f x) ∂μ| ≤ c * μ.real K := by
  have hint : Integrable (K.indicator fun _ => c) μ :=
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  rw [← Real.norm_eq_abs, mul_comm, ← smul_eq_mul, ← integral_indicator_const _ hK.measurableSet]
  refine norm_integral_le_of_norm_le hint (hτ.mono fun x hx => ?_)
  by_cases hxK : x ∈ K
  · rw [indicator_of_mem hxK]
    exact ((τ x).le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hx).trans (hf x))
  · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport fun h => hxK (hfK h), map_zero,
      norm_zero]

omit [FiniteDimensional ℝ F] in
/-- A representation of `L` against a measure finite on compact sets, with a density of dual norm
at most one, bounds `L` on the unit fields supported in each compact set. -/
private lemma exists_le_of_apply_eq_integral {μ : Measure Ω} [IsFiniteMeasureOnCompacts μ]
    {τ : Ω → StrongDual ℝ F} (hτ : ∀ᵐ x ∂μ, ‖τ x‖ ≤ 1)
    (h : ∀ f : C_c(Ω, F), L f = ∫ x, τ x (f x) ∂μ) (K : Set Ω) (hK : IsCompact K) :
    ∃ C : ℝ, ∀ f : C_c(Ω, F), tsupport f ⊆ K → (∀ x, ‖f x‖ ≤ 1) → L f ≤ C := by
  refine ⟨(μ K).toReal, fun f hfK hf => ?_⟩
  have h' := (enorm_integral_le_lintegral hτ f).trans
    (lintegral_enorm_le_measure μ hK.measurableSet hfK hf)
  rw [← h f, Real.eNorm_eq_ofReal_abs] at h'
  exact (le_abs_self _).trans ((ENNReal.ofReal_le_iff_le_toReal hK.measure_lt_top.ne).1 h')

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Minimality of a unit density.** Let `τ` and `σ` be densities of dual norm one for regular
measures `μ` and `m` on `Ω`, with `m ≤ μ`, that give the same pairings with every test vector
field. Then `μ = m` and `τ = σ` almost everywhere. -/
private lemma eq_of_le_of_integral_apply_eq {μ m : Measure Ω} [IsFiniteMeasureOnCompacts μ]
    [IsFiniteMeasureOnCompacts m]
    {τ σ : Ω → StrongDual ℝ F} (hτm : AEStronglyMeasurable τ μ) (hτ : ∀ᵐ x ∂μ, ‖τ x‖ = 1)
    (hσm : Measurable σ) (hσ : ∀ᵐ x ∂m, ‖σ x‖ = 1) (hle : m ≤ μ)
    (h : ∀ φ : 𝓓(Ω, F), ∫ x, τ x (φ x) ∂μ = ∫ x, σ x (φ x) ∂m) :
    μ = m ∧ τ =ᵐ[μ] σ := by
  have hac : m ≪ μ := Measure.absolutelyContinuous_of_le hle
  have hk1 : ∀ᵐ x ∂μ, m.rnDeriv μ x ≤ 1 := Measure.rnDeriv_le_one_of_le hle
  -- Where the density `k = dm/dμ` is nonzero, `σ` has norm one.
  have hkσ : ∀ᵐ x ∂μ, m.rnDeriv μ x ≠ 0 → ‖σ x‖ = 1 := by
    rwa [← Measure.withDensity_rnDeriv_eq m μ hac,
      ae_withDensity_iff (Measure.measurable_rnDeriv m μ)] at hσ
  set kσ : Ω → StrongDual ℝ F := fun x => (m.rnDeriv μ x).toReal • σ x with hkσ_def
  have hkσ1 : ∀ᵐ x ∂μ, ‖kσ x‖ ≤ 1 := by
    filter_upwards [hk1, hkσ] with x hx hxσ
    by_cases hk0 : m.rnDeriv μ x = 0
    · simp [kσ, hk0]
    · rw [hkσ_def, norm_smul, hxσ hk0, mul_one, Real.norm_eq_abs,
        abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hx)
  have hkσm : AEStronglyMeasurable kσ μ :=
    ((Measure.measurable_rnDeriv m μ).ennreal_toReal.smul hσm).aestronglyMeasurable
  -- `τ` and `k σ` give the same pairings against `μ`, so they agree almost everywhere.
  have hpair (φ : 𝓓(Ω, F)) : ∫ x, (τ - kσ) x (φ x) ∂μ = 0 := by
    have hτφ := integrable_apply hτm (hτ.mono fun _ hx => hx.le) φ.toCompactlySupportedContinuousMap
    have hkσφ := integrable_apply hkσm hkσ1 φ.toCompactlySupportedContinuousMap
    simp only [TestFunction.toCompactlySupportedContinuousMap_apply] at hτφ hkσφ
    simp only [Pi.sub_apply, sub_apply]
    rw [integral_sub hτφ hkσφ, h φ]
    simp only [kσ, smul_apply]
    rw [integral_rnDeriv_smul hac, sub_self]
  have hzero := TauCeti.ae_enorm_le_of_forall_enorm_integral_apply_le (k := 0)
    (((memLp_top_of_bound hτm 1 (hτ.mono fun _ hx => hx.le)).locallyIntegrable le_top).sub
      ((memLp_top_of_bound hkσm 1 hkσ1).locallyIntegrable le_top)) measurable_const (by simp)
    fun U _ φ _ _ => by rw [hpair φ]; simp
  have hτkσ : τ =ᵐ[μ] kσ := hzero.mono fun x hx => by
    rwa [Pi.zero_apply, nonpos_iff_eq_zero, ← ofReal_norm, ENNReal.ofReal_eq_zero,
      norm_le_zero_iff, Pi.sub_apply, sub_eq_zero] at hx
  -- `‖τ‖ = 1` forces `k = 1`.
  have hk : m.rnDeriv μ =ᵐ[μ] 1 := by
    filter_upwards [hτkσ, hτ, hkσ] with x hx hx1 hxσ
    have hk0 : m.rnDeriv μ x ≠ 0 := fun h0 => by simp [hx, kσ, h0] at hx1
    rw [hx, hkσ_def, norm_smul, hxσ hk0, mul_one, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.toReal_eq_one_iff] at hx1
    exact hx1
  have hμ : m = μ := by
    rw [← Measure.withDensity_rnDeriv_eq m μ hac, withDensity_congr_ae hk, withDensity_one]
  refine ⟨hμ.symm, hτkσ.trans ?_⟩
  filter_upwards [hk] with x hx
  simp [kσ, hx]

end Pairing

section Representation

variable [NormedSpace ℝ E]
  (hL : ∀ K : Set Ω, IsCompact K → ∃ C : ℝ, ∀ f : C_c(Ω, F), tsupport f ⊆ K →
    (∀ x, ‖f x‖ ≤ 1) → L f ≤ C)

/-- The restriction of `L` to test vector fields. -/
private def restrictTest (L : C_c(Ω, F) →ₗ[ℝ] ℝ) : 𝓓(Ω, F) →ₗ[ℝ] ℝ where
  toFun φ := L φ.toCompactlySupportedContinuousMap
  map_add' φ ψ := by simp
  map_smul' c φ := by simp

include hL

/-- The restriction of `L` to test vector fields has locally finite mass. -/
private lemma hasLocallyFiniteMass_restrictTest : HasLocallyFiniteMass (restrictTest L) := by
  refine hasLocallyFiniteMass_def.2 fun K hK hKΩ => ?_
  obtain ⟨C, hC0, hC⟩ := exists_abs_le (hL _
    (Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK (by simpa using hKΩ)))
  refine ⟨C, hC0, fun φ hφK => ?_⟩
  rw [Real.norm_eq_abs]
  exact hC _ ((TestFunction.tsupport_toCompactlySupportedContinuousMap_subset φ).trans
    (preimage_mono hφK)) _ (norm_nonneg _) fun x => by
      rw [TestFunction.toCompactlySupportedContinuousMap_apply]
      exact (φ : E →ᵇ F).norm_coe_le_norm x

/-- The restriction of `L` to test vector fields, a distribution of order zero. -/
private def testCLM : 𝓓(Ω, F) →L[ℝ] ℝ :=
  ⟨restrictTest L, (hasLocallyFiniteMass_restrictTest hL).continuous⟩

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
  obtain ⟨C, -, hC⟩ := exists_abs_le (hL _ hK₁)
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
      rw [← integral_sub (integrable_apply hτm hτ f) (integrable_apply hτm hτ _)]
      simp [g]
    have hsplit : L f - ∫ x, polarDensity (testCLM hL) x (f x) ∂massMeasure (testCLM hL) =
        L g - ∫ x, polarDensity (testCLM hL) x (g x) ∂massMeasure (testCLM hL) := by
      rw [hint, map_sub, hφ']
      ring
    rw [hsplit, add_mul]
    refine (abs_sub _ _).trans (add_le_add (hC g hgK ε (le_of_lt hε) hg) ?_)
    rw [mul_comm]
    exact abs_integral_apply_le hτ hK₁ hgK hg
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
    refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
    rw [← Real.eNorm_eq_ofReal_abs]
    exact (enorm_integral_le_lintegral ((ae_norm_polarDensity_eq_one hT).mono fun _ hx => hx.le)
      f).trans (lintegral_enorm_le_measure _ hU.measurableSet hfU hf)

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

/-- Every representation of `L` by a measure finite on compact sets with a density of dual norm
one is the one given by the mass measure and the polar density of the restriction of `L` to test
fields. -/
private lemma eq_massMeasure_testCLM {μ : Measure Ω} [IsFiniteMeasureOnCompacts μ]
    {τ : Ω → StrongDual ℝ F}
    (hτm : AEStronglyMeasurable τ μ) (hτ : ∀ᵐ x ∂μ, ‖τ x‖ = 1)
    (h : ∀ f : C_c(Ω, F), L f = ∫ x, τ x (f x) ∂μ) :
    μ = massMeasure (testCLM hL) ∧ τ =ᵐ[μ] polarDensity (testCLM hL) := by
  have hT := hasLocallyFiniteMass_testCLM hL
  have hle : massMeasure (testCLM hL) ≤ μ := massMeasure_le_of_enorm_apply_le μ fun φ => by
    rw [testCLM_apply, h]
    simp only [TestFunction.toCompactlySupportedContinuousMap_apply]
    exact enorm_integral_le_lintegral (hτ.mono fun _ hx => hx.le) fun x : Ω => φ x
  refine eq_of_le_of_integral_apply_eq hτm hτ measurable_polarDensity
    (ae_norm_polarDensity_eq_one hT) hle fun φ => ?_
  rw [← apply_eq_integral_polarDensity hT φ, testCLM_apply, h]
  simp only [TestFunction.toCompactlySupportedContinuousMap_apply]

end Representation

section Uniqueness

variable [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] {μ₁ μ₂ : Measure Ω} [IsFiniteMeasureOnCompacts μ₁]
  [IsFiniteMeasureOnCompacts μ₂] {τ₁ τ₂ : Ω → StrongDual ℝ F}

/-- **Uniqueness of the measure in the Riesz representation.** Two measures finite on compact sets
that represent the same functional on `C_c(Ω, F)` with densities of dual norm one are equal. -/
theorem measure_eq_of_apply_eq_integral_dual (hτ₁m : AEStronglyMeasurable τ₁ μ₁)
    (hτ₂m : AEStronglyMeasurable τ₂ μ₂) (hτ₁ : ∀ᵐ x ∂μ₁, ‖τ₁ x‖ = 1)
    (hτ₂ : ∀ᵐ x ∂μ₂, ‖τ₂ x‖ = 1) (h₁ : ∀ f : C_c(Ω, F), L f = ∫ x, τ₁ x (f x) ∂μ₁)
    (h₂ : ∀ f : C_c(Ω, F), L f = ∫ x, τ₂ x (f x) ∂μ₂) : μ₁ = μ₂ := by
  have hL := exists_le_of_apply_eq_integral (hτ₁.mono fun _ hx => hx.le) h₁
  exact (eq_massMeasure_testCLM hL hτ₁m hτ₁ h₁).1.trans
    (eq_massMeasure_testCLM hL hτ₂m hτ₂ h₂).1.symm

/-- **Uniqueness of the density in the Riesz representation.** Densities of dual norm one that
represent the same functional on `C_c(Ω, F)` against measures finite on compact sets agree almost
everywhere. -/
theorem ae_eq_of_apply_eq_integral_dual (hτ₁m : AEStronglyMeasurable τ₁ μ₁)
    (hτ₂m : AEStronglyMeasurable τ₂ μ₂) (hτ₁ : ∀ᵐ x ∂μ₁, ‖τ₁ x‖ = 1)
    (hτ₂ : ∀ᵐ x ∂μ₂, ‖τ₂ x‖ = 1) (h₁ : ∀ f : C_c(Ω, F), L f = ∫ x, τ₁ x (f x) ∂μ₁)
    (h₂ : ∀ f : C_c(Ω, F), L f = ∫ x, τ₂ x (f x) ∂μ₂) : τ₁ =ᵐ[μ₁] τ₂ := by
  have hL := exists_le_of_apply_eq_integral (hτ₁.mono fun _ hx => hx.le) h₁
  obtain ⟨hμ₁, hτ₁'⟩ := eq_massMeasure_testCLM hL hτ₁m hτ₁ h₁
  obtain ⟨hμ₂, hτ₂'⟩ := eq_massMeasure_testCLM hL hτ₂m hτ₂ h₂
  rw [hμ₁] at hτ₁' ⊢
  rw [hμ₂] at hτ₂'
  exact hτ₁'.trans hτ₂'.symm

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

omit [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The pairing with a unit vector field, read as a density of dual norm one. -/
private lemma toDual_comp (μ : Measure Ω) {η : Ω → G} (hηm : AEStronglyMeasurable η μ)
    (hη : ∀ᵐ x ∂μ, ‖η x‖ = 1) (h : ∀ f : C_c(Ω, G), L f = ∫ x, ⟪η x, f x⟫ ∂μ) :
    AEStronglyMeasurable (fun x => InnerProductSpace.toDual ℝ G (η x)) μ ∧
      (∀ᵐ x ∂μ, ‖InnerProductSpace.toDual ℝ G (η x)‖ = 1) ∧
      ∀ f : C_c(Ω, G), L f = ∫ x, InnerProductSpace.toDual ℝ G (η x) (f x) ∂μ :=
  ⟨(InnerProductSpace.toDual ℝ G).continuous.comp_aestronglyMeasurable hηm,
    hη.mono fun x hx => by simpa using hx, fun f => by
      simp only [InnerProductSpace.toDual_apply_apply, h f]⟩

/-- **Uniqueness of the measure in the Riesz representation, inner product form.** Two measures
finite on compact sets that represent the same functional on `C_c(Ω, G)` with unit vector fields
are equal. -/
theorem measure_eq_of_apply_eq_integral_inner (hη₁m : AEStronglyMeasurable η₁ μ₁)
    (hη₂m : AEStronglyMeasurable η₂ μ₂) (hη₁ : ∀ᵐ x ∂μ₁, ‖η₁ x‖ = 1)
    (hη₂ : ∀ᵐ x ∂μ₂, ‖η₂ x‖ = 1) (h₁ : ∀ f : C_c(Ω, G), L f = ∫ x, ⟪η₁ x, f x⟫ ∂μ₁)
    (h₂ : ∀ f : C_c(Ω, G), L f = ∫ x, ⟪η₂ x, f x⟫ ∂μ₂) : μ₁ = μ₂ := by
  obtain ⟨hm₁, hn₁, hr₁⟩ := toDual_comp μ₁ hη₁m hη₁ h₁
  obtain ⟨hm₂, hn₂, hr₂⟩ := toDual_comp μ₂ hη₂m hη₂ h₂
  exact measure_eq_of_apply_eq_integral_dual hm₁ hm₂ hn₁ hn₂ hr₁ hr₂

/-- **Uniqueness of the vector field in the Riesz representation, inner product form.** Unit
vector fields that represent the same functional on `C_c(Ω, G)` against measures finite on compact
sets agree almost everywhere. -/
theorem ae_eq_of_apply_eq_integral_inner (hη₁m : AEStronglyMeasurable η₁ μ₁)
    (hη₂m : AEStronglyMeasurable η₂ μ₂) (hη₁ : ∀ᵐ x ∂μ₁, ‖η₁ x‖ = 1)
    (hη₂ : ∀ᵐ x ∂μ₂, ‖η₂ x‖ = 1) (h₁ : ∀ f : C_c(Ω, G), L f = ∫ x, ⟪η₁ x, f x⟫ ∂μ₁)
    (h₂ : ∀ f : C_c(Ω, G), L f = ∫ x, ⟪η₂ x, f x⟫ ∂μ₂) : η₁ =ᵐ[μ₁] η₂ := by
  obtain ⟨hm₁, hn₁, hr₁⟩ := toDual_comp μ₁ hη₁m hη₁ h₁
  obtain ⟨hm₂, hn₂, hr₂⟩ := toDual_comp μ₂ hη₂m hη₂ h₂
  exact (ae_eq_of_apply_eq_integral_dual hm₁ hm₂ hn₁ hn₂ hr₁ hr₂).mono fun x hx =>
    (InnerProductSpace.toDual ℝ G).injective hx

end Inner

end TauCeti.RealRMK
