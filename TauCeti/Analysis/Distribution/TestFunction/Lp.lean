/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.Analysis.Distribution.Mass.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import TauCeti.Analysis.Distribution.TestFunction.Approximation
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.Support

/-!
# Test functions in `Lᵖ` spaces

Let `Ω` be an open set of a real normed space `E` and let `μ` be a measure on `Ω`, finite on
compact sets; it need not be finite near the frontier of `Ω`. The restriction to `Ω` of a test
function on `Ω` is a continuous compactly supported function on `Ω`, hence lies in `Lᵖ(μ)`. This
file packages the resulting map `𝓓^{n}(Ω, F) → Lᵖ(μ; F)` as a continuous linear map for the
test-function topology, and shows that its range is dense when `1 ≤ p < ∞`, `E` is
finite-dimensional, `F` is complete and `μ` is regular. For a measure on the ambient space `E`
itself, `TestFunction.ambientToLp` is the corresponding map `𝓓^{n}(Ω, F) → Lᵖ(ν; F)`.

Density is what allows a functional on test functions dominated by an `Lᵖ(μ)` norm to be extended
to all of `Lᵖ(μ)`; for the mass measure of a current of locally finite mass this gives its
evaluation on integrable forms (`Distribution.extendL1`).

## Main declarations

* `TestFunction.toLp`: the class in `Lᵖ(μ)` of the restriction of a test function to `Ω`.
* `TestFunction.ambientToLp`: the class in `Lᵖ(ν)` of a test function, for a measure `ν` on the
  ambient space.
* `TestFunction.indicatorToLp`: the class in `Lᵖ(μ)` of `1_A φ`, for a measurable set `A ⊆ Ω`.
  It is zero for `A = ∅`, is `toLp` for `A = Ω` and is additive on disjoint sets
  (`TestFunction.indicatorToLp_empty`, `_univ`, `_union`).
* `HasCompactSupport.exists_testFunction_eLpNorm_sub_le`: a continuous compactly supported
  function on `Ω` is an `Lᵖ(μ)` limit of test functions for `p < ∞`.
* `HasCompactSupport.exists_testFunction_eLpNorm_sub_le_and_norm_le`: if the continuous compactly
  supported function has pointwise norm at most `M`, the approximating test function can also be
  chosen with pointwise norm at most `M` everywhere.
* `TestFunction.denseRange_toLp`: test functions are dense in `Lᵖ(μ)` for `p < ∞`.
* `MeasureTheory.MemLp.exists_testFunction_eLpNorm_sub_le_and_norm_le`: for `1 ≤ p < ∞` and a
  regular measure `μ` on `Ω`, a function in `Lᵖ(μ)` bounded almost everywhere by `M` in norm is
  approximated in `Lᵖ(μ)` by test functions bounded everywhere by `M` in norm.
* `MeasureTheory.Integrable.exists_testFunction_lintegral_sub_le_and_norm_le` and
  `MeasureTheory.Integrable.exists_testFunction_top_lintegral_sub_le_and_norm_le`: the `L¹`
  versions on `Ω` and on the whole space.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Theorem 1.3.2
  (density of test functions in `Lᵖ`).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter Set Metric
open scoped BoundedContinuousFunction ENNReal Distributions InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞}
  {p : ℝ≥0∞} {μ : Measure Ω}

/-- A continuous function with compact support in `Ω` is the `Lᵖ(μ)` limit of test functions, for
`p < ∞` and a measure `μ` on `Ω` that is finite on compact sets. -/
theorem HasCompactSupport.exists_testFunction_eLpNorm_sub_le [IsFiniteMeasureOnCompacts μ]
    [FiniteDimensional ℝ E] [CompleteSpace F] {g : Ω → F} (hgc : HasCompactSupport g)
    (hg : Continuous g) (hp : p ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ φ : 𝓓^{n}(Ω, F), eLpNorm (g - fun x : Ω => φ x) p μ ≤ ε := by
  -- Mollify the extension of `g` by zero, inside a closed thickening `K'` of its support.
  set K : Set E := (↑) '' tsupport g
  have hK : IsCompact K := hgc.isCompact.image continuous_subtype_val
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen
    (image_subset_iff.2 fun x _ => x.2)
  set K' := cthickening δ K
  set M := μ ((↑) ⁻¹' K') ^ (1 / p.toReal)
  have hM : M ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK.cthickening
      (by simpa using hδΩ)).measure_ne_top
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_nnreal_pos_mul_lt hM hε
  obtain ⟨φ, hφK', hφ⟩ := (hgc.continuous_extend_zero Ω.isOpen hg).exists_testFunction_dist_le hK
    (hgc.tsupport_extend_zero_subset continuous_subtype_val) hδ hδΩ (NNReal.coe_pos.2 hη)
  refine ⟨⟨φ, φ.contDiff.of_le (WithTop.coe_le_coe.2 le_top), φ.hasCompactSupport,
    φ.tsupport_subset⟩, ?_⟩
  -- The error is supported in `K'` and bounded by `η` there.
  simp only [TestFunction.coe_mk]
  refine (eLpNorm_sub_le_of_dist_bdd μ hp
    (measurable_subtype_coe isClosed_cthickening.measurableSet).nullMeasurableSet η.coe_nonneg
    (hg.sub (φ.continuous.comp continuous_subtype_val)).aestronglyMeasurable (fun x => ?_)
    (fun x hx => self_subset_cthickening K (mem_image_of_mem _ (subset_tsupport _ hx)))
    fun x hx => hφK' (subset_tsupport _ hx)).trans ?_
  · rw [dist_comm]
    simpa [Subtype.val_injective.extend_apply] using hφ x
  · rw [ENNReal.ofReal_coe_nnreal]
    exact hηε.le

/-- A continuous compactly supported function on `Ω` bounded by `M` in norm is approximated in
`Lᵖ(μ)` (`p < ∞`) by test functions that are also bounded by `M` in norm everywhere on `E`. -/
theorem HasCompactSupport.exists_testFunction_eLpNorm_sub_le_and_norm_le
    [IsFiniteMeasureOnCompacts μ] [FiniteDimensional ℝ E] [CompleteSpace F] {g : Ω → F}
    (hgc : HasCompactSupport g) (hg : Continuous g) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x, ‖g x‖ ≤ M) (hp : p ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ φ : 𝓓^{n}(Ω, F), (∀ y, ‖φ y‖ ≤ M) ∧ eLpNorm (g - fun x : Ω => φ x) p μ ≤ ε := by
  rcases hM0.eq_or_lt with rfl | hMpos
  · have hg0 : g = 0 := funext fun x => norm_le_zero_iff.mp (hM x)
    exact ⟨0, fun _ => by simp, by simp [hg0]⟩
  set K : Set E := (↑) '' tsupport g
  have hK : IsCompact K := hgc.isCompact.image continuous_subtype_val
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen
    (image_subset_iff.2 fun x _ => x.2)
  set K' := cthickening δ K
  set C := μ ((↑) ⁻¹' K') ^ (1 / p.toReal)
  have hC : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK.cthickening
      (by simpa using hδΩ)).measure_ne_top
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_nnreal_pos_mul_lt hC (ENNReal.half_pos hε).ne'
  obtain ⟨φ₀, hφ₀K', hφ₀⟩ := (hgc.continuous_extend_zero Ω.isOpen hg).exists_testFunction_dist_le
    hK (hgc.tsupport_extend_zero_subset continuous_subtype_val) hδ hδΩ (NNReal.coe_pos.2 hη)
  -- Uniform distance `η` from the zero-extension of `g` bounds `‖φ₀‖` by `M + η`, so scaling by
  -- `M / (M + η)` restores the norm bound `M` while changing values by at most `η`.
  have : (0 : ℝ) < η := NNReal.coe_pos.2 hη
  have hφ₀norm (y : E) : ‖φ₀ y‖ ≤ M + η := by
    have hext : ‖Subtype.val.extend g 0 y‖ ≤ M := by
      by_cases hy : ∃ x : Ω, (x : E) = y
      · obtain ⟨x, rfl⟩ := hy
        simpa [Subtype.val_injective.extend_apply] using hM x
      · simp [Function.extend_apply' _ _ _ hy, hM0]
    have hdist := hφ₀ y
    rw [dist_eq_norm] at hdist
    calc ‖φ₀ y‖ = ‖(φ₀ y - Subtype.val.extend g 0 y) + Subtype.val.extend g 0 y‖ := by abel_nf
      _ ≤ ‖φ₀ y - Subtype.val.extend g 0 y‖ + ‖Subtype.val.extend g 0 y‖ := norm_add_le _ _
      _ ≤ η + M := add_le_add hdist hext
      _ = M + η := add_comm _ _
  set c : ℝ := M / (M + η)
  have hc0 : 0 ≤ c := by positivity
  let ψ : 𝓓^{n}(Ω, F) := ⟨φ₀, φ₀.contDiff.of_le (WithTop.coe_le_coe.2 le_top),
    φ₀.hasCompactSupport, φ₀.tsupport_subset⟩
  refine ⟨c • ψ, fun y => ?_, ?_⟩
  · simp only [FunLike.coe_smul, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_left (hφ₀norm y) hc0).trans_eq
      (div_mul_cancel₀ M (by positivity))
  · refine (eLpNorm_sub_le_of_dist_bdd μ hp
      (measurable_subtype_coe isClosed_cthickening.measurableSet).nullMeasurableSet
      (by positivity : (0 : ℝ) ≤ 2 * η)
      (hg.sub ((c • ψ).continuous.comp continuous_subtype_val)).aestronglyMeasurable
      (fun x => ?_)
      (fun x hx => self_subset_cthickening K (mem_image_of_mem _ (subset_tsupport _ hx)))
      fun x hx => hφ₀K' (subset_tsupport _ fun h0 => hx (by simp [ψ, h0]))).trans ?_
    · have hx1 : dist (g x) (φ₀ x) ≤ η := by
        rw [dist_comm]
        simpa [Subtype.val_injective.extend_apply] using hφ₀ x
      have hx2 : dist (φ₀ x) ((c • ψ) x) ≤ η := by
        have h1c : 1 - c = (η : ℝ) / (M + η) := by simp [c]; field_simp; ring
        have hsub : φ₀ x - (c • ψ) x = (1 - c) • φ₀ x := by
          simp [ψ, sub_smul]
        rw [dist_eq_norm, hsub, norm_smul, h1c, Real.norm_of_nonneg (by positivity)]
        exact (mul_le_mul_of_nonneg_left (hφ₀norm x) (by positivity)).trans_eq
          (div_mul_cancel₀ _ (by positivity))
      exact (dist_triangle (g x) (φ₀ x) ((c • ψ) x)).trans (by linarith)
    · rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal,
        mul_assoc]
      calc 2 * (↑η * C) ≤ 2 * (ε / 2) := mul_le_mul_right hηε.le 2
        _ = ε := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top

namespace TestFunction

/-- The restriction of a test function on `Ω` to `Ω` lies in `Lᵖ(μ)` for every measure `μ` on `Ω`
that is finite on compact sets. -/
theorem memLp_subtype [IsFiniteMeasureOnCompacts μ] (φ : 𝓓^{n}(Ω, F)) :
    MemLp (fun x : Ω => φ x) p μ := by
  rw [← funext (toCompactlySupportedContinuousMap_apply φ)]
  exact (map_continuous _).memLp_of_hasCompactSupport
    φ.toCompactlySupportedContinuousMap.hasCompactSupport

variable {A : Set Ω}

variable (p μ) in
/-- The class in `Lᵖ(μ)` of `1_A φ`, the restriction to `Ω` of a test function `φ` on `Ω` cut off
by the indicator of a measurable set `A ⊆ Ω`, as a linear map. -/
def indicatorToLp [IsFiniteMeasureOnCompacts μ] (hA : MeasurableSet A) :
    𝓓^{n}(Ω, F) →ₗ[ℝ] Lp F p μ where
  toFun φ := ((memLp_subtype φ).indicator hA.nullMeasurableSet).toLp
    (A.indicator fun x : Ω => φ x)
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (.of_eq (by ext x; by_cases hx : x ∈ A <;> simp [hx]))
  map_smul' c φ := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (.of_eq (by ext x; by_cases hx : x ∈ A <;> simp [hx]))

/-- `indicatorToLp p μ hA φ` is the `Lᵖ(μ)` class of `1_A φ`. -/
theorem indicatorToLp_apply [IsFiniteMeasureOnCompacts μ] (hA : MeasurableSet A)
    (φ : 𝓓^{n}(Ω, F)) :
    indicatorToLp p μ hA φ =
      ((memLp_subtype φ).indicator hA.nullMeasurableSet).toLp (A.indicator fun x : Ω => φ x) :=
  (rfl)

variable (p μ) in
/-- Cutting a test function off by the empty set gives zero. -/
@[simp]
theorem indicatorToLp_empty [IsFiniteMeasureOnCompacts μ] :
    (indicatorToLp p μ MeasurableSet.empty : 𝓓^{n}(Ω, F) →ₗ[ℝ] Lp F p μ) = 0 :=
  LinearMap.ext fun φ => by
    simp only [indicatorToLp_apply, indicator_empty, LinearMap.zero_apply]
    exact MemLp.toLp_zero _

variable (p μ) in
/-- `indicatorToLp` is additive on disjoint measurable sets. -/
theorem indicatorToLp_union [IsFiniteMeasureOnCompacts μ] {B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B) :
    (indicatorToLp p μ (hA.union hB) : 𝓓^{n}(Ω, F) →ₗ[ℝ] Lp F p μ) =
      indicatorToLp p μ hA + indicatorToLp p μ hB :=
  LinearMap.ext fun φ => by
    rw [LinearMap.add_apply, indicatorToLp_apply, indicatorToLp_apply, indicatorToLp_apply,
      ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (.of_eq (indicator_union_of_disjoint hAB _))

variable [Fact (1 ≤ p)]

section FiniteOnCompacts

variable [IsFiniteMeasureOnCompacts μ]

/-- The order-zero bound for the class of a test function in `Lᵖ(μ)`. -/
private theorem hasLocallyFiniteMass_memLp_toLp :
    Distribution.HasLocallyFiniteMass fun φ : 𝓓^{n}(Ω, F) =>
      (memLp_subtype (p := p) (μ := μ) φ).toLp fun x : Ω => φ x := by
  refine Distribution.hasLocallyFiniteMass_def.2 fun K hK hKΩ =>
    ⟨(μ ((↑) ⁻¹' K) ^ p.toReal⁻¹).toReal, ENNReal.toReal_nonneg, fun φ hφK => ?_⟩
  exact MemLp.norm_toLp_le_of_support_subset _
    (Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK
      (by simpa using hKΩ)).measure_ne_top
    (fun x hx => hφK (subset_tsupport _ hx)) (norm_nonneg (φ : E →ᵇ F))
    (ae_of_all _ fun x => BoundedContinuousFunction.norm_coe_le_norm (φ : E →ᵇ F) x)

variable (p μ) in
/-- The class in `Lᵖ(μ)` of the restriction to `Ω` of a test function on `Ω`, for a measure `μ`
on `Ω` that is finite on compact sets, as a continuous linear map for the test-function
topology. -/
def toLp : 𝓓^{n}(Ω, F) →L[ℝ] Lp F p μ :=
  let L : 𝓓^{n}(Ω, F) →ₗ[ℝ] Lp F p μ :=
    { toFun φ := (memLp_subtype φ).toLp _
      map_add' φ ψ := by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (.of_eq (by ext; simp))
      map_smul' c φ := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (.of_eq (by ext; simp)) }
  ⟨L, Distribution.HasLocallyFiniteMass.continuous hasLocallyFiniteMass_memLp_toLp⟩

/-- `toLp p μ φ` is the `Lᵖ(μ)` class of the restriction of `φ` to `Ω`. -/
theorem toLp_apply (φ : 𝓓^{n}(Ω, F)) :
    toLp p μ φ = (memLp_subtype φ).toLp fun x : Ω => φ x :=
  (rfl)

variable (p μ) in
/-- Cutting a test function off by all of `Ω` gives its class in `Lᵖ(μ)`. -/
@[simp]
theorem indicatorToLp_univ (φ : 𝓓^{n}(Ω, F)) :
    indicatorToLp p μ MeasurableSet.univ φ = toLp p μ φ := by
  rw [indicatorToLp_apply, toLp_apply]
  exact MemLp.toLp_congr _ _ (.of_eq (indicator_univ _))

variable (p μ) in
/-- The class of a test function in `Lᵖ(μ)` satisfies an order-zero bound on each compact subset
of `Ω`: on the tests supported in a compact `K ⊆ Ω`, its norm is at most a constant depending on
`K` times the sup norm. -/
theorem hasLocallyFiniteMass_toLp :
    Distribution.HasLocallyFiniteMass (toLp p μ : 𝓓^{n}(Ω, F) → Lp F p μ) := by
  rw [funext toLp_apply]
  exact hasLocallyFiniteMass_memLp_toLp

/-- A representative of `toLp p μ φ` agrees almost everywhere with the restriction of `φ`. -/
theorem coeFn_toLp (φ : 𝓓^{n}(Ω, F)) : toLp p μ φ =ᵐ[μ] fun x : Ω => φ x := by
  rw [toLp_apply]
  exact MemLp.coeFn_toLp _

variable (μ) in
/-- The `L¹(μ)` norm of a test function is the integral of its norm. -/
theorem enorm_toLp_one (φ : 𝓓^{n}(Ω, F)) :
    ‖toLp 1 μ φ‖ₑ = ∫⁻ x, ‖φ x‖ₑ ∂μ := by
  rw [Lp.eNorm_def, eLpNorm_congr_ae (coeFn_toLp φ), eLpNorm_one_eq_lintegral_eNorm]
  exact (memLp_subtype (p := 1) φ).aestronglyMeasurable

variable (μ) in
/-- The `L¹(μ)` norm of `1_A φ` is the integral of `‖φ‖` over `A`. -/
theorem enorm_indicatorToLp_one (hA : MeasurableSet A) (φ : 𝓓^{n}(Ω, F)) :
    ‖indicatorToLp 1 μ hA φ‖ₑ = ∫⁻ x in A, ‖φ x‖ₑ ∂μ := by
  rw [indicatorToLp_apply, Lp.eNorm_toLp, eLpNorm_one_eq_lintegral_eNorm,
    ← lintegral_indicator hA]
  · simp_rw [eNorm_indicator_eq_indicator_eNorm]
  · exact ((memLp_subtype (p := 1) φ).indicator hA.nullMeasurableSet).aestronglyMeasurable

/-- Cutting a test function off by an indicator does not increase its `Lᵖ(μ)` norm. -/
theorem norm_indicatorToLp_le (hA : MeasurableSet A) (φ : 𝓓^{n}(Ω, F)) :
    ‖indicatorToLp p μ hA φ‖ ≤ ‖toLp p μ φ‖ := by
  rw [indicatorToLp_apply, toLp_apply, Lp.norm_toLp, Lp.norm_toLp]
  exact ENNReal.toReal_mono (memLp_subtype φ).eLpNorm_ne_top
    (eLpNorm_indicator_le _ hA.nullMeasurableSet)

end FiniteOnCompacts

section Ambient

variable {ν : Measure E} [IsFiniteMeasureOnCompacts ν]

/-- The order-zero bound for the class of a test function in `Lᵖ(ν)`, for a measure `ν` on `E`. -/
private theorem hasLocallyFiniteMass_memLp_ambientToLp :
    Distribution.HasLocallyFiniteMass fun φ : 𝓓^{n}(Ω, F) =>
      (φ.continuous.memLp_of_hasCompactSupport (p := p) (μ := ν) φ.hasCompactSupport).toLp φ := by
  refine Distribution.hasLocallyFiniteMass_def.2 fun K hK _ =>
    ⟨(ν K ^ p.toReal⁻¹).toReal, ENNReal.toReal_nonneg, fun φ hφK => ?_⟩
  exact MemLp.norm_toLp_le_of_support_subset _ hK.measure_ne_top
    (fun x hx => hφK (subset_tsupport _ hx)) (norm_nonneg (φ : E →ᵇ F))
    (ae_of_all _ fun x => BoundedContinuousFunction.norm_coe_le_norm (φ : E →ᵇ F) x)

variable (p ν) in
/-- The class in `Lᵖ(ν)` of a test function on `Ω`, for a measure `ν` on the ambient space `E`
that is finite on compact sets, as a continuous linear map for the test-function topology. Unlike
`TestFunction.toLp`, the measure lives on `E`: a test function vanishes off `Ω`, so it needs no
restriction. -/
def ambientToLp : 𝓓^{n}(Ω, F) →L[ℝ] Lp F p ν :=
  let L : 𝓓^{n}(Ω, F) →ₗ[ℝ] Lp F p ν :=
    { toFun φ := (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ
      map_add' φ ψ := by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (.of_eq (by ext; simp))
      map_smul' c φ := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (.of_eq (by ext; simp)) }
  ⟨L, Distribution.HasLocallyFiniteMass.continuous hasLocallyFiniteMass_memLp_ambientToLp⟩

/-- `ambientToLp p ν φ` is the `Lᵖ(ν)` class of `φ`. -/
theorem ambientToLp_apply (φ : 𝓓^{n}(Ω, F)) :
    ambientToLp p ν φ = (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ :=
  (rfl)

/-- A representative of `ambientToLp p ν φ` agrees almost everywhere with `φ`. -/
theorem coeFn_ambientToLp (φ : 𝓓^{n}(Ω, F)) : ambientToLp p ν φ =ᵐ[ν] φ := by
  rw [ambientToLp_apply]
  exact MemLp.coeFn_toLp _

/-- The squared `L²(ν)` norm of the class of a test function is the integral of its squared
pointwise norm. -/
theorem norm_ambientToLp_sq (φ : 𝓓^{n}(Ω, F)) : ‖ambientToLp 2 ν φ‖ ^ 2 = ∫ x, ‖φ x‖ ^ 2 ∂ν := by
  rw [ambientToLp_apply]
  exact MemLp.norm_toLp_sq _

end Ambient

/-- The `L²(ν)` inner product with the class of a test function is the integral of the pointwise
inner product. -/
theorem inner_ambientToLp {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {ν : Measure E} [IsFiniteMeasureOnCompacts ν] (u : Lp G 2 ν) (φ : 𝓓^{n}(Ω, G)) :
    ⟪u, ambientToLp 2 ν φ⟫_ℝ = ∫ x, ⟪u x, φ x⟫_ℝ ∂ν := by
  rw [ambientToLp_apply]
  exact L2.inner_toLp u _

/-- **Density of test functions in `Lᵖ`.** For `1 ≤ p < ∞` and a regular measure `μ` on an open
set `Ω` of a finite-dimensional space, the classes of test functions are dense in `Lᵖ(μ; F)`. -/
theorem denseRange_toLp [FiniteDimensional ℝ E] [CompleteSpace F] [μ.Regular] (hp : p ≠ ∞) :
    DenseRange (toLp p μ : 𝓓^{n}(Ω, F) →L[ℝ] Lp F p μ) := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  refine fun f => (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε => ?_
  -- Approximate `f` by a continuous function with compact support, and that by a test function.
  obtain ⟨g, hgc, hfg, hg, _⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le hp
    (ENNReal.half_pos hε.ne').ne'
  obtain ⟨φ, hφ⟩ := hgc.exists_testFunction_eLpNorm_sub_le (n := n) (μ := μ) hg hp
    (ENNReal.half_pos hε.ne').ne'
  refine ⟨_, mem_range_self φ, ?_⟩
  rw [Metric.mem_closedEBall', ← Lp.toLp_coeFn f (Lp.memLp f), toLp_apply, Lp.edist_toLp_toLp,
    ← ENNReal.add_halves ε, ← sub_add_sub_cancel (⇑f) g]
  exact (eLpNorm_add_le Fact.out).trans (add_le_add hfg hφ)

end TestFunction

namespace MeasureTheory

/-- Radial projection onto the closed ball of radius `M > 0` sends every vector into that ball. -/
private theorem norm_radialClamp_le {M : ℝ} (hM : 0 < M) (v : F) :
    ‖(max 1 (‖v‖ / M))⁻¹ • v‖ ≤ M := by
  rcases le_or_gt ‖v‖ M with hv | hv
  · rw [max_eq_left ((div_le_one hM).2 hv), inv_one, one_smul]
    exact hv
  · have hv0 : 0 < ‖v‖ := hM.trans hv
    rw [max_eq_right ((one_le_div hM).2 hv.le), inv_div, norm_smul,
      Real.norm_of_nonneg (by positivity), div_mul_cancel₀ M hv0.ne']

/-- Radial clamping to radius `M > 0` at most doubles the distance to any vector `u` of norm at
most `M`, in an arbitrary normed space. -/
private theorem norm_sub_radialClamp_le {M : ℝ} (hM : 0 < M) {u : F} (hu : ‖u‖ ≤ M) (v : F) :
    ‖u - (max 1 (‖v‖ / M))⁻¹ • v‖ ≤ 2 * ‖u - v‖ := by
  rcases le_or_gt ‖v‖ M with hv | hv
  · rw [max_eq_left ((div_le_one hM).2 hv), inv_one, one_smul]
    linarith [norm_nonneg (u - v)]
  · have hv0 : 0 < ‖v‖ := hM.trans hv
    rw [max_eq_right ((one_le_div hM).2 hv.le), inv_div]
    have hdiff : v - (M / ‖v‖) • v = (1 - M / ‖v‖) • v := by simp [sub_smul]
    have h1 : 0 ≤ 1 - M / ‖v‖ := sub_nonneg.2 ((div_le_one hv0).2 hv.le)
    have hvc : ‖v - (M / ‖v‖) • v‖ ≤ ‖u - v‖ := by
      rw [hdiff, norm_smul, Real.norm_of_nonneg h1, sub_mul, one_mul,
        div_mul_cancel₀ M hv0.ne']
      linarith [norm_sub_norm_le v u, norm_sub_rev v u]
    calc ‖u - (M / ‖v‖) • v‖ = ‖(u - v) + (v - (M / ‖v‖) • v)‖ := by abel_nf
      _ ≤ ‖u - v‖ + ‖v - (M / ‖v‖) • v‖ := norm_add_le _ _
      _ ≤ 2 * ‖u - v‖ := by linarith

/-- **Norm-bounded approximation by test functions in `Lᵖ`.** For `1 ≤ p < ∞` and a regular
measure `μ` on an open set `Ω` of a finite-dimensional space, a function `f` in `Lᵖ(μ; F)` with
`‖f x‖ ≤ M` almost everywhere can be approximated in `Lᵖ(μ; F)` by test functions `φ` satisfying
`‖φ y‖ ≤ M` everywhere on `E`. -/
theorem MemLp.exists_testFunction_eLpNorm_sub_le_and_norm_le [Fact (1 ≤ p)]
    [FiniteDimensional ℝ E] [CompleteSpace F] [μ.Regular] {f : Ω → F} (hf : MemLp f p μ)
    (hp : p ≠ ∞) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ φ : 𝓓^{n}(Ω, F), (∀ y, ‖φ y‖ ≤ M) ∧ eLpNorm (f - fun x : Ω => φ x) p μ ≤ ε := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  rcases hM0.eq_or_lt with rfl | hMpos
  · refine ⟨0, fun _ => by simp, ?_⟩
    have hf0 : (f - fun x : Ω => (0 : 𝓓^{n}(Ω, F)) x) =ᵐ[μ] (0 : Ω → F) :=
      hM.mono fun x hx => by simp [norm_le_zero_iff.mp hx]
    rw [eLpNorm_congr_ae hf0, eLpNorm_zero]
    exact zero_le
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  have hε4 : ε / 2 / 2 ≠ 0 := (ENNReal.half_pos hε2).ne'
  obtain ⟨g₀, hg₀c, hfg₀, hg₀, _⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hp hε4
  -- Radially clamp `g₀` to the ball of radius `M`, losing at most a factor of `2` in `Lᵖ`.
  set q : F → F := fun v => (max 1 (‖v‖ / M))⁻¹ • v
  have hqcont : Continuous q :=
    ((continuous_const.max (continuous_norm.div_const M)).inv₀
      fun v => (zero_lt_one.trans_le (le_max_left _ _)).ne').smul continuous_id
  set g₁ : Ω → F := q ∘ g₀
  have hg₁c : HasCompactSupport g₁ := hg₀c.comp_left (by simp [q] : q 0 = 0)
  have hg₁ : Continuous g₁ := hqcont.comp hg₀
  have hfg₁ : eLpNorm (f - g₁) p μ ≤ ε / 2 := by
    have hpt : ∀ᵐ x ∂μ, ‖(f - g₁) x‖ ≤ ‖((2 : ℝ) • (f - g₀)) x‖ :=
      hM.mono fun x hx => by
        simpa [g₁, q, Pi.smul_apply, norm_smul] using norm_sub_radialClamp_le hMpos hx (g₀ x)
    calc eLpNorm (f - g₁) p μ
        ≤ eLpNorm ((2 : ℝ) • (f - g₀)) p μ :=
          eLpNorm_mono_ae (hf.aestronglyMeasurable.sub hg₁.aestronglyMeasurable) hpt
      _ = 2 * eLpNorm (f - g₀) p μ := by
          rw [eLpNorm_const_smul, Real.eNorm_of_nonneg zero_le_two, ENNReal.ofReal_ofNat]
      _ ≤ 2 * (ε / 2 / 2) := mul_le_mul_right hfg₀ 2
      _ = ε / 2 := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top
  obtain ⟨φ, hφM, hg₁φ⟩ := hg₁c.exists_testFunction_eLpNorm_sub_le_and_norm_le (n := n) (μ := μ)
    hg₁ hM0 (fun x => norm_radialClamp_le hMpos (g₀ x)) hp hε2
  refine ⟨φ, hφM, ?_⟩
  rw [← ENNReal.add_halves ε, ← sub_add_sub_cancel f g₁]
  exact (eLpNorm_add_le Fact.out).trans (add_le_add hfg₁ hg₁φ)

/-- **Norm-bounded approximation by test functions in `L¹(μ)`.** For a regular measure `μ` on `Ω`,
an integrable function bounded almost everywhere by `M` in norm can be approximated in `L¹(μ)` by
test functions bounded everywhere by `M` in norm. -/
theorem Integrable.exists_testFunction_lintegral_sub_le_and_norm_le
    [FiniteDimensional ℝ E] [CompleteSpace F] [μ.Regular] {f : Ω → F} (hf : Integrable f μ)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ φ : 𝓓^{n}(Ω, F), (∀ y, ‖φ y‖ ≤ M) ∧ ∫⁻ x, ‖f x - φ x‖ₑ ∂μ ≤ ε := by
  obtain ⟨φ, hφM, hφ⟩ :=
    (memLp_one_iff_integrable.2 hf).exists_testFunction_eLpNorm_sub_le_and_norm_le
      (n := n) ENNReal.one_ne_top hM0 hM hε
  refine ⟨φ, hφM, ?_⟩
  rwa [eLpNorm_one_eq_lintegral_eNorm (hf.aestronglyMeasurable.sub
    (TestFunction.memLp_subtype (p := 1) (μ := μ) φ).aestronglyMeasurable)] at hφ

/-- **Norm-bounded approximation by test functions in `L¹(ν)` on the whole space.** For a regular
measure `ν` on `E`, an integrable function bounded almost everywhere by `M` in norm can be
approximated in `L¹(ν)` by test functions on `⊤` bounded everywhere by `M` in norm. -/
theorem Integrable.exists_testFunction_top_lintegral_sub_le_and_norm_le
    {ν : Measure E} [FiniteDimensional ℝ E] [CompleteSpace F] [ν.Regular] {f : E → F}
    (hf : Integrable f ν) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂ν, ‖f x‖ ≤ M) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) :
    ∃ φ : 𝓓^{n}(⊤, F), (∀ y, ‖φ y‖ ≤ M) ∧ ∫⁻ x, ‖f x - φ x‖ₑ ∂ν ≤ ε := by
  let μ' : Measure (⊤ : Opens E) := ν.comap Subtype.val
  have : μ'.Regular := Measure.Regular.comap' ν (⊤ : Opens E).isOpen.isOpenEmbedding_subtypeVal
  have hm : MeasurableEmbedding (Subtype.val : (⊤ : Opens E) → E) :=
    MeasurableEmbedding.subtype_coe (⊤ : Opens E).isOpen.measurableSet
  have hmp : MeasurePreserving (Subtype.val : (⊤ : Opens E) → E) μ' ν :=
    ⟨measurable_subtype_coe,
      by rw [hm.map_comap, Subtype.range_coe, Opens.coe_top, Measure.restrict_univ]⟩
  have hf' : Integrable (fun x : (⊤ : Opens E) => f x) μ' := hmp.integrable_comp_of_integrable hf
  have hM' : ∀ᵐ x : (⊤ : Opens E) ∂μ', ‖f x‖ ≤ M := hmp.quasiMeasurePreserving.ae hM
  obtain ⟨φ, hφM, hφ⟩ := hf'.exists_testFunction_lintegral_sub_le_and_norm_le (n := n) hM0 hM' hε
  refine ⟨φ, hφM, ?_⟩
  rwa [← hmp.lintegral_comp_emb hm (f := fun y : E => ‖f y - φ y‖ₑ)]

end MeasureTheory
