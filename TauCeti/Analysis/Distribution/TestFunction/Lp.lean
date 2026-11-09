/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.Analysis.Distribution.Mass.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import TauCeti.Analysis.Distribution.TestFunction.Approximation
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.MeasureTheory.Function.LpSeminorm.Support

/-!
# Test functions in `Lᵖ` spaces

Let `Ω` be an open set of a real normed space `E` and let `μ` be a measure on `Ω`, finite on
compact sets; it need not be finite near the frontier of `Ω`. The restriction to `Ω` of a test
function on `Ω` is a continuous compactly supported function on `Ω`, hence lies in `Lᵖ(μ)`. This
file packages the resulting map `𝓓^{n}(Ω, F) → Lᵖ(μ; F)` as a continuous linear map for the
test-function topology, and shows that its range is dense when `1 ≤ p < ∞`, `E` is
finite-dimensional, `F` is complete and `μ` is regular.

Density is what allows a functional on test functions dominated by an `Lᵖ(μ)` norm to be extended
to all of `Lᵖ(μ)`; for the mass measure of a current of locally finite mass this gives its
evaluation on integrable forms (`Distribution.extendL1`).

## Main declarations

* `TestFunction.toLp`: the class in `Lᵖ(μ)` of the restriction of a test function to `Ω`.
* `TestFunction.indicatorToLp`: the class in `Lᵖ(μ)` of `1_A φ`, for a measurable set `A ⊆ Ω`.
  It is zero for `A = ∅`, is `toLp` for `A = Ω` and is additive on disjoint sets
  (`TestFunction.indicatorToLp_empty`, `_univ`, `_union`).
* `HasCompactSupport.exists_testFunction_eLpNorm_sub_le`: a continuous compactly supported
  function on `Ω` is an `Lᵖ(μ)` limit of test functions for `p < ∞`.
* `TestFunction.denseRange_toLp`: test functions are dense in `Lᵖ(μ)` for `p < ∞`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Theorem 1.3.2
  (density of test functions in `Lᵖ`).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter Set Metric
open scoped BoundedContinuousFunction ENNReal Distributions

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
  have hfin : μ ((↑) ⁻¹' K) ^ p.toReal⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK
        (by simpa using hKΩ)).measure_ne_top
  rw [Lp.norm_toLp, ← ENNReal.toReal_ofReal (norm_nonneg (φ : E →ᵇ F)), ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top)
    (eLpNorm_le_of_ae_bound_of_support_subset (memLp_subtype (p := 1) φ).aestronglyMeasurable
      (fun x hx => hφK (subset_tsupport _ hx))
      (ae_of_all _ fun x => BoundedContinuousFunction.norm_coe_le_norm (φ : E →ᵇ F) x))

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
  rw [Lp.enorm_def, eLpNorm_congr_ae (coeFn_toLp φ), eLpNorm_one_eq_lintegral_enorm]
  exact (memLp_subtype (p := 1) φ).aestronglyMeasurable

variable (μ) in
/-- The `L¹(μ)` norm of `1_A φ` is the integral of `‖φ‖` over `A`. -/
theorem enorm_indicatorToLp_one (hA : MeasurableSet A) (φ : 𝓓^{n}(Ω, F)) :
    ‖indicatorToLp 1 μ hA φ‖ₑ = ∫⁻ x in A, ‖φ x‖ₑ ∂μ := by
  rw [indicatorToLp_apply, Lp.enorm_toLp, eLpNorm_one_eq_lintegral_enorm,
    ← lintegral_indicator hA]
  · simp_rw [enorm_indicator_eq_indicator_enorm]
  · exact ((memLp_subtype (p := 1) φ).indicator hA.nullMeasurableSet).aestronglyMeasurable

/-- Cutting a test function off by an indicator does not increase its `Lᵖ(μ)` norm. -/
theorem norm_indicatorToLp_le (hA : MeasurableSet A) (φ : 𝓓^{n}(Ω, F)) :
    ‖indicatorToLp p μ hA φ‖ ≤ ‖toLp p μ φ‖ := by
  rw [indicatorToLp_apply, toLp_apply, Lp.norm_toLp, Lp.norm_toLp]
  exact ENNReal.toReal_mono (memLp_subtype φ).eLpNorm_ne_top
    (eLpNorm_indicator_le _ hA.nullMeasurableSet)

end FiniteOnCompacts

/-- **Density of test functions in `Lᵖ`.** For `1 ≤ p < ∞` and a regular measure `μ` on an open
set `Ω` of a finite-dimensional space, the classes of test functions are dense in `Lᵖ(μ; F)`. -/
theorem denseRange_toLp [FiniteDimensional ℝ E] [CompleteSpace F] [μ.Regular] (hp : p ≠ ∞) :
    DenseRange (toLp p μ : 𝓓^{n}(Ω, F) →L[ℝ] Lp F p μ) := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  refine fun f => (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε => ?_
  -- Approximate `f` by a continuous function with compact support, and that by a test function.
  obtain ⟨g, hgc, hfg, hg, hgp⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le hp
    (ENNReal.half_pos hε.ne').ne'
  obtain ⟨φ, hφ⟩ := hgc.exists_testFunction_eLpNorm_sub_le (n := n) (μ := μ) hg hp
    (ENNReal.half_pos hε.ne').ne'
  refine ⟨_, mem_range_self φ, ?_⟩
  rw [Metric.mem_closedEBall', ← Lp.toLp_coeFn f (Lp.memLp f), toLp_apply, Lp.edist_toLp_toLp,
    ← ENNReal.add_halves ε, ← sub_add_sub_cancel (⇑f) g]
  exact (eLpNorm_add_le Fact.out).trans (add_le_add hfg hφ)

end TestFunction
