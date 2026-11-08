/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import TauCeti.MeasureTheory.Measure.Typeclasses.Finite
-- Non-public: measurability of the sections `ν.map (Prod.mk a)` and Weierstrass approximation are
-- used inside proofs only.
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Measurability of measure-valued maps

This file supplies general-purpose measurability results for maps into the Giry measurable space
of measures.

## Main results

* `TauCeti.MeasureTheory.measurable_sum_smul_dirac` — a countable mixture of Dirac measures at
  fixed atoms is measurable when each weight is measurable.
* `TauCeti.MeasureTheory.measurable_probabilityMeasure_map` — pushing forward along a fixed
  measurable map is measurable on `ProbabilityMeasure`.
* `TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry` — pushing a fixed s-finite measure
  forward along a jointly measurable family of maps is measurable in the parameter.
* `TauCeti.MeasureTheory.measurable_map_finiteMeasure_of_measurable_uncurry` — jointly varying a
  finite measure and the map that pushes it forward is measurable, with a probability-measure
  specialization.
* `MeasureTheory.measurableSet_isLocallyFiniteMeasure` and
  `MeasureTheory.measurableSet_isFiniteMeasureOnCompacts` — local finiteness is a measurable
  condition on measures on a locally compact, sigma-compact Hausdorff space.
* `MeasureTheory.measurable_integral_continuousMap_Icc_of_measurable_integral_pow` — if the
  moments of a family of finite measures on `[l, u]` are measurable, so are all integrals of
  continuous functions (Weierstrass approximation).
* `MeasureTheory.measurable_measure_of_measurable_integral_boundedContinuousFunction` — a family
  of finite measures is Giry-measurable once the integrals of bounded continuous functions are
  measurable.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace MeasureTheory

/-- A countable mixture of Dirac measures at fixed atoms `g i` is measurable in the weights.

Evaluating on a measurable set turns the measure into the sum
`∑' i, f b i * 1_{g i ∈ s}`, and a `tsum` of measurable functions is measurable. The atoms are
indexed by a countable type of their own, so the ambient space `α` may be uncountable. -/
theorem measurable_sum_smul_dirac {β ι α : Type*} [MeasurableSpace β] [MeasurableSpace α]
    [Countable ι] {f : β → ι → ℝ≥0∞} {g : ι → α}
    (hf : ∀ i, Measurable fun b => f b i) :
    Measurable fun b => Measure.sum fun i => f b i • Measure.dirac (g i) := by
  refine Measure.measurable_measure.2 fun s hs => ?_
  simp only [Measure.sum_apply _ hs, _root_.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  exact Measurable.tsum fun i => (hf i).mul_const _

/-- Pushing a probability measure forward along a fixed measurable map is measurable for the Giry
structure that `ProbabilityMeasure` inherits as a subtype of `Measure`. -/
theorem measurable_probabilityMeasure_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f) :
    Measurable fun P : ProbabilityMeasure α => P.map f :=
  ((Measure.measurable_map f hf).comp measurable_subtype_coe).subtype_mk

/-- Pushing a fixed s-finite measure forward along a jointly measurable family of maps `f a` is
measurable in the parameter `a`. -/
theorem measurable_map_of_measurable_uncurry {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] {ν : Measure β} [SFinite ν] {f : α → β → γ}
    (hf : Measurable (Function.uncurry f)) :
    Measurable fun a => ν.map (f a) := by
  -- `ν.map (f a)` is the pushforward along `uncurry f` of the section `ν.map (Prod.mk a)`.
  have hsec : (fun a => ν.map (f a)) = fun a => (ν.map (Prod.mk a)).map (Function.uncurry f) :=
    funext fun a => (Measure.map_map hf measurable_prodMk_left).symm
  rw [hsec]
  exact (Measure.measurable_map _ hf).comp Measurable.map_prodMk_left

/-- Pushing a finite measure forward along a jointly measurable family of maps is jointly
measurable in the measure and the parameter.

This complements `Measure.measurable_map`, where the map is fixed, and
`measurable_map_of_measurable_uncurry`, where the measure is fixed. -/
theorem measurable_map_finiteMeasure_of_measurable_uncurry
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : γ → α → β} (hf : Measurable (Function.uncurry f)) :
    Measurable fun p : FiniteMeasure α × γ => (p.1 : Measure α).map (f p.2) := by
  let diracFinite (c : γ) : FiniteMeasure γ := ⟨Measure.dirac c, inferInstance⟩
  have hdirac : Measurable diracFinite := by
    exact Measure.measurable_dirac.subtype_mk
  have hprod : Measurable fun p : FiniteMeasure α × γ =>
      (Measure.dirac p.2).prod (p.1 : Measure α) := by
    exact FiniteMeasure.measurable_fun_prod.comp
      ((hdirac.comp measurable_snd).prodMk measurable_fst)
  have hmap : Measurable fun p : FiniteMeasure α × γ =>
      ((Measure.dirac p.2).prod (p.1 : Measure α)).map (Function.uncurry f) :=
    (Measure.measurable_map _ hf).comp hprod
  convert hmap using 1
  funext p
  rw [Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left]
  rfl

/-- The probability-measure specialization of
`measurable_map_finiteMeasure_of_measurable_uncurry`. -/
theorem measurable_probabilityMeasure_map_of_measurable_uncurry
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : γ → α → β} (hf : Measurable (Function.uncurry f)) :
    Measurable fun p : ProbabilityMeasure α × γ => p.1.map (f p.2) := by
  have htoFinite : Measurable fun μ : ProbabilityMeasure α => μ.toFiniteMeasure := by
    exact measurable_subtype_coe.subtype_mk
  exact ((measurable_map_finiteMeasure_of_measurable_uncurry hf).comp
    (htoFinite.comp measurable_fst |>.prodMk measurable_snd)).subtype_mk

end MeasureTheory

end TauCeti

namespace MeasureTheory

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [T2Space X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]

/-- Local finiteness is a measurable condition in the evaluation sigma-algebra on measures. -/
theorem measurableSet_isLocallyFiniteMeasure :
    MeasurableSet {μ : Measure X | IsLocallyFiniteMeasure μ} := by
  let K := CompactExhaustion.choice X
  simp_rw [K.isLocallyFiniteMeasure_iff]
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun n =>
    measurableSet_lt (Measure.measurable_coe (K.isCompact n).measurableSet) measurable_const

/-- Finiteness on compact sets is measurable in the evaluation sigma-algebra on measures. -/
theorem measurableSet_isFiniteMeasureOnCompacts :
    MeasurableSet {μ : Measure X | IsFiniteMeasureOnCompacts μ} := by
  let K := CompactExhaustion.choice X
  simp_rw [K.isFiniteMeasureOnCompacts_iff]
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun n =>
    measurableSet_lt (Measure.measurable_coe (K.isCompact n).measurableSet) measurable_const

end MeasureTheory

section Giry

open Filter
open scoped BoundedContinuousFunction NNReal

namespace MeasureTheory

/-- A continuous function on a compact interval is integrable against any finite measure. -/
private lemma integrable_of_continuous_Icc {l u : ℝ} {ν : Measure ↥(Set.Icc l u)}
    [IsFiniteMeasure ν] {f : ↥(Set.Icc l u) → ℝ} (hf : Continuous f) : Integrable f ν :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- If the moments `a ↦ ∫ x, x ^ n ∂ν a` of a family of finite measures on `[l, u]` are
measurable, then so is `a ↦ ∫ x, g x ∂ν a` for every continuous `g`. -/
theorem measurable_integral_continuousMap_Icc_of_measurable_integral_pow {α : Type*} {l u : ℝ}
    [MeasurableSpace α] {ν : α → Measure ↥(Set.Icc l u)} [∀ a, IsFiniteMeasure (ν a)]
    (hmom : ∀ n : ℕ, Measurable fun a => ∫ x, ((x : ℝ)) ^ n ∂(ν a))
    (g : C(↥(Set.Icc l u), ℝ)) : Measurable fun a => ∫ x, g x ∂(ν a) := by
  have hpoly : ∀ p : Polynomial ℝ, Measurable fun a => ∫ x, p.eval ((x : ℝ)) ∂(ν a) := by
    intro p
    have hrw : (fun a => ∫ x, p.eval ((x : ℝ)) ∂(ν a))
        = fun a => ∑ i ∈ Finset.range (p.natDegree + 1),
            p.coeff i * ∫ x, ((x : ℝ)) ^ i ∂(ν a) := by
      funext a
      simp_rw [Polynomial.eval_eq_sum_range]
      rw [integral_finsetSum _ fun i _ =>
        integrable_of_continuous_Icc
          (f := fun x : ↥(Set.Icc l u) => p.coeff i * ((x : ℝ)) ^ i) (by fun_prop)]
      simp_rw [integral_const_mul]
    rw [hrw]
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul (hmom i)
  have hcont : ∀ g : C(↥(Set.Icc l u), ℝ), Measurable fun a => ∫ x, g x ∂(ν a) := by
    intro g
    have happrox : ∀ n : ℕ, ∃ p : Polynomial ℝ,
        ‖p.toContinuousMapOn (Set.Icc l u) - g‖ < 1 / (n + 1) := fun n =>
      exists_polynomial_near_continuousMap l u g (1 / (n + 1)) (by positivity)
    choose q hq using happrox
    have hbound : ∀ (n : ℕ) (x : ↥(Set.Icc l u)),
        ‖(q n).eval ((x : ℝ)) - g x‖ ≤ 1 / ((n : ℝ) + 1) := by
      intro n x
      have hx := ContinuousMap.norm_coe_le_norm
        ((q n).toContinuousMapOn (Set.Icc l u) - g) x
      simpa using hx.trans (hq n).le
    refine measurable_of_tendsto_metrizable
      (f := fun n a => ∫ x, (q n).eval ((x : ℝ)) ∂(ν a)) (fun n => hpoly (q n)) ?_
    rw [tendsto_pi_nhds]
    intro a
    have hgint : Integrable (fun x => g x) (ν a) := integrable_of_continuous_Icc g.continuous
    have hqint : ∀ n, Integrable (fun x : ↥(Set.Icc l u) => (q n).eval ((x : ℝ))) (ν a) :=
      fun n => integrable_of_continuous_Icc ((q n).continuous.comp continuous_subtype_val)
    have key : ∀ n : ℕ, ‖(∫ x, (q n).eval ((x : ℝ)) ∂(ν a)) - ∫ x, g x ∂(ν a)‖
        ≤ (1 / ((n : ℝ) + 1)) * (ν a).real Set.univ := by
      intro n
      rw [← integral_sub (hqint n) hgint]
      exact norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall fun x => hbound n x)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) key ?_
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ((ν a).real Set.univ)
  exact hcont g

/-- A family of finite measures on a Borel space in which closed sets are approximated from above
by bounded continuous functions is measurable for the Giry σ-algebra as soon as
`a ↦ ∫ x, g x ∂ν a` is measurable for every bounded continuous `g`. -/
theorem measurable_measure_of_measurable_integral_boundedContinuousFunction {α X : Type*}
    [MeasurableSpace α] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] {ν : α → Measure X} [∀ a, IsFiniteMeasure (ν a)]
    (hcont : ∀ g : X →ᵇ ℝ, Measurable fun a => ∫ x, g x ∂(ν a)) :
    Measurable ν := by
  -- Non-negative bounded continuous test functions, in `ℝ≥0∞` form.
  have hlint : ∀ g : X →ᵇ ℝ≥0, Measurable fun a => ∫⁻ x, (g x : ℝ≥0∞) ∂(ν a) := by
    intro g
    have hrw : (fun a => ∫⁻ x, (g x : ℝ≥0∞) ∂(ν a))
        = fun a => ENNReal.ofReal (∫ x, ((g x : ℝ)) ∂(ν a)) := by
      funext a
      rw [← BoundedContinuousFunction.toReal_lintegral_coe_eq_integral g (ν a),
        ENNReal.ofReal_toReal (BoundedContinuousFunction.lintegral_lt_top_of_nnreal (ν a) g).ne]
    rw [hrw]
    exact ENNReal.measurable_ofReal.comp (hcont
      ⟨⟨fun x => (g x : ℝ), NNReal.continuous_coe.comp g.continuous⟩,
        g.map_bounded'.imp fun _ hC x y => by simpa [Real.dist_eq, NNReal.dist_eq] using hC x y⟩)
  -- Outer approximation of closed sets transfers measurability to closed sets.
  have hclosed : ∀ F : Set X, IsClosed F → Measurable fun a => ν a F := by
    intro F hF
    have hrw : (fun a => ν a F)
        = fun a => liminf (fun n => ∫⁻ x, (hF.apprSeq n x : ℝ≥0∞) ∂(ν a)) atTop := by
      funext a
      exact (HasOuterApproxClosed.tendsto_lintegral_apprSeq hF (ν a)).liminf_eq.symm
    rw [hrw]
    exact Measurable.liminf fun n => hlint (hF.apprSeq n)
  -- The closed sets are a π-system generating the Borel σ-algebra.
  refine Measurable.measure_of_isPiSystem ?_ isPiSystem_isClosed
    (fun F hF => hclosed F hF) (hclosed _ isClosed_univ)
  rw [BorelSpace.measurable_eq (α := X), borel_eq_generateFrom_isClosed]

end MeasureTheory

end Giry
