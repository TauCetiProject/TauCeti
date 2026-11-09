/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Medians of real functions

A **median** of a real function `f` on a finite measure space is a level `m` such that each of
the sublevel set `{f ≤ m}` and the superlevel set `{m ≤ f}` carries at least half of the total
mass. Every almost everywhere measurable `f` has one, integrable or not.

Medians serve as the centre of level-set arguments where the mean does not. A truncation of
`(f - m)⁺` vanishes on `{f ≤ m}`, so on a set of at least half the measure, and the same holds for
`(m - f)⁺` on `{m ≤ f}`; inequalities that need a large zero set, such as the weak-type Poincaré
inequality behind the Sobolev–Poincaré inequality, apply to both. Nothing comparable holds for
the mean: `{f ≤ ∫ f}` may have arbitrarily small measure.

## Main declarations

* `TauCeti.exists_measure_univ_le_two_mul_measure_setOf_le_and_ge`: every almost everywhere
  measurable real function on a finite measure space has a median.
-/

public section

namespace TauCeti

open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}

/-- Right-continuity of the sublevel measures: if every level `t > a` has a sublevel set carrying
half of the mass, so does `a`. -/
private theorem measure_univ_le_two_mul_measure_setOf_le_of_forall_gt (hf : Measurable f) {a : ℝ}
    (h : ∀ t > a, μ univ ≤ 2 * μ {x | f x ≤ t}) : μ univ ≤ 2 * μ {x | f x ≤ a} := by
  have hI : (⋂ k : ℕ, {x | f x ≤ a + 1 / (k + 1)}) = {x | f x ≤ a} := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq]
    exact ⟨fun h => le_of_forall_pos_lt_add fun ε hε => by
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      linarith [h k], fun h k => h.trans (le_add_of_nonneg_right (by positivity))⟩
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (s := fun k : ℕ => {x | f x ≤ a + 1 / (k + 1)})
    (fun k => (measurableSet_le hf measurable_const).nullMeasurableSet)
    (fun i j hij x hx => (show f x ≤ _ from hx).trans (add_le_add le_rfl (by gcongr)))
    ⟨0, measure_ne_top μ _⟩
  rw [hI] at hlim
  exact ge_of_tendsto' (ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofNat_ne_top)) fun k =>
    h _ (lt_add_of_pos_right a (by positivity))

/-- Left limits of the sublevel measures: if every level `t < a` has a sublevel set carrying at
most half of the mass, then the superlevel set `{a ≤ f}` carries at least half. -/
private theorem measure_univ_le_two_mul_measure_setOf_ge_of_forall_lt (hf : Measurable f) {a : ℝ}
    (h : ∀ t < a, 2 * μ {x | f x ≤ t} ≤ μ univ) : μ univ ≤ 2 * μ {x | a ≤ f x} := by
  have hU : (⋃ k : ℕ, {x | f x ≤ a - 1 / (k + 1)}) = {x | f x < a} := by
    ext x
    simp only [mem_iUnion, mem_ofPred_eq]
    refine ⟨fun ⟨k, hk⟩ => hk.trans_lt (sub_lt_self _ (by positivity)), fun h => ?_⟩
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 h)
    exact ⟨k, by linarith⟩
  have hlim := tendsto_measure_iUnion_atTop (μ := μ) (s := fun k : ℕ => {x | f x ≤ a - 1 / (k + 1)})
    (fun i j hij x hx => (show f x ≤ _ from hx).trans (sub_le_sub le_rfl (by gcongr)))
  rw [hU] at hlim
  have hlt : 2 * μ {x | f x < a} ≤ μ univ :=
    le_of_tendsto' (ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofNat_ne_top)) fun k =>
      h _ (sub_lt_self _ (by positivity))
  have hsplit : μ {x | f x < a} + μ {x | a ≤ f x} = μ univ := by
    rw [← measure_union (Set.disjoint_left.2 fun x h₁ h₂ => (not_le.2 h₁) h₂)
      (measurableSet_le measurable_const hf)]
    congr 1
    ext x
    simp [lt_or_ge]
  refine (ENNReal.add_le_add_iff_left
    (ENNReal.mul_ne_top (ENNReal.ofNat_ne_top (n := 2)) (measure_ne_top μ {x | f x < a}))).1 ?_
  calc 2 * μ {x | f x < a} + μ univ ≤ μ univ + μ univ := add_le_add_left hlt _
    _ = 2 * μ {x | f x < a} + 2 * μ {x | a ≤ f x} := by rw [← two_mul, ← hsplit, mul_add]

/-- The existence of a median for a measurable function. -/
private theorem exists_measure_univ_le_two_mul_measure_setOf_le_and_ge_of_measurable
    (hf : Measurable f) :
    ∃ m, μ univ ≤ 2 * μ {x | f x ≤ m} ∧ μ univ ≤ 2 * μ {x | m ≤ f x} := by
  by_cases h0 : μ univ = 0
  · exact ⟨0, by simp [h0]⟩
  -- `m` is the least level whose sublevel set carries half of the mass.
  set T : Set ℝ := {t | μ univ ≤ 2 * μ {x | f x ≤ t}}
  have hTmono : ∀ ⦃s t⦄, s ≤ t → s ∈ T → t ∈ T := fun s t hst hs =>
    hs.trans (mul_le_mul_right (measure_mono fun x hx => (show f x ≤ s from hx).trans hst) _)
  -- Sublevel sets exhaust the space as the level grows, and shrink to `∅` as it decreases.
  have htop : Tendsto (fun k : ℕ => μ {x | f x ≤ k}) atTop (𝓝 (μ univ)) := by
    have hU : (⋃ k : ℕ, {x | f x ≤ k}) = univ :=
      eq_univ_of_forall fun x => mem_iUnion.2 ((exists_nat_ge (f x)).imp fun _ hk => hk)
    rw [← hU]
    exact tendsto_measure_iUnion_atTop fun i j hij x hx =>
      (show f x ≤ i from hx).trans (Nat.cast_le.2 hij)
  have hbot : Tendsto (fun k : ℕ => μ {x | f x ≤ -k}) atTop (𝓝 0) := by
    have hI : (⋂ k : ℕ, {x | f x ≤ -k}) = ∅ :=
      eq_empty_of_forall_notMem fun x hx => by
        obtain ⟨k, hk⟩ := exists_nat_gt (-f x)
        have := mem_iInter.1 hx k
        simp only [mem_ofPred_eq] at this
        linarith
    rw [← measure_empty (μ := μ), ← hI]
    exact tendsto_measure_iInter_atTop
      (fun k => (measurableSet_le hf measurable_const).nullMeasurableSet)
      (fun i j hij x hx => (show f x ≤ -(j : ℝ) from hx).trans
        (neg_le_neg (Nat.cast_le.2 hij))) ⟨0, measure_ne_top μ _⟩
  obtain ⟨k₁, hk₁⟩ := (htop.eventually
    (lt_mem_nhds (ENNReal.half_lt_self h0 (measure_ne_top μ univ)))).exists
  obtain ⟨k₀, hk₀⟩ := (hbot.eventually (gt_mem_nhds (ENNReal.half_pos h0))).exists
  rw [ENNReal.div_lt_iff (by simp) (by simp), mul_comm] at hk₁
  rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp), mul_comm] at hk₀
  have hTne : T.Nonempty := ⟨k₁, hk₁.le⟩
  have hTbdd : BddBelow T :=
    ⟨-k₀, fun t ht => le_of_not_gt fun hlt => not_le.2 hk₀ (hTmono hlt.le ht)⟩
  refine ⟨sInf T, measure_univ_le_two_mul_measure_setOf_le_of_forall_gt hf fun t ht => ?_,
    measure_univ_le_two_mul_measure_setOf_ge_of_forall_lt hf fun t ht =>
      (not_le.1 fun h => notMem_of_lt_csInf ht hTbdd h).le⟩
  obtain ⟨t', ht'T, ht'⟩ := exists_lt_of_csInf_lt hTne ht
  exact hTmono ht'.le ht'T

/-- **Existence of a median.** An almost everywhere measurable real function `f` on a finite
measure space has a median: a level `m` such that both `{f ≤ m}` and `{m ≤ f}` have at least half
of the total measure. -/
theorem exists_measure_univ_le_two_mul_measure_setOf_le_and_ge (hf : AEMeasurable f μ) :
    ∃ m, μ univ ≤ 2 * μ {x | f x ≤ m} ∧ μ univ ≤ 2 * μ {x | m ≤ f x} := by
  obtain ⟨m, h₁, h₂⟩ :=
    exists_measure_univ_le_two_mul_measure_setOf_le_and_ge_of_measurable (μ := μ) hf.measurable_mk
  refine ⟨m, h₁.trans_eq (congrArg _ (measure_congr ?_)),
    h₂.trans_eq (congrArg _ (measure_congr ?_))⟩
  · exact hf.ae_eq_mk.mono fun x hx => congrArg (· ≤ m) hx.symm
  · exact hf.ae_eq_mk.mono fun x hx => congrArg (m ≤ ·) hx.symm

end TauCeti
