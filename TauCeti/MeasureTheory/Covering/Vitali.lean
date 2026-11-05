/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Summing integral estimates over a Vitali subfamily

Mathlib's `Vitali.exists_disjoint_subfamily_covering_enlargement_ball` extracts, from a family of
balls of bounded radii, a disjoint subfamily whose enlargements cover every ball of the family.
This file records the integral estimate that the extraction is usually applied for: if the
integral of `G` over each enlarged ball `B(x, 4 r x)` is controlled by integrals over `B(x, r x)`,
and all the balls `B(x, r x)` lie in a set `S`, then the integral of `G` over a measurable set
containing every centre is controlled by the same integrals over `S`. Stopping-time arguments,
such as the proof of Gehring's lemma, use it in place of a Calderón–Zygmund decomposition.

## Main statements

* `TauCeti.exists_superset_setLIntegral_le`: summing ball-wise integral estimates over a disjoint
  Vitali subfamily.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal

variable {α : Type*} [PseudoMetricSpace α] [SeparableSpace α] [MeasurableSpace α]
  [OpensMeasurableSpace α] {μ : Measure α}

/-- **Summing over a Vitali subfamily.** Let every centre `x ∈ X` carry a radius `0 < ρ x ≤ ρm`
with `B(x, 2 ρ x) ⊆ S`, and suppose the integral of `G` over each enlarged ball `B(x, 8 ρ x)` is at
most `c (β ∫_{B(x, 2 ρ x)} F₁ + ∫_{B(x, 2 ρ x)} F₂)`. Then `X` lies in a measurable set `U` on
which the integral of `G` is at most `c (β ∫_S F₁ + ∫_S F₂)`. -/
theorem exists_superset_setLIntegral_le {X S : Set α} {ρ : α → ℝ} {ρm : ℝ}
    (hρ : ∀ x ∈ X, 0 < ρ x ∧ ρ x ≤ ρm) (hS : ∀ x ∈ X, ball x (2 * ρ x) ⊆ S)
    {G F₁ F₂ : α → ℝ≥0∞} {c β : ℝ≥0∞}
    (hball : ∀ x ∈ X, ∫⁻ y in ball x (4 * (2 * ρ x)), G y ∂μ ≤
      c * (β * ∫⁻ y in ball x (2 * ρ x), F₁ y ∂μ + ∫⁻ y in ball x (2 * ρ x), F₂ y ∂μ)) :
    ∃ U, MeasurableSet U ∧ X ⊆ U ∧
      ∫⁻ y in U, G y ∂μ ≤ c * (β * ∫⁻ y in S, F₁ y ∂μ + ∫⁻ y in S, F₂ y ∂μ) := by
  -- A disjoint subfamily whose `4`-fold enlargements cover the balls `B(x, 2 ρ x)`.
  obtain ⟨u, huX, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball X
    id (fun x => 2 * ρ x) (2 * ρm) (fun a ha => by linarith [(hρ a ha).2]) 4 (by norm_num)
  have hucount : u.Countable := hudisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun a ha => nonempty_ball.2 (by linarith [(hρ a (huX ha)).1]))
  have : Countable u := hucount.to_subtype
  refine ⟨⋃ a : u, ball (a : α) (4 * (2 * ρ a)),
    (isOpen_iUnion fun _ => isOpen_ball).measurableSet, fun x hx => ?_, ?_⟩
  · obtain ⟨c, hcu, hc⟩ := hucov x hx
    exact mem_iUnion.2 ⟨⟨c, hcu⟩, hc (mem_ball_self (by linarith [(hρ x hx).1]))⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun a : u => ball (a : α) (2 * ρ a)) :=
    fun a a' haa' => hudisj a.2 a'.2 (Subtype.coe_injective.ne haa')
  have hUS : (⋃ a : u, ball (a : α) (2 * ρ a)) ⊆ S := iUnion_subset fun a => hS a (huX a.2)
  have hsum : ∀ F : α → ℝ≥0∞, ∑' a : u, ∫⁻ y in ball (a : α) (2 * ρ a), F y ∂μ ≤
      ∫⁻ y in S, F y ∂μ := fun F => by
    rw [← lintegral_iUnion (fun _ => measurableSet_ball) hdisj]
    exact lintegral_mono_set hUS
  calc _ ≤ ∑' a : u, ∫⁻ y in ball (a : α) (4 * (2 * ρ a)), G y ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' a : u, c * (β * ∫⁻ y in ball (a : α) (2 * ρ a), F₁ y ∂μ +
          ∫⁻ y in ball (a : α) (2 * ρ a), F₂ y ∂μ) := tsum_le_tsum fun a => hball a (huX a.2)
    _ = c * (β * ∑' a : u, ∫⁻ y in ball (a : α) (2 * ρ a), F₁ y ∂μ +
          ∑' a : u, ∫⁻ y in ball (a : α) (2 * ρ a), F₂ y ∂μ) := by
        rw [ENNReal.tsum_mul_left, tsum_add, ENNReal.tsum_mul_left]
    _ ≤ _ := by gcongr <;> exact hsum _

end TauCeti
