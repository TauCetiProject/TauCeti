/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Log
public import TauCeti.Combinatorics.ComparisonTree.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith

/-!
# Counting bounds for comparison trees

A comparison tree that gives pairwise different outputs on a finite set `A` of inputs satisfies
Kraft's inequality `∑_{x ∈ A} 2⁻¹ ^ cost(x) ≤ 1`: each comparison halves the weight, and two
inputs with different outputs end in different leaves. Hence some input of `A` costs at least
`⌈log₂ |A|⌉` comparisons, and Jensen's inequality for the logarithm bounds the total cost below by
`|A| log₂ |A|`.

## Main results

* `TauCeti.CompTree.sum_two_inv_pow_cost_le_one`: Kraft's inequality for the costs.
* `TauCeti.CompTree.exists_clog_card_le_cost`: some input of a nonempty `A` has cost at least
  `Nat.clog 2 |A| = ⌈log₂ |A|⌉`.
* `TauCeti.CompTree.card_mul_logb_card_le_sum_cost`: the total cost over `A` is at least
  `|A| log₂ |A|`.

## References

* J. Erickson, *Algorithms*, Lecture 12, §12.3.
-/

public section

open Finset

namespace TauCeti

namespace CompTree

variable {n : ℕ} {α β : Type*} [LinearOrder β]

/-- **Kraft's inequality for a comparison tree.** If a comparison tree gives pairwise different
outputs on a finite set `A` of inputs, then `∑_{x ∈ A} 2⁻¹ ^ cost(x) ≤ 1`. -/
theorem sum_two_inv_pow_cost_le_one (t : CompTree n α) {A : Finset (Fin n → β)}
    (hA : Set.InjOn t.eval (A : Set (Fin n → β))) : ∑ x ∈ A, (2⁻¹ : ℝ) ^ t.cost x ≤ 1 := by
  induction t generalizing A with
  | leaf a =>
    simp only [cost_leaf, pow_zero, sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast card_le_one.2 fun x hx y hy ↦ hA hx hy (by simp)
  | node i j l r ihl ihr =>
    -- The inputs with `x i < x j` continue in `l`, the others in `r`, each with weight halved.
    have hl := ihl (A := {x ∈ A | x i < x j}) fun x hx y hy hxy ↦
      hA (mem_filter.1 hx).1 (mem_filter.1 hy).1 (by
        simp [(mem_filter.1 hx).2, (mem_filter.1 hy).2, hxy])
    have hr := ihr (A := {x ∈ A | ¬x i < x j}) fun x hx y hy hxy ↦
      hA (mem_filter.1 hx).1 (mem_filter.1 hy).1 (by
        simp [(mem_filter.1 hx).2, (mem_filter.1 hy).2, hxy])
    rw [← sum_filter_add_sum_filter_not A fun x ↦ x i < x j]
    have hl' : ∑ x ∈ A with x i < x j, (2⁻¹ : ℝ) ^ (node i j l r).cost x =
        2⁻¹ * ∑ x ∈ A with x i < x j, (2⁻¹ : ℝ) ^ l.cost x := by
      rw [mul_sum]
      exact sum_congr rfl fun x hx ↦ by
        simp only [cost_node, (mem_filter.1 hx).2, ↓reduceIte, pow_succ']
    have hr' : ∑ x ∈ A with ¬x i < x j, (2⁻¹ : ℝ) ^ (node i j l r).cost x =
        2⁻¹ * ∑ x ∈ A with ¬x i < x j, (2⁻¹ : ℝ) ^ r.cost x := by
      rw [mul_sum]
      exact sum_congr rfl fun x hx ↦ by
        simp only [cost_node, (mem_filter.1 hx).2, ↓reduceIte, pow_succ']
    rw [hl', hr']
    linarith

/-- If a comparison tree gives pairwise different outputs on a nonempty finite set `A` of inputs,
then some input of `A` costs at least `⌈log₂ |A|⌉` comparisons. -/
theorem exists_clog_card_le_cost (t : CompTree n α) {A : Finset (Fin n → β)}
    (hA : Set.InjOn t.eval (A : Set (Fin n → β))) (hne : A.Nonempty) :
    ∃ x ∈ A, Nat.clog 2 #A ≤ t.cost x := by
  obtain ⟨x, hx, hmax⟩ := A.exists_mem_eq_sup hne t.cost
  refine ⟨x, hx, Nat.clog_le_of_le_pow ?_⟩
  rw [← hmax]
  -- Every term of Kraft's sum is at least `2⁻¹ ^ m`, where `m` is the largest cost.
  have hle : (#A : ℝ) * (2⁻¹ : ℝ) ^ A.sup t.cost ≤ 1 := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact (sum_le_sum fun y hy ↦ pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (le_sup hy)).trans (sum_two_inv_pow_cost_le_one t hA)
  have hpos : (0 : ℝ) < 2 ^ A.sup t.cost := by positivity
  rw [inv_pow, ← div_eq_mul_inv, div_le_one hpos] at hle
  exact_mod_cast hle

/-- If a comparison tree gives pairwise different outputs on a finite set `A` of inputs, then the
total cost over `A` is at least `|A| log₂ |A|`. -/
theorem card_mul_logb_card_le_sum_cost (t : CompTree n α) {A : Finset (Fin n → β)}
    (hA : Set.InjOn t.eval (A : Set (Fin n → β))) :
    (#A : ℝ) * Real.logb 2 #A ≤ ∑ x ∈ A, (t.cost x : ℝ) := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  have hc : (0 : ℝ) < #A := by exact_mod_cast hne.card_pos
  -- Jensen's inequality for the logarithm with the equal weights `1 / |A|`.
  have hJ := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := A) (w := fun _ ↦ (#A : ℝ)⁻¹)
    (p := fun x ↦ (2⁻¹ : ℝ) ^ t.cost x) (fun _ _ ↦ by positivity) (by simp [hc.ne'])
    fun _ _ ↦ Set.mem_Ioi.2 (by positivity)
  have hL : ∑ x ∈ A, (#A : ℝ)⁻¹ • Real.log ((2⁻¹ : ℝ) ^ t.cost x) =
      (#A : ℝ)⁻¹ * (-Real.log 2 * ∑ x ∈ A, (t.cost x : ℝ)) := by
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun x _ ↦ by rw [smul_eq_mul, Real.log_pow, Real.log_inv]; ring
  rw [hL, ← smul_sum, smul_eq_mul] at hJ
  have hR := Real.log_le_log (mul_pos (inv_pos.2 hc) (sum_pos (fun _ _ ↦ by positivity) hne))
    (mul_le_of_le_one_right (inv_nonneg.2 hc.le) (sum_two_inv_pow_cost_le_one t hA))
  rw [Real.log_inv] at hR
  have h := (hJ.trans hR)
  rw [inv_mul_le_iff₀ hc] at h
  rw [Real.logb, ← mul_div_assoc, div_le_iff₀ (Real.log_pos one_lt_two)]
  linarith

end CompTree

end TauCeti
