/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import TauCeti.Combinatorics.ComparisonTree.Complexity
public import TauCeti.Combinatorics.ComparisonTree.Counting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic.Linarith

/-!
# Lower bounds for comparison sorting

A comparison tree on `n` items with outputs in `Equiv.Perm (Fin n)` sorts when its output on
every ranking `σ` is `σ` itself, that is, when it solves the problem with all rankings admissible
and correctness relation `fun σ τ => τ = σ`. Such a tree gives `n!` pairwise different outputs on
the `n!` rankings, so the counting bounds for comparison trees apply: some ranking costs at least
`⌈log₂ n!⌉` comparisons, and the average cost over all rankings is at least `log₂ n!`. With the
logarithmic form of Stirling's lower bound for `n!`, both costs are at least
`n log₂ n - n / ln 2`.

The counting step holds for every problem in which an output is correct for at most one ranking,
on any finite set of admissible rankings; the sorting bounds are its case with all rankings.

## Main results

* `TauCeti.CompTree.Solves.injOn_eval`: a tree that solves a problem in which an output is correct
  for at most one ranking gives pairwise different outputs on the admissible rankings.
* `TauCeti.CompTree.Solves.exists_clog_card_le_cost`,
  `TauCeti.CompTree.Solves.card_mul_logb_card_le_sum_cost`: the counting bounds for such a
  problem on a finite set `A` of admissible rankings.
* `TauCeti.CompTree.exists_clog_factorial_le_cost`: a tree that sorts `n` items costs at least
  `⌈log₂ n!⌉` comparisons on some ranking.
* `TauCeti.CompTree.logb_factorial_le_average_cost`: the average cost of a tree that sorts `n`
  items is at least `log₂ n!`.
* `TauCeti.CompTree.exists_mul_logb_sub_div_log_le_cost`,
  `TauCeti.CompTree.mul_logb_sub_div_log_le_average_cost`: the bound `n log₂ n - n / ln 2` on some
  ranking and on average.

## References

* J. Erickson, *Algorithms*, lecture notes, Lecture 12, "Lower Bounds", §12.5 (revision of Fall
  2013).
* Lecture notes of the course 15-451, *Algorithms*, Carnegie Mellon University, Fall 2011,
  Lecture 5, "Comparison-based Lower Bounds for Sorting", Theorems 5.1 and 5.2.
-/

public section

open Finset

namespace TauCeti

namespace CompTree

variable {n : ℕ} {α : Type*} {t : CompTree n α} {R : Equiv.Perm (Fin n) → α → Prop}

/-- If a tree solves a problem in which an output is correct for at most one ranking, then it gives
pairwise different outputs on the admissible rankings. -/
theorem Solves.injOn_eval {A : Set (Equiv.Perm (Fin n))} (ht : t.Solves A R)
    (hR : ∀ σ τ a, R σ a → R τ a → σ = τ) :
    Set.InjOn (fun σ : Equiv.Perm (Fin n) => t.eval ⇑σ) A := by
  intro σ hσ τ hτ h
  dsimp only at h
  have hτ' := solves_iff.1 ht τ hτ
  rw [← h] at hτ'
  exact hR σ τ _ (solves_iff.1 ht σ hσ) hτ'

/-- If a tree solves a problem in which an output is correct for at most one ranking, then the
rankings of a finite set `A` of admissible rankings, seen as inputs, receive pairwise different
outputs. -/
private theorem Solves.injOn_eval_map {A : Finset (Equiv.Perm (Fin n))} (ht : t.Solves ↑A R)
    (hR : ∀ σ τ a, R σ a → R τ a → σ = τ) :
    Set.InjOn t.eval
      ((A.map ⟨fun σ : Equiv.Perm (Fin n) => ⇑σ, DFunLike.coe_injective⟩ :
        Finset (Fin n → Fin n)) : Set (Fin n → Fin n)) := by
  rw [coe_map]
  exact (ht.injOn_eval hR).image_of_comp

/-- If a tree solves a problem in which an output is correct for at most one ranking, then it
costs at least `⌈log₂ |A|⌉` comparisons on some ranking of a nonempty finite set `A` of admissible
rankings. -/
theorem Solves.exists_clog_card_le_cost {A : Finset (Equiv.Perm (Fin n))} (ht : t.Solves ↑A R)
    (hR : ∀ σ τ a, R σ a → R τ a → σ = τ) (hne : A.Nonempty) :
    ∃ σ ∈ A, Nat.clog 2 #A ≤ t.cost ⇑σ := by
  obtain ⟨x, hx, hcost⟩ := t.exists_clog_card_le_cost (ht.injOn_eval_map hR) hne.map
  obtain ⟨σ, hσ, rfl⟩ := mem_map.1 hx
  exact ⟨σ, hσ, by simpa using hcost⟩

/-- If a tree solves a problem in which an output is correct for at most one ranking, then its
total cost over a finite set `A` of admissible rankings is at least `|A| log₂ |A|`. -/
theorem Solves.card_mul_logb_card_le_sum_cost {A : Finset (Equiv.Perm (Fin n))}
    (ht : t.Solves ↑A R) (hR : ∀ σ τ a, R σ a → R τ a → σ = τ) :
    (#A : ℝ) * Real.logb 2 #A ≤ ∑ σ ∈ A, (t.cost ⇑σ : ℝ) := by
  simpa using t.card_mul_logb_card_le_sum_cost (ht.injOn_eval_map hR)

/-- **The lower bound for sorting.** A comparison tree that outputs the ranking of every input
makes at least `⌈log₂ n!⌉` comparisons on some input. -/
theorem exists_clog_factorial_le_cost (t : CompTree n (Equiv.Perm (Fin n)))
    (ht : t.Solves Set.univ fun σ τ => τ = σ) :
    ∃ σ : Equiv.Perm (Fin n), Nat.clog 2 n.factorial ≤ t.cost ⇑σ := by
  have ht' : t.Solves ↑(univ : Finset (Equiv.Perm (Fin n))) fun σ τ => τ = σ := by
    rwa [coe_univ]
  obtain ⟨σ, -, hσ⟩ :=
    ht'.exists_clog_card_le_cost (fun _ _ _ h h' => h.symm.trans h') univ_nonempty
  exact ⟨σ, by simpa [Fintype.card_perm] using hσ⟩

/-- **The average lower bound for sorting.** A comparison tree that outputs the ranking of every
input makes at least `log₂ n!` comparisons on average over the `n!` rankings. -/
theorem logb_factorial_le_average_cost (t : CompTree n (Equiv.Perm (Fin n)))
    (ht : t.Solves Set.univ fun σ τ => τ = σ) :
    Real.logb 2 n.factorial ≤
      (∑ σ : Equiv.Perm (Fin n), (t.cost ⇑σ : ℝ)) / n.factorial := by
  have ht' : t.Solves ↑(univ : Finset (Equiv.Perm (Fin n))) fun σ τ => τ = σ := by
    rwa [coe_univ]
  have h := ht'.card_mul_logb_card_le_sum_cost fun _ _ _ h h' => h.symm.trans h'
  simp only [card_univ, Fintype.card_perm, Fintype.card_fin] at h
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact h

/-- The average cost of a comparison tree that outputs the ranking of every input is at least
`n log₂ n - n / ln 2`. -/
theorem mul_logb_sub_div_log_le_average_cost (t : CompTree n (Equiv.Perm (Fin n)))
    (ht : t.Solves Set.univ fun σ τ => τ = σ) :
    n * Real.logb 2 n - n / Real.log 2 ≤
      (∑ σ : Equiv.Perm (Fin n), (t.cost ⇑σ : ℝ)) / n.factorial := by
  refine le_trans ?_ (t.logb_factorial_le_average_cost ht)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  -- Stirling's bound `n ln n - n + (ln n) / 2 + ln (2π) / 2 ≤ ln n!`, divided by `ln 2`.
  have hS := Stirling.le_log_factorial_stirling hn
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlogpi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.two_le_pi])
  rw [Real.logb, Real.logb, mul_div_assoc', div_sub_div_same]
  exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos one_lt_two).le

/-- A comparison tree that outputs the ranking of every input makes at least
`n log₂ n - n / ln 2` comparisons on some input. -/
theorem exists_mul_logb_sub_div_log_le_cost (t : CompTree n (Equiv.Perm (Fin n)))
    (ht : t.Solves Set.univ fun σ τ => τ = σ) :
    ∃ σ : Equiv.Perm (Fin n), n * Real.logb 2 n - n / Real.log 2 ≤ t.cost ⇑σ := by
  have h : ∑ _σ : Equiv.Perm (Fin n), (n * Real.logb 2 n - n / Real.log 2) ≤
      ∑ σ : Equiv.Perm (Fin n), (t.cost ⇑σ : ℝ) := by
    rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    exact (le_div_iff₀ (by positivity)).1 (t.mul_logb_sub_div_log_le_average_cost ht)
  obtain ⟨σ, -, hσ⟩ := exists_le_of_sum_le univ_nonempty h
  exact ⟨σ, hσ⟩

end CompTree

end TauCeti
