/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Maximal coupling transition kernels on finite types

Given two probability distributions `q` and `p` on a finite state space `κ` with values in a
linearly ordered field `𝕜`, Doeblin's maximal coupling constructs a Markov transition kernel
`M : κ → κ → 𝕜` pushing `q` forward to `p` (`∑ c₀, q c₀ * M c₀ c = p c`) whose stay-put mass at
every state `c₀` is at least the overlap `min (q c₀) (p c₀)`. Summing over `c₀` shows that the
total probability of staying put is at least `∑ c₀, min (q c₀) (p c₀)`, attaining the total
variation bound `1 - (1 / 2) ∑ c, |q c - p c|`.

## Main results

* `TauCeti.exists_coupling_kernel`: existence of a Markov transition kernel pushing `q` forward to
  `p` with `min (q c₀) (p c₀) ≤ q c₀ * M c₀ c₀` for every `c₀ : κ`.

## References

* T. Lindvall, *Lectures on the Coupling Method*, Dover (2002), Chapter I, Theorem 5.2 (maximal
  coupling of discrete distributions).
-/

public section

open Finset

namespace TauCeti

/-- **Maximal coupling kernel.** Given probability distributions `q` and `p` on a finite type `κ`
taking values in a linearly ordered field `𝕜`, there is a Markov transition kernel `M : κ → κ → 𝕜`
pushing `q` forward to `p` whose stay-put mass at every state `c₀` is at least
`min (q c₀) (p c₀)`. -/
theorem exists_coupling_kernel {κ 𝕜 : Type*} [Fintype κ] [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {q p : κ → 𝕜}
    (hq : ∀ c, 0 ≤ q c) (hq1 : ∑ c, q c = 1) (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) :
    ∃ M : κ → κ → 𝕜, (∀ c₀ c, 0 ≤ M c₀ c) ∧ (∀ c₀, ∑ c, M c₀ c = 1) ∧
      (∀ c, ∑ c₀, q c₀ * M c₀ c = p c) ∧ ∀ c₀, min (q c₀) (p c₀) ≤ q c₀ * M c₀ c₀ := by
  classical
  let m : κ → 𝕜 := fun c ↦ min (q c) (p c)
  set s : 𝕜 := ∑ c, (p c - m c) with hs_def
  have hqm (c : κ) : 0 ≤ q c - m c := sub_nonneg.2 (min_le_left _ _)
  have hpm (c : κ) : 0 ≤ p c - m c := sub_nonneg.2 (min_le_right _ _)
  have hsq : ∑ c, (q c - m c) = s := by simp only [hs_def, sum_sub_distrib, hp1, hq1]
  have hs₀ : 0 ≤ s := sum_nonneg fun c _ ↦ hpm c
  have hrem (c₀ c : κ) : 0 ≤ if s = 0 then (0 : 𝕜) else (q c₀ - m c₀) * (p c - m c) / s := by
    split_ifs; exacts [le_rfl, div_nonneg (mul_nonneg (hqm c₀) (hpm c)) hs₀]
  -- Combine the stay-put overlap `m c₀` on the diagonal with the product of the excesses `q - m`
  -- and `p - m` normalized by `s`.
  let num (c₀ c : κ) : 𝕜 :=
    (if c = c₀ then m c₀ else 0) + if s = 0 then 0 else (q c₀ - m c₀) * (p c - m c) / s
  let M (c₀ c : κ) : 𝕜 := if q c₀ = 0 then p c else num c₀ c / q c₀
  have hmul (c₀ c : κ) : q c₀ * M c₀ c = num c₀ c := by
    dsimp only [M]; split_ifs with hq0
    · have hm0 : m c₀ = 0 := le_antisymm ((min_le_left _ _).trans_eq hq0) (le_min (hq c₀) (hp c₀))
      simp [num, hq0, hm0]
    · exact mul_div_cancel₀ _ hq0
  refine ⟨M, fun c₀ c ↦ ?_, fun c₀ ↦ ?_, fun c ↦ ?_, fun c₀ ↦ ?_⟩
  · dsimp only [M]; split_ifs
    · exact hp c
    · refine div_nonneg (add_nonneg ?_ (hrem c₀ c)) (hq c₀)
      split_ifs; exacts [le_min (hq c₀) (hp c₀), le_rfl]
  · dsimp only [M]; split_ifs with hq0
    · exact hp1
    · rw [← sum_div, div_eq_one_iff_eq hq0]
      simp only [num, sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte]
      split_ifs with hs0
      · rw [sum_const_zero]
        linarith [(sum_eq_zero_iff_of_nonneg fun c _ ↦ hqm c).1 (hsq.trans hs0) c₀ (mem_univ _)]
      · simp_rw [mul_div_assoc, ← mul_sum, ← sum_div]
        rw [← hs_def, div_self hs0]; ring
  · simp_rw [hmul, num]
    simp only [sum_add_distrib, sum_ite_eq, mem_univ, ↓reduceIte]
    split_ifs with hs0
    · rw [sum_const_zero]
      linarith [(sum_eq_zero_iff_of_nonneg fun c _ ↦ hpm c).1 hs0 c (mem_univ _)]
    · simp_rw [mul_div_assoc]
      rw [← sum_mul, hsq, mul_comm s, div_mul_cancel₀ _ hs0]; ring
  · rw [hmul]; dsimp only [num]; rw [ite_eq_left rfl]; linarith [hrem c₀ c₀]

end TauCeti
