/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Order.BigOperators.Sum.PosPart

/-!
# Maximal-coupling transition matrices on finite state spaces

Given two probability distributions `p` and `q` on a finite state space `κ` taking values in a
linearly ordered field `R`, the maximal coupling keeps as much mass on the diagonal as possible—
`min (p a) (q a)` at each state `a`—and redistributes the excess `max (p a - q a) 0` across states
proportionally to their deficits `max (q c - p c) 0`. Dividing each row by `p a` (or assigning the
row `q` when `p a = 0`) produces a row-stochastic transition matrix `M : κ → κ → R` pushing `p`
forward to `q` whose total off-diagonal mass `∑ a, p a * (1 - M a a)` equals the total variation
distance `(1 / 2) * ∑ a, |p a - q a|`.

## Main results

* `TauCeti.exists_transition_coupling`: existence of a maximal-coupling Markov transition matrix
  between any two finite probability distributions over a linearly ordered field.

## References

* T. Lindvall, *Lectures on the Coupling Method*, Wiley (1992), §I.2 (maximal coupling of discrete
  distributions).
-/

public section

open Finset

namespace TauCeti

variable {κ R : Type*} [Fintype κ] [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Maximal-coupling transition kernel.** For any two probability distributions `p` and `q` on a
finite type `κ` with values in a linearly ordered field `R`, there is a Markov transition matrix
`M : κ → κ → R` pushing `p` forward to `q` whose diagonal mass at each `a` satisfies
`p a * M a a = min (p a) (q a)`, so that the total off-diagonal mass `∑ a, p a * (1 - M a a)`
equals the total variation distance `(1 / 2) * ∑ a, |p a - q a|`. -/
theorem exists_transition_coupling {p q : κ → R} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    (hq : ∀ c, 0 ≤ q c) (hq1 : ∑ c, q c = 1) :
    ∃ M : κ → κ → R,
      (∀ a c, 0 ≤ M a c) ∧
      (∀ a, ∑ c, M a c = 1) ∧
      (∀ c, ∑ a, p a * M a c = q c) ∧
      (∀ a, p a * M a a = min (p a) (q a)) ∧
      ∑ a, p a * (1 - M a a) = (1 / 2) * ∑ a, |p a - q a| := by
  classical
  let ex : κ → R := fun a ↦ max (p a - q a) 0
  let df : κ → R := fun c ↦ max (q c - p c) 0
  have hex₀ (a : κ) : 0 ≤ ex a := le_max_right _ _
  have hdf₀ (c : κ) : 0 ≤ df c := le_max_right _ _
  have hbal : ∑ a, (p a - q a) = 0 := by rw [sum_sub_distrib, hp1, hq1, sub_self]
  have hmin_ex (a : κ) : min (p a) (q a) + ex a = p a := by
    have hmax : ex a = max (p a) (q a) - q a := by
      simpa only [ex, sub_self] using max_sub_sub_right (p a) (q a) (q a)
    linarith [min_add_max (p a) (q a)]
  have hmin_df (c : κ) : min (p c) (q c) + df c = q c := by
    have hmax : df c = max (q c) (p c) - p c := by
      simpa only [df, sub_self] using max_sub_sub_right (q c) (p c) (p c)
    linarith [min_add_max (q c) (p c), min_comm (p c) (q c)]
  have hsum_eq : ∑ a, ex a = ∑ c, df c := by
    simpa only [ex, df, neg_sub] using (sum_max_neg_eq_sum_max univ (fun a ↦ p a - q a) hbal).symm
  set tv := ∑ a, ex a with htv_def
  have htv_abs : 2 * tv = ∑ a, |p a - q a| := by
    simpa only [tv, ex, nsmul_eq_mul, Nat.cast_ofNat] using
      two_nsmul_sum_max_eq_sum_abs univ (fun a ↦ p a - q a) hbal
  -- When `tv = 0`, `p = q` everywhere; otherwise redistribute excess proportionally to deficit.
  by_cases htv : tv = 0
  · have hpq (a : κ) : p a = q a := by
      have hex_zero : ex a = 0 :=
        le_antisymm ((single_le_sum (fun b _ ↦ hex₀ b) (mem_univ a)).trans_eq htv) (hex₀ a)
      have hdf_zero : df a = 0 :=
        le_antisymm ((single_le_sum (fun b _ ↦ hdf₀ b) (mem_univ a)).trans_eq
          (hsum_eq.symm.trans htv)) (hdf₀ a)
      linarith [hmin_ex a, hmin_df a]
    refine ⟨fun a c ↦ if c = a then 1 else 0, fun a c ↦ by dsimp only; split_ifs <;> norm_num,
      fun a ↦ by simp, fun c ↦ by simp [hpq], fun a ↦ by simp [hpq], ?_⟩
    have habs : ∑ a, |p a - q a| = 0 := by linarith
    simp [habs]
  · have : 0 < tv := (sum_nonneg fun a _ ↦ hex₀ a).lt_of_ne' htv
    let M : κ → κ → R := fun a c ↦
      if p a = 0 then q c
      else (if c = a then min (p a) (q a) else 0) / p a + ex a / p a * (df c / tv)
    have hM_nonneg (a c : κ) : 0 ≤ M a c := by
      dsimp only [M]
      split_ifs with hpa hca
      · exact hq c
      · have hpa' : 0 < p a := (hp a).lt_of_ne' hpa
        have hmin : 0 ≤ min (p a) (q a) := le_min (hp a) (hq a)
        positivity
      · have hpa' : 0 < p a := (hp a).lt_of_ne' hpa
        positivity
    have hM_sum (a : κ) : ∑ c, M a c = 1 := by
      dsimp only [M]
      by_cases hpa : p a = 0
      · simp [hpa, hq1]
      · simp only [hpa, ↓reduceIte, sum_add_distrib, ← sum_div, ← mul_sum]
        rw [Fintype.sum_ite_eq' a fun _ ↦ min (p a) (q a), ← hsum_eq,
          div_self htv, mul_one, ← add_div, hmin_ex a, div_self hpa]
    -- Whether `p a = 0` or `p a > 0`, `p a * M a c` takes the same form.
    have hpM (a c : κ) :
        p a * M a c = (if c = a then min (p c) (q c) else 0) + ex a * (df c / tv) := by
      dsimp only [M]
      by_cases hpa : p a = 0
      · have hex_a : ex a = 0 := max_eq_right (by linarith [hq a])
        split_ifs with hca
        · subst hca; simp [hpa, hex_a, hq c]
        · simp [hpa, hex_a]
      · simp only [hpa, ↓reduceIte]
        have : p a * ((if c = a then min (p a) (q a) else 0) / p a + ex a / p a * (df c / tv)) =
            (if c = a then min (p a) (q a) else 0) + ex a * (df c / tv) := by
          field_simp [hpa]
        rw [this]
        split_ifs with hca
        · subst hca; rfl
        · rfl
    have hM_marg (c : κ) : ∑ a, p a * M a c = q c := by
      simp_rw [hpM]
      rw [sum_add_distrib, Fintype.sum_ite_eq c fun _ ↦ min (p c) (q c), ← sum_mul, ← htv_def,
        mul_div_cancel₀ _ htv, hmin_df c]
    have hM_diag (a : κ) : p a * M a a = min (p a) (q a) := by
      simp only [hpM, ↓reduceIte]
      have hzero : ex a * df a = 0 := by
        rcases le_total (p a) (q a) with h | h
        · simp [ex, max_eq_right (sub_nonpos.2 h)]
        · simp [df, max_eq_right (sub_nonpos.2 h)]
      calc min (p a) (q a) + ex a * (df a / tv)
          = min (p a) (q a) + ex a * df a / tv := by ring
        _ = min (p a) (q a) := by rw [hzero, zero_div, add_zero]
    refine ⟨M, hM_nonneg, hM_sum, hM_marg, hM_diag, ?_⟩
    have hterm (a : κ) : p a * (1 - M a a) = ex a := by
      calc p a * (1 - M a a) = p a - p a * M a a := by ring
        _ = p a - min (p a) (q a) := by rw [hM_diag]
        _ = ex a := by linarith [hmin_ex a]
    simp_rw [hterm]
    linarith

end TauCeti
