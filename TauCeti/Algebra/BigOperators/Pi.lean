/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite products and sums against `Pi.single`

A product `∏ j, f j ^ e j` whose exponent vector `e` is `Pi.single i a` is the single power
`f i ^ a`. For exponent vectors `α : ι → ℕ` over a finite type, this file records how the total
degree `∑ j, α j` controls the decomposition of `α` into unit vectors `Pi.single i 1`, and proves
an induction principle over the exponent vectors of a fixed degree `d`: starting from the pure
power `Pi.single i d`, every such vector is reached by moving one unit at a time from the
coordinate `i` to another coordinate.

## Main results

* `Fintype.prod_pow_pi_single`: `∏ j, f j ^ Pi.single i a j = f i ^ a`.
* `Pi.exists_eq_add_single_one`: an exponent vector with a positive `i`-th entry is `γ + e_i`.
* `Pi.eq_single_of_apply_eq_sum`: an exponent vector of degree `d` with `i`-th entry `d` is
  `Pi.single i d`.
* `Fintype.exists_ne_pos_of_apply_lt_sum`: an exponent vector whose `i`-th entry is less than its
  degree has another positive entry.
* `Pi.induction_on_single_of_sum_eq`: induction over the exponent vectors of degree `d`, starting
  from `Pi.single i d` and moving one unit at a time from the coordinate `i` to another coordinate.
-/

public section

open Finset

variable {ι : Type*}

/-- The monomial with exponent vector `Pi.single i a` is the power `f i ^ a`. -/
theorem Fintype.prod_pow_pi_single [Fintype ι] [DecidableEq ι] {M : Type*} [CommMonoid M]
    (f : ι → M) (i : ι) (a : ℕ) : ∏ j, f j ^ Pi.single (M := fun _ ↦ ℕ) i a j = f i ^ a := by
  rw [prod_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp

/-- An exponent vector with a positive `i`-th entry is of the form `γ + e_i`. -/
theorem Pi.exists_eq_add_single_one [DecidableEq ι] {β : ι → ℕ} {i : ι} (h : 0 < β i) :
    ∃ γ : ι → ℕ, β = γ + Pi.single i 1 := by
  refine ⟨Function.update β i (β i - 1), funext fun k ↦ ?_⟩
  by_cases hk : k = i
  · subst hk; simp; omega
  · simp [hk]

/-- An exponent vector of degree `d` whose `i`-th entry is `d` is the pure power `d e_i`. -/
theorem Pi.eq_single_of_apply_eq_sum [Fintype ι] [DecidableEq ι] {α : ι → ℕ} {d : ℕ}
    (hα : ∑ j, α j = d) {i : ι} (hi : α i = d) : α = Pi.single i d := by
  have h0 : ∀ j ∈ univ.erase i, α j = 0 := by
    rw [← sum_eq_zero_iff, ← add_right_cancel_iff (a := α i), sum_erase_add _ _ (mem_univ i)]
    omega
  ext j
  by_cases hj : j = i
  · subst hj; simp [hi]
  · simp [hj, h0 j (mem_erase.mpr ⟨hj, mem_univ j⟩)]

/-- An exponent vector whose `i`-th entry is less than its degree has another positive entry. -/
theorem Fintype.exists_ne_pos_of_apply_lt_sum [Fintype ι] {α : ι → ℕ} {i : ι}
    (hi : α i < ∑ j, α j) : ∃ j, j ≠ i ∧ 0 < α j := by
  classical
  by_contra! h
  have : ∑ j, α j = α i := by
    rw [← sum_erase_add _ _ (mem_univ i), sum_eq_zero fun j hj ↦
      Nat.le_zero.mp (h j (ne_of_mem_erase hj)), zero_add]
  omega

/-- Induction over the exponent vectors of degree `d`, starting from the pure power `d e_i` and
moving one unit at a time from the coordinate `i` to another coordinate `j`: a property of `d e_i`
which transfers from `β + e_i` to `β + e_j` holds for every exponent vector of degree `d`. -/
theorem Pi.induction_on_single_of_sum_eq [Fintype ι] [DecidableEq ι] {d : ℕ} (i : ι)
    {P : (ι → ℕ) → Prop}
    (hsingle : P (Pi.single i d))
    (step : ∀ (β : ι → ℕ) (j : ι), j ≠ i → ∑ k, β k + 1 = d →
      P (β + Pi.single i 1) → P (β + Pi.single j 1))
    {α : ι → ℕ} (hα : ∑ j, α j = d) : P α := by
  induction hm : d - α i generalizing α with
  | zero =>
    have hi : α i ≤ d := hα ▸ single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
    rwa [Pi.eq_single_of_apply_eq_sum (i := i) hα (by omega)]
  | succ m ih =>
    obtain ⟨j, hji, hj⟩ := Fintype.exists_ne_pos_of_apply_lt_sum (α := α) (i := i) (by omega)
    obtain ⟨β, rfl⟩ := Pi.exists_eq_add_single_one hj
    simp only [Pi.add_apply, sum_add_distrib, Fintype.sum_pi_single'] at hα
    refine step β j hji hα (ih (by simp [sum_add_distrib, hα]) ?_)
    simp [hji.symm] at hm ⊢
    omega
