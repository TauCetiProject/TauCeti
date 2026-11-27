/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ExponentialSum.Interval
import Mathlib.Data.Rat.Floor
import TauCeti.Algebra.Order.Floor.Ring

/-!
# The near-integer count

The distance from a real number `x` to the nearest integer, `‖x‖ = |x - round x|`, is
`TauCeti.distInt x`, the norm of `x` in `UnitAddCircle` (`TauCeti.distInt_eq_norm`). For a real
phase `f : ℝ → ℝ` and real `a`, `N` and `δ`, the *near-integer count*

  `R(f, a, N, δ) = #{n ∈ ℤ | a ≤ n ≤ a + N, ‖f(n)‖ < δ}`

is `TauCeti.nearIntegerCount f a N δ`. It runs over the integers `Finset.Icc ⌈a⌉ ⌊a + N⌋` of the
exponential sum `TauCeti.intervalExpSum f a (a + N)`. For `δ ≤ 1/2` it is the number of integer
points `(n, m)` with `a ≤ n ≤ a + N` at vertical distance less than `δ` from the curve `y = f(x)`.

## Main results

* `TauCeti.nearIntegerCount_le`: `R(f, a, N, δ) ≤ N + 1` for `N ≥ -1`.
* `TauCeti.nearIntegerCount_mono` and `TauCeti.nearIntegerCount_le_of_le_of_add_le`: `R` is
  monotone in `δ` and in the interval.
* `TauCeti.nearIntegerCount_add_of_forall_intCast`, `TauCeti.nearIntegerCount_add_intCast` and
  `TauCeti.nearIntegerCount_neg`: `R` does not change when a function with integer values at the
  integers of the interval (such as an integer `k`) is added to `f`, or when `f` is negated.
* `TauCeti.nearIntegerCount_of_half_lt`: if `δ > 1/2`, then every integer of `[a, a + N]` is
  counted, because `‖x‖ ≤ 1/2`.
-/

public section

noncomputable section

open Finset

namespace TauCeti

/-- The near-integer count `R(f, a, N, δ)`: the number of integers `n` with `a ≤ n ≤ a + N` for
which `f(n)` is nearer than `δ` to an integer, `‖f(n)‖ < δ` (`TauCeti.distInt`). -/
def nearIntegerCount (f : ℝ → ℝ) (a N δ : ℝ) : ℕ :=
  #{n ∈ Icc ⌈a⌉ ⌊a + N⌋ | distInt (f (n : ℤ)) < δ}

variable {f g : ℝ → ℝ} {a N δ : ℝ}

theorem nearIntegerCount_def (f : ℝ → ℝ) (a N δ : ℝ) :
    nearIntegerCount f a N δ = #{n ∈ Icc ⌈a⌉ ⌊a + N⌋ | distInt (f (n : ℤ)) < δ} := (rfl)

/-- `R(f, a, N, δ) ≤ N + 1`, the bound by the number of integers in `[a, a + N]`, for
`N ≥ -1`. -/
theorem nearIntegerCount_le (f : ℝ → ℝ) (a δ : ℝ) (hN : -1 ≤ N) :
    (nearIntegerCount f a N δ : ℝ) ≤ N + 1 :=
  calc (nearIntegerCount f a N δ : ℝ) ≤ #(Icc ⌈a⌉ ⌊a + N⌋) := by
        rw [nearIntegerCount_def]
        exact_mod_cast card_filter_le _ _
    _ ≤ a + N - a + 1 := card_Icc_ceil_floor_le (by linarith)
    _ = N + 1 := by ring

/-- `R(f, a, N, δ)` is monotone in `δ`. -/
theorem nearIntegerCount_mono (f : ℝ → ℝ) (a N : ℝ) : Monotone (nearIntegerCount f a N) := by
  intro δ δ' h
  simp only [nearIntegerCount_def]
  exact card_le_card fun n hn ↦ by
    rw [mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.trans_le h⟩

/-- `R` is monotone in the interval: if `a ≤ a'` and `a' + N' ≤ a + N`, then
`R(f, a', N', δ) ≤ R(f, a, N, δ)`. -/
theorem nearIntegerCount_le_of_le_of_add_le (f : ℝ → ℝ) {a' N' : ℝ} (δ : ℝ) (ha : a ≤ a')
    (hN : a' + N' ≤ a + N) : nearIntegerCount f a' N' δ ≤ nearIntegerCount f a N δ :=
  card_le_card (filter_subset_filter _ (Icc_subset_Icc (Int.ceil_mono ha) (Int.floor_mono hN)))

/-- Adding to `f` a function `g` with integer values at the integers of `[a, a + N]` does not
change `R(f, a, N, δ)`. -/
theorem nearIntegerCount_add_of_forall_intCast
    (hg : ∀ n : ℤ, (n : ℝ) ∈ Set.Icc a (a + N) → ∃ m : ℤ, g n = m) (δ : ℝ) :
    nearIntegerCount (fun x ↦ f x + g x) a N δ = nearIntegerCount f a N δ := by
  simp only [nearIntegerCount_def]
  refine congr_arg card (filter_congr fun n hn ↦ ?_)
  obtain ⟨m, hm⟩ := hg n (Int.cast_mem_Icc_iff.2 hn)
  rw [hm, distInt_add_intCast]

/-- `R(f + k, a, N, δ) = R(f, a, N, δ)` for an integer `k`. -/
@[simp]
theorem nearIntegerCount_add_intCast (f : ℝ → ℝ) (k : ℤ) (a N δ : ℝ) :
    nearIntegerCount (fun x ↦ f x + k) a N δ = nearIntegerCount f a N δ :=
  nearIntegerCount_add_of_forall_intCast (fun _ _ ↦ ⟨k, rfl⟩) δ

/-- `R(-f, a, N, δ) = R(f, a, N, δ)`, since `‖-x‖ = ‖x‖`. -/
@[simp]
theorem nearIntegerCount_neg (f : ℝ → ℝ) (a N δ : ℝ) :
    nearIntegerCount (fun x ↦ -f x) a N δ = nearIntegerCount f a N δ := by
  simp only [nearIntegerCount_def, distInt_neg]

/-- If `δ > 1/2`, every integer of `[a, a + N]` is counted, since `‖x‖ ≤ 1/2`. -/
theorem nearIntegerCount_of_half_lt (f : ℝ → ℝ) (a N : ℝ) (hδ : 1 / 2 < δ) :
    nearIntegerCount f a N δ = (⌊a + N⌋ + 1 - ⌈a⌉).toNat := by
  rw [nearIntegerCount_def, filter_true_of_mem fun n _ ↦ (distInt_le_half _).trans_lt hδ,
    Int.card_Icc]

/-! ### Checks -/

/-- `‖2.3‖ = 0.3`. -/
example : distInt 2.3 = 0.3 := by
  norm_num [distInt_def]

/-- `‖-0.2‖ = 0.2`, where the fractional part would give `0.8`. -/
example : distInt (-0.2) = 0.2 := by
  norm_num [distInt_def]

/-- For `f(x) = x / 3` on `[0, 6]` with `δ = 0.1` the counted integers are `0`, `3` and `6`. -/
example : nearIntegerCount (fun x ↦ x / 3) 0 6 0.1 = 3 := by
  have h₁ : ⌈(0 : ℝ)⌉ = 0 := by norm_num
  have h₂ : ⌊(0 : ℝ) + 6⌋ = 6 := by norm_num
  have h₃ : Icc (0 : ℤ) 6 = {0, 1, 2, 3, 4, 5, 6} := by decide
  rw [nearIntegerCount_def, h₁, h₂, h₃]
  norm_num [filter_insert, filter_singleton, distInt_def]

/-- The count is strict: `‖1/3‖ = ‖2/3‖ = 1/3` is not counted for `δ = 1/3`. -/
example : nearIntegerCount (fun x ↦ x / 3) 1 1 (1 / 3) = 0 := by
  have h₁ : ⌈(1 : ℝ)⌉ = 1 := by norm_num
  have h₂ : ⌊(1 : ℝ) + 1⌋ = 2 := by norm_num
  have h₃ : Icc (1 : ℤ) 2 = {1, 2} := by decide
  rw [nearIntegerCount_def, h₁, h₂, h₃]
  norm_num [filter_insert, distInt_def]

/-- Length zero: `[3, 3]` contains the integer `3`, and `‖1‖ = 0 < 0.1`. -/
example : nearIntegerCount (fun x ↦ x / 3) 3 0 0.1 = 1 := by
  have h₁ : ⌈(3 : ℝ)⌉ = 3 := by norm_num
  have h₂ : ⌊(3 : ℝ) + 0⌋ = 3 := by norm_num
  rw [nearIntegerCount_def, h₁, h₂, Icc_self]
  norm_num [filter_singleton, distInt_def]

/-- Length zero: `[2.5, 2.5]` contains no integer. -/
example : nearIntegerCount (fun x ↦ x / 3) 2.5 0 0.5 = 0 := by
  have h₁ : ⌈(2.5 : ℝ)⌉ = 3 := by norm_num
  have h₂ : ⌊(2.5 : ℝ) + 0⌋ = 2 := by norm_num
  rw [nearIntegerCount_def, h₁, h₂, Icc_eq_empty (by norm_num), filter_empty, card_empty]

end TauCeti
