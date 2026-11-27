/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Finset.Floor
public import TauCeti.NumberTheory.CircleMethod.AdditiveCharacter

/-!
# Exponential sums over the integers of a real interval

For a real phase `f : ℝ → ℝ` and real endpoints `a`, `b`, the *interval exponential sum*

  `S_f[a, b] = ∑_{n ∈ ℤ, a ≤ n ≤ b} e(f(n))`,  `e(x) = exp(2πix)`,

is `TauCeti.intervalExpSum f a b`, the finite sum of `TauCeti.expTwoPiI (f n)` over
`Finset.Icc ⌈a⌉ ⌊b⌋`. This is the sum that explicit van der Corput type inequalities bound,
and through which integer points near a smooth curve are counted. The endpoints are real
because those arguments shorten the interval by real amounts, and a half-open sum
`∑_{X < n ≤ X + Y}` is the case `a = ⌊X⌋ + 1`, `b = X + Y`
(`TauCeti.intervalExpSum_intCast_add_one`).

## Main results

* `TauCeti.intervalExpSum_eq_zero`: the sum vanishes when `[a, b]` contains no integer, in
  particular when `b < a` (`TauCeti.intervalExpSum_eq_zero_of_lt`).
* `TauCeti.intervalExpSum_add_const`, `TauCeti.intervalExpSum_add_of_forall_intCast`,
  `TauCeti.intervalExpSum_add_intCast_mul`, `TauCeti.intervalExpSum_neg`: adding a real constant
  to the phase multiplies the sum by `e(c)`, adding a function that is integral at the integers
  (such as `k x` with `k ∈ ℤ`) changes nothing, and negating the phase conjugates the sum.
* `TauCeti.intervalExpSum_add_adjacent`: `S_f[a, c] + S_f[c + 1, b] = S_f[a, b]` for an integer
  `c` with `a ≤ c + 1` and `c ≤ b`.
* `TauCeti.norm_intervalExpSum_le_toNat` and `TauCeti.norm_intervalExpSum_le`: the trivial
  bounds `‖S_f[a, b]‖ ≤ (⌊b⌋ + 1 - ⌈a⌉).toNat` (the number of integers in `[a, b]`) and
  `‖S_f[a, b]‖ ≤ b - a + 1` for `a ≤ b + 1`.

## References

* J. Arias de Reyna, *Explicit van der Corput's d-th derivative estimate*, arXiv:2407.02094
  (2024), Lemma 6 and Theorem 7, which estimate the sums `∑_{X < n ≤ X + Y} e(f(n))`.
-/

public section

noncomputable section

open Finset

namespace TauCeti

/-- The exponential sum `S_f[a, b] = ∑_{n ∈ ℤ, a ≤ n ≤ b} e(f(n))` of a real phase `f` over the
integers of the real interval `[a, b]`, with `e(x) = exp(2πix)` (`TauCeti.expTwoPiI`). It is `0`
when `[a, b]` contains no integer. -/
def intervalExpSum (f : ℝ → ℝ) (a b : ℝ) : ℂ :=
  ∑ n ∈ Icc ⌈a⌉ ⌊b⌋, expTwoPiI (f n)

variable {f g : ℝ → ℝ} {a b : ℝ}

theorem intervalExpSum_def (f : ℝ → ℝ) (a b : ℝ) :
    intervalExpSum f a b = ∑ n ∈ Icc ⌈a⌉ ⌊b⌋, expTwoPiI (f n) := (rfl)

/-- At integer endpoints the sum runs over `Finset.Icc m k`. -/
@[simp]
theorem intervalExpSum_intCast (f : ℝ → ℝ) (m k : ℤ) :
    intervalExpSum f m k = ∑ n ∈ Icc m k, expTwoPiI (f n) := by
  simp [intervalExpSum_def]

/-- The sum only depends on the integer endpoints `⌈a⌉` and `⌊b⌋`. -/
theorem intervalExpSum_ceil_floor (f : ℝ → ℝ) (a b : ℝ) :
    intervalExpSum f ⌈a⌉ ⌊b⌋ = intervalExpSum f a b := by
  rw [intervalExpSum_intCast, intervalExpSum_def]

/-! ### Empty intervals -/

/-- If `[a, b]` contains no integer, the sum is `0`. -/
theorem intervalExpSum_eq_zero (h : ∀ n : ℤ, (n : ℝ) ∉ Set.Icc a b) :
    intervalExpSum f a b = 0 :=
  sum_eq_zero fun n hn ↦ (h n (Int.cast_mem_Icc_iff.2 hn)).elim

/-- An exponential sum over a reversed interval is `0`. -/
theorem intervalExpSum_eq_zero_of_lt (h : b < a) : intervalExpSum f a b = 0 :=
  intervalExpSum_eq_zero fun _ hn ↦ (h.trans_le hn.1).not_ge hn.2

/-! ### Changing the phase -/

/-- Two phases agreeing at the integers of `[a, b]` have the same exponential sum there. -/
theorem intervalExpSum_congr (h : ∀ n : ℤ, (n : ℝ) ∈ Set.Icc a b → f n = g n) :
    intervalExpSum f a b = intervalExpSum g a b :=
  sum_congr rfl fun n hn ↦ by rw [h n (Int.cast_mem_Icc_iff.2 hn)]

/-- Adding a real constant `c` to the phase multiplies the sum by the unit `e(c)`. -/
theorem intervalExpSum_add_const (f : ℝ → ℝ) (c a b : ℝ) :
    intervalExpSum (fun x ↦ f x + c) a b = expTwoPiI c * intervalExpSum f a b := by
  simp_rw [intervalExpSum_def, expTwoPiI_add, mul_sum, mul_comm]

@[simp]
theorem norm_intervalExpSum_add_const (f : ℝ → ℝ) (c a b : ℝ) :
    ‖intervalExpSum (fun x ↦ f x + c) a b‖ = ‖intervalExpSum f a b‖ := by
  rw [intervalExpSum_add_const, norm_mul, norm_expTwoPiI, one_mul]

/-- Adding to the phase a function `g` that takes integer values at the integers of `[a, b]`
does not change the sum. -/
theorem intervalExpSum_add_of_forall_intCast
    (hg : ∀ n : ℤ, (n : ℝ) ∈ Set.Icc a b → ∃ m : ℤ, g n = m) :
    intervalExpSum (fun x ↦ f x + g x) a b = intervalExpSum f a b :=
  sum_congr rfl fun n hn ↦ by
    obtain ⟨m, hm⟩ := hg n (Int.cast_mem_Icc_iff.2 hn)
    simp only [hm, expTwoPiI_add_intCast]

/-- Adding an integer multiple `k x` of the identity to the phase does not change the sum: the
exponential sum only sees the phase modulo `1` at the integers. -/
@[simp]
theorem intervalExpSum_add_intCast_mul (f : ℝ → ℝ) (k : ℤ) (a b : ℝ) :
    intervalExpSum (fun x ↦ f x + k * x) a b = intervalExpSum f a b :=
  intervalExpSum_add_of_forall_intCast fun n _ ↦ ⟨k * n, by push_cast; ring⟩

/-- Negating the phase conjugates the sum. -/
theorem intervalExpSum_neg (f : ℝ → ℝ) (a b : ℝ) :
    intervalExpSum (-f) a b = starRingEnd ℂ (intervalExpSum f a b) := by
  simp [intervalExpSum_def, map_sum]

@[simp]
theorem norm_intervalExpSum_neg (f : ℝ → ℝ) (a b : ℝ) :
    ‖intervalExpSum (-f) a b‖ = ‖intervalExpSum f a b‖ := by
  rw [intervalExpSum_neg, Complex.norm_conj]

/-- Composing the phase with a translation by an integer `m` translates the interval by `m`. -/
theorem intervalExpSum_comp_add_intCast (f : ℝ → ℝ) (m : ℤ) (a b : ℝ) :
    intervalExpSum (fun x ↦ f (x + m)) a b = intervalExpSum f (a + m) (b + m) := by
  rw [intervalExpSum_def, intervalExpSum_def, Int.ceil_add_intCast, Int.floor_add_intCast,
    ← map_add_right_Icc, sum_map]
  simp

/-- The sum of a constant phase `c` is `e(c)` times the number of integers in `[a, b]`. -/
theorem intervalExpSum_const (c a b : ℝ) :
    intervalExpSum (fun _ ↦ c) a b = (⌊b⌋ + 1 - ⌈a⌉).toNat * expTwoPiI c := by
  rw [intervalExpSum_def, sum_const, Int.card_Icc, nsmul_eq_mul]

/-! ### Splitting the interval -/

/-- **Additivity in the interval.** For an integer `c` with `a ≤ c + 1` and `c ≤ b`,
`S_f[a, c] + S_f[c + 1, b] = S_f[a, b]`. In particular this holds for every integer
`a ≤ c < b`. -/
theorem intervalExpSum_add_adjacent (f : ℝ → ℝ) {c : ℤ} (hac : a ≤ c + 1) (hcb : c ≤ b) :
    intervalExpSum f a c + intervalExpSum f (c + 1) b = intervalExpSum f a b := by
  have h₁ : ⌈a⌉ ≤ c + 1 := Int.ceil_le.2 (by exact_mod_cast hac)
  have h₂ : c + 1 ≤ ⌊b⌋ + 1 := by
    have := Int.le_floor.2 hcb
    omega
  simp only [intervalExpSum_def, Int.ceil_add_one, Int.ceil_intCast, Int.floor_intCast,
    ← Ico_add_one_right_eq_Icc]
  rw [← sum_union (Ico_disjoint_Ico_consecutive _ _ _), Ico_union_Ico_eq_Ico h₁ h₂]

/-- **Half-open intervals.** For an integer `m`, `S_f[m + 1, b]` is the sum of `e(f(n))` over
the integers `m < n ≤ b`, which are the elements of `Finset.Ioc m ⌊b⌋`. With `m = ⌊X⌋` these
are the integers `X < n ≤ b` (`Int.floor_lt`), so for `b = X + Y` this is
`∑_{X < n ≤ X + Y} e(f(n))`. -/
theorem intervalExpSum_intCast_add_one (f : ℝ → ℝ) (m : ℤ) (b : ℝ) :
    intervalExpSum f (m + 1) b = ∑ n ∈ Ioc m ⌊b⌋, expTwoPiI (f n) := by
  rw [intervalExpSum_def, Int.ceil_add_one, Int.ceil_intCast, Icc_add_one_left_eq_Ioc]

/-! ### Trivial bounds -/

/-- The trivial bound: `‖S_f[a, b]‖` is at most the number `⌊b⌋ + 1 - ⌈a⌉` (or `0`) of integers
in `[a, b]`. -/
theorem norm_intervalExpSum_le_toNat (f : ℝ → ℝ) (a b : ℝ) :
    ‖intervalExpSum f a b‖ ≤ (⌊b⌋ + 1 - ⌈a⌉).toNat := by
  rw [intervalExpSum_def, ← Int.card_Icc]
  exact (norm_sum_le _ _).trans (by simp)

/-- The trivial bound `‖S_f[a, b]‖ ≤ b - a + 1`, for `a ≤ b + 1`. -/
theorem norm_intervalExpSum_le (f : ℝ → ℝ) (hab : a ≤ b + 1) :
    ‖intervalExpSum f a b‖ ≤ b - a + 1 := by
  refine (norm_intervalExpSum_le_toNat f a b).trans ?_
  have hcast : ((⌊b⌋ + 1 - ⌈a⌉).toNat : ℝ) = max ((⌊b⌋ : ℝ) + 1 - ⌈a⌉) 0 := by
    exact_mod_cast Int.toNat_eq_max (⌊b⌋ + 1 - ⌈a⌉)
  rw [hcast]
  exact max_le (by linarith [Int.floor_le b, Int.le_ceil a]) (by linarith)

/-! ### Checks -/

/-- The phase `0` on `[0, 2]` counts the three integers `0, 1, 2`. -/
example : intervalExpSum (fun _ ↦ 0) 0 2 = 3 := by
  rw [intervalExpSum_const]
  norm_num

/-- `[0.2, 0.8]` contains no integer, so the sum vanishes; a sum indexed by the length of the
real interval would not. -/
example : intervalExpSum f 0.2 0.8 = 0 := by
  refine intervalExpSum_eq_zero fun n hn ↦ ?_
  have h₁ : (0 : ℝ) < n := by linarith [hn.1]
  have h₂ : (n : ℝ) < 1 := by linarith [hn.2]
  norm_cast at h₁ h₂
  omega

/-- Integer slopes are invisible: the phase `x` on `[0, 2]` gives the same sum as the phase `0`. -/
example : intervalExpSum (fun x ↦ x) 0 2 = 3 := by
  have := intervalExpSum_add_intCast_mul (fun _ ↦ 0) 1 0 2
  simp only [Int.cast_one, one_mul, zero_add] at this
  rw [this, intervalExpSum_const]
  norm_num

/-- The phase `x / 2` on `[0, 2]` gives `e(0) + e(1/2) + e(1) = 1 - 1 + 1`, which pins the
normalisation `e(1/2) = -1` of `e(x) = exp(2πix)`. -/
example : intervalExpSum (fun x ↦ x / 2) 0 2 = 1 := by
  have h : expTwoPiI 2⁻¹ = -1 := by
    rw [expTwoPiI_def, ← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring
  have hI : Icc (0 : ℤ) 2 = {0, 1, 2} := by decide
  rw [← Int.cast_zero, ← Int.cast_two, intervalExpSum_intCast, hI]
  simp [h]

/-- The half-open sum over `0.5 < n ≤ 2.5` is `S_f[1, 2.5]`, with the two terms `n = 1, 2`. -/
example : intervalExpSum f (⌊(0.5 : ℝ)⌋ + 1) 2.5 = expTwoPiI (f 1) + expTwoPiI (f 2) := by
  have h₁ : ⌊(0.5 : ℝ)⌋ = 0 := Int.floor_eq_iff.2 (by norm_num)
  have h₂ : ⌊(2.5 : ℝ)⌋ = 2 := Int.floor_eq_iff.2 (by norm_num)
  have hI : Ioc (0 : ℤ) 2 = {1, 2} := by decide
  rw [intervalExpSum_intCast_add_one, h₁, h₂, hI]
  simp

end TauCeti
