/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic
import TauCeti.Algebra.Order.Floor.Semifield

/-!
# A strict finite Sobolev exponent ladder in dimension two

For `p > 2`, the product exponent `r = p q / (p + q)` has two-dimensional Sobolev exponent
`2 r / (2 - r)` when `r < 2`. This file constructs a finite increasing sequence starting in
`(p / (p - 1), p]` and crossing `2 p / (p - 2)` strictly. Every product exponent is greater
than one; every step before the crossing is strictly below two, and the final product exponent
is strictly above two. Thus neither endpoint obstructs the successive Sobolev embeddings.

The construction uses reciprocals: each step subtracts `a = (p - 2) / (2 p)`. Choosing the
initial reciprocal at a half-integer multiple of `a` prevents landing on the critical exponent.
This is the exponent arithmetic for the order-zero regularity argument, not a regularity theorem.

## References

D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
Lemma B.4.4.
-/

public section

namespace TauCeti

/-- The initial exponent of the ladder lies in `(p / (p - 1), p]` when its reciprocal `b` lies
in `[1 / p, (p - 1) / p)`, with strict inequality at the left end. -/
private theorem ladder_initial_exponent {p b : ℝ} (hp : 2 < p)
    (hb1 : 1 / p < b) (hb2 : b < (p - 1) / p) : p / (p - 1) < 1 / b ∧ 1 / b ≤ p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hb0 : 0 < b := (one_div_pos.mpr hp0).trans hb1
  refine ⟨?_, ?_⟩
  · apply (div_lt_div_iff₀ hp1 hb0).2
    have h := (lt_div_iff₀ hp0).mp hb2
    nlinarith
  · apply (div_le_iff₀ hb0).2
    have h := (div_lt_iff₀ hp0).mp hb1
    linarith

/-- The product exponent of `p` and `1 / b` has reciprocal `1 / p + b`. -/
private theorem ladder_product_exponent {p b : ℝ} (hp : 0 < p) (hb : 0 < b) :
    p * (1 / b) / (p + 1 / b) = 1 / (1 / p + b) := by
  field_simp [hp.ne', hb.ne']
  ring

/-- One step of the ladder: if `b' = b - a` with `a = 1 / 2 - 1 / p`, the exponent `1 / b'` is
the two-dimensional Sobolev exponent of the product exponent of `p` and `1 / b`. -/
private theorem ladder_step_eq {p a b b' : ℝ} (hp : 0 < p) (hae : a = 1 / 2 - 1 / p)
    (hb : 0 < b) (hb' : 0 < b') (hbb : b' = b - a) (hr : p * (1 / b) / (p + 1 / b) < 2) :
    1 / b' = 2 * (p * (1 / b) / (p + 1 / b)) / (2 - p * (1 / b) / (p + 1 / b)) := by
  apply (eq_div_iff (sub_pos.mpr hr).ne').2
  rw [ladder_product_exponent hp hb]
  have hd : 1 / p + b ≠ 0 := (add_pos (one_div_pos.mpr hp) hb).ne'
  field_simp [hb'.ne', hd]
  rw [hbb, hae]
  have hd' : 1 + p * b ≠ 0 := (add_pos zero_lt_one (mul_pos hp hb)).ne'
  field_simp [hp.ne', hd']
  ring

/-- The last two ladder exponents straddle the critical exponent `2 p / (p - 2)`, and the last
product exponent exceeds two. Here `a = (p - 2) / (2 p)` and the last two reciprocals are
`3 a / 2` and `a / 2`. -/
private theorem ladder_final_exponents {p a : ℝ} (hp : 2 < p) (ha : a = (p - 2) / (2 * p)) :
    1 / (3 * a / 2) < 2 * p / (p - 2) ∧ 2 * p / (p - 2) < 1 / (a / 2) ∧
      2 < 1 / (1 / p + a / 2) := by
  have hp0 : 0 < p := by linarith
  have hapos : 0 < a := ha ▸ div_pos (by linarith) (by positivity)
  have hae : a = 1 / 2 - 1 / p := by
    rw [ha]
    field_simp
  have hthreshold : 2 * p / (p - 2) = 1 / a := by
    rw [ha]
    field_simp
  rw [hthreshold]
  refine ⟨one_div_lt_one_div_of_lt hapos (by linarith),
    one_div_lt_one_div_of_lt (by positivity) (by linarith), ?_⟩
  apply (lt_div_iff₀ (by positivity : 0 < 1 / p + a / 2)).2
  rw [hae]
  have h := (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) hp)
  linarith

/-- The reciprocal of the initial exponent lies strictly between `1 / p` and `(p - 1) / p`. -/
private theorem ladder_initial_reciprocal {p a : ℝ} {N : ℕ} (hp : p ≠ 0) (hae : a = 1 / 2 - 1 / p)
    (ha : 0 < a) (hNlow : 1 / p < N * a) (hNhigh : N * a ≤ 1 / p + a) :
    1 / p < ((N : ℝ) + 1 / 2) * a ∧ ((N : ℝ) + 1 / 2) * a < (p - 1) / p := by
  have hfrac : (p - 1) / p = 1 / p + 2 * a := by
    rw [hae]
    field_simp
    ring
  rw [hfrac]
  constructor <;> nlinarith

/-- A product exponent of `p` with an exponent above `p / (p - 1)` exceeds one. -/
private theorem one_lt_product_exponent {p q : ℝ} (hp : 2 < p) (hq0 : 0 < q)
    (hq : p / (p - 1) < q) : 1 < p * q / (p + q) := by
  have hp1 : 0 < p - 1 := by linarith
  have h := (div_lt_iff₀ hp1).mp hq
  apply (lt_div_iff₀ (by linarith)).2
  nlinarith

/-- The product exponent of `p` and `1 / b` is below two when `b > a = 1 / 2 - 1 / p`. -/
private theorem product_exponent_lt_two {p a b : ℝ} (hp : 0 < p) (hae : a = 1 / 2 - 1 / p)
    (hb : 0 < b) (hab : a < b) : p * (1 / b) / (p + 1 / b) < 2 := by
  rw [ladder_product_exponent hp hb]
  apply (div_lt_iff₀ (add_pos (one_div_pos.mpr hp) hb)).2
  rw [hae] at hab
  linarith

/-- For every finite real `p > 2`, there is a finite strict ladder for the two-dimensional
Sobolev iteration. The final product exponent is greater than two, so the iteration reaches
an exponent with a bounded continuous representative without passing through the critical case.
No regularity assertion about a function is part of this arithmetic statement. -/
theorem exists_finite_sobolev_exponent_ladder {p : ℝ} (hp : 2 < p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ q : ℕ → ℝ,
      p / (p - 1) < q 0 ∧ q 0 ≤ p ∧ StrictMonoOn q (Set.Iic N) ∧
      (∀ j ≤ N, 0 < q j ∧ 1 < p * q j / (p + q j)) ∧
      (∀ j < N, p * q j / (p + q j) < 2 ∧
        q (j + 1) = 2 * (p * q j / (p + q j)) / (2 - p * q j / (p + q j)) ∧
        1 / q (j + 1) = 1 / q j + 1 / p - 1 / 2) ∧
      q (N - 1) < 2 * p / (p - 2) ∧ 2 * p / (p - 2) < q N ∧
        2 < p * q N / (p + q N) := by
  have hp0 : 0 < p := by linarith
  let a : ℝ := (p - 2) / (2 * p)
  have ha : 0 < a := div_pos (by linarith) (by positivity)
  have hae : a = 1 / 2 - 1 / p := by
    dsimp only [a]
    field_simp
  obtain ⟨N, hN, hNlow, hNhigh⟩ := exists_pos_nat_mul_bounds (one_div_pos.mpr hp0).le ha
  let b : ℕ → ℝ := fun j => ((N : ℝ) + 1 / 2 - j) * a
  let q : ℕ → ℝ := fun j => 1 / b j
  have hb : ∀ j ≤ N, 0 < b j := by
    intro j hj
    have hcast : (j : ℝ) ≤ N := by exact_mod_cast hj
    exact mul_pos (by linarith : 0 < (N : ℝ) + 1 / 2 - j) ha
  have hbstep (j : ℕ) : b (j + 1) = b j - a := by
    dsimp only [b]
    push_cast
    ring
  have hmono : StrictMonoOn q (Set.Iic N) := by
    intro i hi j hj hij
    have hcast : (i : ℝ) < j := by exact_mod_cast hij
    have hbij : b j < b i := by dsimp only [b]; nlinarith
    exact one_div_lt_one_div_of_lt (hb j hj) hbij
  have hb0 : b 0 = ((N : ℝ) + 1 / 2) * a := by simp [b]
  have hbinit := ladder_initial_reciprocal hp0.ne' hae ha hNlow hNhigh
  rw [← hb0] at hbinit
  obtain ⟨hq0, hq0p⟩ := ladder_initial_exponent hp hbinit.1 hbinit.2
  have hqpos (j : ℕ) (hj : j ≤ N) : 0 < q j := one_div_pos.mpr (hb j hj)
  have hrone (j : ℕ) (hj : j ≤ N) : 1 < p * q j / (p + q j) :=
    one_lt_product_exponent hp (hqpos j hj)
      (hq0.trans_le (hmono.monotoneOn (by simp) hj (Nat.zero_le j)))
  have hr (j : ℕ) (hj : j ≤ N) : p * q j / (p + q j) = 1 / (1 / p + b j) :=
    ladder_product_exponent hp0 (hb j hj)
  have hrtwo (j : ℕ) (hj : j < N) : p * q j / (p + q j) < 2 := by
    have hcast : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
    exact product_exponent_lt_two hp0 hae (hb j hj.le) (by dsimp only [b]; nlinarith)
  have hlast : b N = a / 2 := by dsimp only [b]; ring
  have hprev : b (N - 1) = 3 * a / 2 := by
    dsimp only [b]
    rw [Nat.cast_sub hN]
    push_cast
    ring
  obtain ⟨hf1, hf2, hf3⟩ := ladder_final_exponents hp (rfl : a = (p - 2) / (2 * p))
  refine ⟨N, hN, q, hq0, hq0p, hmono, fun j hj => ⟨hqpos j hj, hrone j hj⟩,
    fun j hj => ⟨hrtwo j hj, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact ladder_step_eq hp0 hae (hb j hj.le) (hb (j + 1) hj) (hbstep j) (hrtwo j hj)
  · dsimp only [q]
    rw [one_div_one_div, one_div_one_div, hbstep j, hae]
    ring
  · simpa only [q, hprev] using hf1
  · simpa only [q, hlast] using hf2
  · rw [hr N le_rfl, hlast]
    exact hf3

end TauCeti
