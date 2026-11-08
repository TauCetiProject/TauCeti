/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

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
  have hp1 : 0 < p - 1 := by linarith
  let a : ℝ := (p - 2) / (2 * p)
  have ha : 0 < a := div_pos (by linarith) (by positivity)
  have hae : a = 1 / 2 - 1 / p := by
    dsimp only [a]
    field_simp
  let N : ℕ := ⌊(1 / p) / a⌋₊ + 1
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hNlow : 1 / p < (N : ℝ) * a := by
    have h := Nat.lt_floor_add_one ((1 / p) / a)
    have h' : (1 / p) / a < (N : ℝ) := by simpa only [N, Nat.cast_add,
      Nat.cast_one] using h
    exact (div_lt_iff₀ ha).mp h'
  have hNhigh : (N : ℝ) * a ≤ 1 / p + a := by
    have h := Nat.floor_le (show 0 ≤ (1 / p) / a by positivity)
    have h' := (le_div_iff₀ ha).mp h
    dsimp only [N]
    push_cast
    nlinarith
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
  have hb0 : 1 / p < b 0 ∧ b 0 < (p - 1) / p := by
    have hfrac : (p - 1) / p = 1 / p + 2 * a := by
      rw [hae]
      field_simp
      ring
    dsimp only [b]
    push_cast
    rw [hfrac]
    constructor <;> nlinarith
  have hq0 : p / (p - 1) < q 0 := by
    dsimp only [q]
    apply (div_lt_div_iff₀ hp1 (hb 0 (by omega))).2
    have h := (lt_div_iff₀ hp0).mp hb0.2
    nlinarith
  have hq0p : q 0 ≤ p := by
    apply (div_le_iff₀ (hb 0 (by omega))).2
    have h := (div_lt_iff₀ hp0).mp hb0.1
    linarith
  have hqpos (j : ℕ) (hj : j ≤ N) : 0 < q j := one_div_pos.mpr (hb j hj)
  have hrone (j : ℕ) (hj : j ≤ N) : 1 < p * q j / (p + q j) := by
    have hq : p / (p - 1) < q j :=
      hq0.trans_le (hmono.monotoneOn (by simp) hj (Nat.zero_le j))
    have h := (div_lt_iff₀ hp1).mp hq
    apply (lt_div_iff₀ (by linarith [hqpos j hj])).2
    nlinarith
  have hr (j : ℕ) (hj : j ≤ N) :
      p * q j / (p + q j) = 1 / (1 / p + b j) := by
    dsimp only [q]
    field_simp [hp0.ne', (hb j hj).ne']
    ring
  have hbefore (j : ℕ) (hj : j < N) : a < b j := by
    have hcast : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
    dsimp only [b]
    nlinarith
  have hrtwo (j : ℕ) (hj : j < N) : p * q j / (p + q j) < 2 := by
    rw [hr j hj.le]
    apply (div_lt_iff₀ (add_pos (one_div_pos.mpr hp0) (hb j hj.le))).2
    have h := hbefore j hj
    rw [hae] at h
    linarith
  have hlast : b N = a / 2 := by dsimp only [b]; ring
  have hprev : b (N - 1) = 3 * a / 2 := by
    dsimp only [b]
    rw [Nat.cast_sub hN]
    push_cast
    ring
  have hthreshold : 2 * p / (p - 2) = 1 / a := by
    dsimp only [a]
    field_simp
  refine ⟨N, hN, q, hq0, hq0p, hmono, fun j hj => ⟨hqpos j hj, hrone j hj⟩,
    ?_, ?_, ?_, ?_⟩
  · intro j hj
    refine ⟨hrtwo j hj, ?_, ?_⟩
    · apply (eq_div_iff (sub_pos.mpr (hrtwo j hj)).ne').2
      rw [hr j hj.le]
      dsimp only [q]
      have hbn : b (j + 1) ≠ 0 := (hb (j + 1) (by omega)).ne'
      have hd : 1 / p + b j ≠ 0 := (add_pos (one_div_pos.mpr hp0) (hb j hj.le)).ne'
      field_simp [hbn, hd]
      rw [hbstep j, hae]
      have hd' : 1 + p * b j ≠ 0 := (add_pos zero_lt_one (mul_pos hp0 (hb j hj.le))).ne'
      field_simp [hp0.ne', hd']
      ring
    · dsimp only [q]
      rw [one_div_one_div, one_div_one_div, hbstep j, hae]
      ring
  · rw [hthreshold]
    dsimp only [q]
    rw [hprev]
    exact one_div_lt_one_div_of_lt ha (by linarith)
  · rw [hthreshold]
    dsimp only [q]
    rw [hlast]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  · rw [hr N le_rfl, hlast]
    apply (lt_div_iff₀ (by positivity : 0 < 1 / p + a / 2)).2
    rw [hae]
    have h := (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) hp)
    linarith

end TauCeti
