/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Chords of discretely concave sequences

A sequence `a : ℕ → K` in a linearly ordered commutative ring is discretely concave on
`[0, r]` when `a j + a (j + 2) ≤ 2 a (j + 1)` for `j + 2 ≤ r`, that is, when its increments
`a (j + 1) - a j` decrease. This file proves the chord inequalities of such sequences: the
slope of a chord decreases when either endpoint moves to the right.

## Main results

* `TauCeti.mul_sub_le_mul_sub_of_add_le_two_mul`: for `p < q < m ≤ r`, the slope over `[q, m]`
  is at most the slope over `[p, q]`, in the form `(q - p) (a m - a q) ≤ (m - q) (a q - a p)`.
* `TauCeti.div_sub_le_div_sub_of_add_le_two_mul`: in a linearly ordered field, the slope over
  `[s, r]` is at most the slope over `[l, k]` when `l ≤ s`, `l < k ≤ r` and `s < r`.
-/

public section

namespace TauCeti

section OrderedRing

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Three chords of a concave sequence: if `a_j + a_{j+2} ≤ 2 a_{j+1}` for `j + 2 ≤ r`, then for
`p < q < m ≤ r` the slope over `[q, m]` is at most the slope over `[p, q]`. -/
theorem mul_sub_le_mul_sub_of_add_le_two_mul {a : ℕ → K} {r : ℕ}
    (ha : ∀ j, j + 2 ≤ r → a j + a (j + 2) ≤ 2 * a (j + 1)) {p q m : ℕ} (hpq : p < q)
    (hqm : q < m) (hmr : m ≤ r) :
    ((q : K) - p) * (a m - a q) ≤ ((m : K) - q) * (a q - a p) := by
  -- the differences `a (j + 1) - a j` decrease on `[0, r)`
  have hd : ∀ i j, i ≤ j → j + 1 ≤ r → a (j + 1) - a j ≤ a (i + 1) - a i := by
    intro i j hij hjr
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j _ ih =>
      have := ha j (by omega)
      linarith [ih (by omega)]
  -- the chord over `[p, q]` against the difference at `q`
  have hB1 : ∀ t p : ℕ, p + t = q → (t : K) * (a (q + 1) - a q) ≤ a q - a p := by
    intro t
    induction t with
    | zero => intro p h; subst h; simp
    | succ t ih =>
      intro p h
      have := ih (p + 1) (by omega)
      have := hd p q (by omega) (by omega)
      push_cast
      linarith
  -- the chord over `[q, q + t]` against the difference at `q`
  have hB2 : ∀ t : ℕ, q + t ≤ r → a (q + t) - a q ≤ t * (a (q + 1) - a q) := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro hq
      have := ih (by omega)
      have := hd q (q + t) (by omega) (by omega)
      rw [← add_assoc]
      push_cast
      linarith
  have h1 := hB1 (q - p) p (by omega)
  have h2 := hB2 (m - q) (by omega)
  have hqm' : q + (m - q) = m := by omega
  rw [hqm'] at h2
  push_cast [Nat.cast_sub hpq.le, Nat.cast_sub hqm.le] at h1 h2
  have hqp : (0 : K) ≤ q - p := sub_nonneg.mpr (by exact_mod_cast hpq.le)
  have hmq : (0 : K) ≤ m - q := sub_nonneg.mpr (by exact_mod_cast hqm.le)
  nlinarith [mul_le_mul_of_nonneg_left h1 hmq, mul_le_mul_of_nonneg_left h2 hqp]

end OrderedRing

section Field

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A sequence `a` with `a_j + a_{j+2} ≤ 2 a_{j+1}` for `j + 2 ≤ r` is concave on `[0, r]`: the
slope of the chord over `[s, r]` is at most the slope over `[l, k]` when `l ≤ s` and `k ≤ r`. -/
theorem div_sub_le_div_sub_of_add_le_two_mul {a : ℕ → K} {r : ℕ}
    (ha : ∀ j, j + 2 ≤ r → a j + a (j + 2) ≤ 2 * a (j + 1)) {s k l : ℕ} (hsr : s < r)
    (hlk : l < k) (hkr : k ≤ r) (hls : l ≤ s) :
    (a r - a s) / ((r : K) - s) ≤ (a k - a l) / ((k : K) - l) := by
  have hkl : (0 : K) < k - l := by
    have : (l : K) < k := by exact_mod_cast hlk
    linarith
  have hrs : (0 : K) < r - s := by
    have : (s : K) < r := by exact_mod_cast hsr
    linarith
  have hrl : (0 : K) < r - l := by
    have : (l : K) < r := by exact_mod_cast (hlk.trans_le hkr)
    linarith
  -- the slope over `[s, r]` is at most the slope over `[l, r]`
  have step1 : (a r - a s) / ((r : K) - s) ≤ (a r - a l) / ((r : K) - l) := by
    rw [div_le_div_iff₀ hrs hrl]
    rcases hls.lt_or_eq with hls | rfl
    · have := mul_sub_le_mul_sub_of_add_le_two_mul ha hls hsr le_rfl
      nlinarith
    · exact le_rfl
  -- the slope over `[l, r]` is at most the slope over `[l, k]`
  have step2 : (a r - a l) / ((r : K) - l) ≤ (a k - a l) / ((k : K) - l) := by
    rw [div_le_div_iff₀ hrl hkl]
    rcases hkr.lt_or_eq with hkr | rfl
    · have := mul_sub_le_mul_sub_of_add_le_two_mul ha hlk hkr le_rfl
      nlinarith
    · exact le_rfl
  exact step1.trans step2

end Field

end TauCeti
