/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.Combinatorics.Enumerative.Catalan
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Central

/-!
# The least central-binomial rank

In Couveignes's construction of small models of number fields, a number field of degree `n` is
cut out by `r` integer equations in `r` variables of total degree at most `r`. The space of such
equations has dimension `(2r choose r)`, the number of monomials of total degree at most `r` in
`r` variables, and the construction needs it to be at least `n (r + 1)`, the number of values
and first partial derivatives prescribed at the `n` complex conjugates of the generators. This
file studies the least admissible `r`.

`Nat.centralBinomialRank n` is the least positive `r` with `n (r + 1) ≤ (2r choose r)`. Since
`(2r choose r) = (r + 1) Cᵣ` for the Catalan number `Cᵣ`, this is the least positive `r` with
`n ≤ Cᵣ` (`Nat.centralBinomialRank_le_iff`), and the consecutive Catalan ratio
`Cᵣ₊₁ / Cᵣ = 2 (2r + 1) / (r + 2) < 4` shows that the minimal choice wastes less than a factor
four: `(2r choose r) < 4 n (r + 1)` for `0 < n`. Because `Cᵣ` grows like `4ʳ` up to a polynomial
factor, the rank is logarithmic in `n`: it is at least `5` exactly when `14 < n`, and at most
`3 log n` for `73 ≤ n`.

## Main results

* `Nat.centralBinomialRank` — the least positive `r` with `n (r + 1) ≤ (2r choose r)`.
* `Nat.centralBinomialRank_pos`, `Nat.mul_add_one_le_centralBinom_centralBinomialRank` — the
  rank is positive and admissible.
* `Nat.centralBinomialRank_le_iff`, `Nat.lt_centralBinomialRank_iff` — for positive `r`,
  `centralBinomialRank n ≤ r ↔ n ≤ Cᵣ`; in particular every positive `r` below the rank is
  inadmissible.
* `Nat.centralBinom_centralBinomialRank_lt` — `(2r choose r) < 4 n (r + 1)` at the rank.
* `Nat.monotone_centralBinomialRank` — the rank is monotone in `n`.
* `Nat.five_le_centralBinomialRank_iff` — `5 ≤ centralBinomialRank n ↔ 14 < n`.
* `Nat.centralBinomialRank_le_three_mul_log` — `centralBinomialRank n ≤ 3 log n` for `73 ≤ n`.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), 487–497, §4,
  equation (1).
-/

public section

namespace Nat

/-- The least central-binomial rank of `n`: the least positive `r` such that
`n * (r + 1) ≤ (2r choose r)`, equivalently `n ≤ Cᵣ`. The set of such `r` contains
`max n 1` because `n ≤ Cₙ`, so this is its least element; for `n ≤ 1` it is `1`. -/
noncomputable def centralBinomialRank (n : ℕ) : ℕ :=
  sInf {r : ℕ | 0 < r ∧ n * (r + 1) ≤ r.centralBinom}

/-- Every `n` has a positive admissible `r`, namely `max n 1`, since `n ≤ Cₙ`. -/
private theorem centralBinomialRank_set_nonempty (n : ℕ) :
    {r : ℕ | 0 < r ∧ n * (r + 1) ≤ r.centralBinom}.Nonempty :=
  ⟨max n 1, by positivity, mul_add_one_le_centralBinom_iff.2 <|
    (le_max_left n 1).trans (self_le_catalan _)⟩

private theorem centralBinomialRank_mem (n : ℕ) :
    0 < centralBinomialRank n ∧
      n * (centralBinomialRank n + 1) ≤ (centralBinomialRank n).centralBinom :=
  Nat.sInf_mem (centralBinomialRank_set_nonempty n)

/-- The least central-binomial rank is positive. -/
theorem centralBinomialRank_pos (n : ℕ) : 0 < centralBinomialRank n :=
  (centralBinomialRank_mem n).1

/-- The least central-binomial rank `r` is admissible: `n (r + 1) ≤ (2r choose r)`. -/
theorem mul_add_one_le_centralBinom_centralBinomialRank (n : ℕ) :
    n * (centralBinomialRank n + 1) ≤ (centralBinomialRank n).centralBinom :=
  (centralBinomialRank_mem n).2

/-- At the least central-binomial rank `r`, the Catalan number `Cᵣ` is at least `n`. -/
theorem le_catalan_centralBinomialRank (n : ℕ) : n ≤ catalan (centralBinomialRank n) :=
  mul_add_one_le_centralBinom_iff.1 (mul_add_one_le_centralBinom_centralBinomialRank n)

/-- For positive `r`, the least central-binomial rank of `n` is at most `r` exactly when
`r` is admissible, that is, when `n ≤ Cᵣ`. -/
theorem centralBinomialRank_le_iff {n r : ℕ} (hr : 0 < r) :
    centralBinomialRank n ≤ r ↔ n ≤ catalan r :=
  ⟨fun h => (le_catalan_centralBinomialRank n).trans (monotone_catalan h),
    fun h => Nat.sInf_le ⟨hr, mul_add_one_le_centralBinom_iff.2 h⟩⟩

/-- For positive `r`, `r` lies below the least central-binomial rank of `n` exactly when
`Cᵣ < n`: every positive `r` below the rank is inadmissible. -/
theorem lt_centralBinomialRank_iff {n r : ℕ} (hr : 0 < r) :
    r < centralBinomialRank n ↔ catalan r < n := by
  simpa only [not_le] using (centralBinomialRank_le_iff (n := n) hr).not

/-- For `n ≤ 1` the least central-binomial rank is `1`, and only then. -/
theorem centralBinomialRank_eq_one_iff {n : ℕ} : centralBinomialRank n = 1 ↔ n ≤ 1 := by
  have h := centralBinomialRank_le_iff (n := n) one_pos
  rw [catalan_one] at h
  have := centralBinomialRank_pos n
  omega

/-- The least central-binomial rank is monotone in `n`. -/
theorem monotone_centralBinomialRank : Monotone centralBinomialRank := fun _ m hnm =>
  (centralBinomialRank_le_iff (centralBinomialRank_pos m)).2
    (hnm.trans (le_catalan_centralBinomialRank m))

/-- At the least central-binomial rank `r` of a positive `n`, the Catalan number `Cᵣ` is less
than `4 n`: either `r = 1`, or `Cᵣ < 4 Cᵣ₋₁` and `Cᵣ₋₁ < n` by minimality. -/
theorem catalan_centralBinomialRank_lt {n : ℕ} (hn : 0 < n) :
    catalan (centralBinomialRank n) < 4 * n := by
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_one_of_ne_zero (centralBinomialRank_pos n).ne'
  rw [hs]
  rcases s.eq_zero_or_pos with rfl | hs0
  · rw [zero_add, catalan_one]
    omega
  · have hlt : catalan s < n := (lt_centralBinomialRank_iff hs0).1 (by omega)
    exact (catalan_succ_lt_four_mul s).trans_le (by omega)

/-- At the least central-binomial rank `r` of a positive `n`, the central binomial coefficient
`(2r choose r)`, the number of monomials of total degree at most `r` in `r` variables, is less
than `4 n (r + 1)`. -/
theorem centralBinom_centralBinomialRank_lt {n : ℕ} (hn : 0 < n) :
    (centralBinomialRank n).centralBinom < 4 * n * (centralBinomialRank n + 1) := by
  rw [← succ_mul_catalan_eq_centralBinom, mul_comm _ (centralBinomialRank n + 1)]
  exact Nat.mul_lt_mul_of_pos_left (catalan_centralBinomialRank_lt hn) (Nat.succ_pos _)

/-- The least central-binomial rank is at least `5` exactly when `14 < n`, as `C₄ = 14`. -/
theorem five_le_centralBinomialRank_iff {n : ℕ} : 5 ≤ centralBinomialRank n ↔ 14 < n := by
  rw [← catalan_four]
  exact lt_centralBinomialRank_iff (by norm_num)

/-- A positive `s` with `n (s + 1) (2s + 1) ≤ 4ˢ` bounds the least central-binomial rank of
`n`, by the lower estimate `4ˢ ≤ (2s + 1) (2s choose s)`. -/
theorem centralBinomialRank_le_of_mul_le_four_pow {n s : ℕ} (hs : 0 < s)
    (h : n * ((s + 1) * (2 * s + 1)) ≤ 4 ^ s) : centralBinomialRank n ≤ s := by
  rw [centralBinomialRank_le_iff hs, ← mul_add_one_le_centralBinom_iff]
  have h4 := four_pow_le_two_mul_add_one_mul_centralBinom s
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 2 * s + 1 by omega)
  nlinarith

/-- The real inequality `(n : ℝ) ^ 4 < 4 ^ (⌊3 log n⌋₊ + 1)`, from `4 / 3 < log 4`. -/
private theorem pow_four_lt_four_pow_floor_three_mul_log_add_one {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 4 < 4 ^ (⌊3 * Real.log n⌋₊ + 1) := by
  have hlog4 : (4 : ℝ) / 3 < Real.log 4 := by
    have h2 := Real.log_two_gt_d9
    rw [Real.log_four_eq]
    linarith
  have hfloor := Nat.lt_floor_add_one (3 * Real.log n)
  rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  nlinarith

/-- From `73` on, the least central-binomial rank is at most `3 log n` (natural logarithm).
The threshold `73` is not optimal, but some threshold is needed: at `n = 1` the rank is `1`
while `3 log 1 = 0`. -/
theorem centralBinomialRank_le_three_mul_log {n : ℕ} (hn : 73 ≤ n) :
    (centralBinomialRank n : ℝ) ≤ 3 * Real.log n := by
  set s := ⌊3 * Real.log n⌋₊
  have hn' : (73 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog1 : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hlogle : Real.log n ≤ n - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h3log : 0 ≤ 3 * Real.log n := by linarith
  have hs_le : (s : ℝ) ≤ 3 * Real.log n := Nat.floor_le h3log
  have hs_pos : 0 < s := (Nat.one_le_floor_iff _).2 (by linarith)
  have hs3 : s ≤ 3 * n := by
    have : (s : ℝ) ≤ 3 * n := by linarith
    exact_mod_cast this
  -- the polynomial factor `4 (s + 1) (2s + 1)` is at most `n ^ 3`
  have hpoly : 4 * ((s + 1) * (2 * s + 1)) ≤ n ^ 3 := by
    have h1 : 4 * ((s + 1) * (2 * s + 1)) ≤ 4 * ((3 * n + 1) * (2 * (3 * n) + 1)) := by
      gcongr
    refine h1.trans ?_
    have h2 : 73 * n ≤ n * n := Nat.mul_le_mul_right n hn
    have h3 : 73 * (n * n) ≤ n * (n * n) := Nat.mul_le_mul_right (n * n) hn
    nlinarith
  -- the exponential factor: `n ^ 4 < 4 ^ (s + 1)`
  have hexp : n ^ 4 < 4 ^ (s + 1) := by
    exact_mod_cast pow_four_lt_four_pow_floor_three_mul_log_add_one (n := n) (by omega)
  have hkey : n * ((s + 1) * (2 * s + 1)) ≤ 4 ^ s := by
    have : 4 * (n * ((s + 1) * (2 * s + 1))) < 4 * 4 ^ s := by
      calc 4 * (n * ((s + 1) * (2 * s + 1))) = n * (4 * ((s + 1) * (2 * s + 1))) := by ring
        _ ≤ n * n ^ 3 := Nat.mul_le_mul_left n hpoly
        _ = n ^ 4 := by ring
        _ < 4 ^ (s + 1) := hexp
        _ = 4 * 4 ^ s := by ring
    omega
  calc (centralBinomialRank n : ℝ) ≤ s := by
        exact_mod_cast centralBinomialRank_le_of_mul_le_four_pow hs_pos hkey
    _ ≤ 3 * Real.log n := hs_le

end Nat
