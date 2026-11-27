/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Algebra.Order.Floor.Semifield
import TauCeti.NumberTheory.ArithmeticFunction.Moebius
import TauCeti.NumberTheory.ZetaValues

/-!
# MacLeod's functions and MacLeod's identity

MacLeod's functions
`φ_k(x) = (B_k(x) - B_k({x})) / x ^ (k - 1)` (`TauCeti.macleodFun`) interpolate between
`φ₁(x) = ⌊x⌋` and higher-degree polynomial approximations to `x - 1` built from the Bernoulli
polynomials `B_k` (`bernoulliFun k`). Because `B_k(X + 1) - B_k(X) = k X ^ (k - 1)`,
`φ_k(x)` telescopes to the sum `∑_{1 ≤ n ≤ x} k (1 - n / x) ^ (k - 1)`, and hyperbola Möbius
inversion (`ArithmeticFunction.sum_moebius_smul_sum_div`) gives MacLeod's identity:

`∑_{n ≤ x} μ(n) φ_k(x / n) = k (1 - 1 / x) ^ (k - 1)` for `x ≥ 1`.

At `k = 1` this recovers Meissel's identity `∑_{n ≤ x} μ(n) ⌊x / n⌋ = 1`
(`TauCeti.sum_moebius_mul_natFloor_div`). At `k = 2`, differentiating the remainder
`({t}² - {t}) / t` away from the integers gives Balazard's `k = 2` formula for `x m(x) - M(x)`
(`TauCeti.mul_moebiusDivSum_sub_moebiusSum_eq` in `Moebius.Balazard`).

## Main declarations

* `TauCeti.macleodFun`: MacLeod's function `φ_k(x)`.
* `TauCeti.macleodFun_one`, `TauCeti.macleodFun_two`, `TauCeti.macleodFun_of_mem_Ico`,
  `TauCeti.macleodFun_eval_one`, `TauCeti.macleodFun_eq_sum`: values at `k = 1, 2`, on `[0, 1)`,
  at `1`, and the finite sum representation for `x > 0`.
* `TauCeti.sum_moebius_mul_macleodFun`: MacLeod's identity.

## References

* M. Balazard, *Elementary remarks on Möbius' function*, Proc. Steklov Inst. Math. 276 (2012),
  33–39, Proposition 1 and Proposition 2.
-/

public section

open Finset
open scoped ArithmeticFunction.Moebius

namespace TauCeti

/-! ### MacLeod's functions -/

/-- MacLeod's function `φ_k(x) = (B_k(x) - B_k({x})) / x ^ (k - 1)`. For `x > 0`,
this equals `∑_{1 ≤ n ≤ x} k (1 - n / x) ^ (k - 1)`. -/
noncomputable def macleodFun (k : ℕ) (x : ℝ) : ℝ :=
  (bernoulliFun k x - bernoulliFun k (Int.fract x)) / x ^ (k - 1)

/-- The defining formula of `macleodFun`. -/
theorem macleodFun_def (k : ℕ) (x : ℝ) :
    macleodFun k x = (bernoulliFun k x - bernoulliFun k (Int.fract x)) / x ^ (k - 1) := (rfl)

/-- `φ₁(x) = ⌊x⌋` for every real `x`. -/
@[simp]
theorem macleodFun_one (x : ℝ) : macleodFun 1 x = ⌊x⌋ := by
  simp [macleodFun]

/-- `φ₂(x) = x - 1 - ({x}² - {x}) / x` for every nonzero real `x`. -/
theorem macleodFun_two {x : ℝ} (hx : x ≠ 0) :
    macleodFun 2 x = x - 1 - (Int.fract x ^ 2 - Int.fract x) / x := by
  simp only [macleodFun, Nat.add_one_sub_one, pow_one, bernoulliFun_two]
  field_simp
  ring

/-- On `[0, 1)`, `{x} = x`, so `φ_k(x) = 0`. -/
theorem macleodFun_of_mem_Ico (k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    macleodFun k x = 0 := by
  rw [macleodFun, Int.fract_eq_self.mpr ⟨hx0, hx1⟩, sub_self, zero_div]

/-- For `k ≠ 1`, `B_k(1) = B_k(0)`, so `φ_k(1) = 0`. -/
@[simp]
theorem macleodFun_eval_one {k : ℕ} (hk : k ≠ 1) : macleodFun k 1 = 0 := by
  rw [macleodFun, Int.fract_one, bernoulliFun_endpoints_eq_of_ne_one hk, sub_self, zero_div]

/-- Telescoping sum formula for MacLeod's function: for `k : ℕ` and `x > 0`,
`φ_k(x) = ∑_{1 ≤ n ≤ x} k (1 - n / x) ^ (k - 1)`. -/
theorem macleodFun_eq_sum (k : ℕ) {x : ℝ} (hx : 0 < x) :
    macleodFun k x = ∑ n ∈ Icc 1 ⌊x⌋₊, (k : ℝ) * (1 - (n : ℝ) / x) ^ (k - 1) := by
  have hterm (n : ℕ) :
      (k : ℝ) * (1 - ((n + 1 : ℕ) : ℝ) / x) ^ (k - 1) =
        (bernoulliFun k (x - n) - bernoulliFun k (x - (n + 1 : ℕ))) / x ^ (k - 1) := by
    have hdiff := bernoulliFun_eval_add_one k (x - (n + 1 : ℕ))
    have harg : x - (n + 1 : ℕ) + 1 = x - n := by push_cast; ring
    rw [harg] at hdiff
    have hpow : 1 - ((n + 1 : ℕ) : ℝ) / x = (x - (n + 1 : ℕ)) / x := by
      field_simp
    rw [hpow, div_pow, ← mul_div_assoc, ← sub_eq_iff_eq_add'.mpr hdiff]
  have hreindex :
      ∑ n ∈ Icc 1 ⌊x⌋₊, (k : ℝ) * (1 - (n : ℝ) / x) ^ (k - 1) =
        ∑ n ∈ range ⌊x⌋₊, (k : ℝ) * (1 - ((n + 1 : ℕ) : ℝ) / x) ^ (k - 1) := by
    refine Finset.sum_nbij' (fun n ↦ n - 1) (fun n ↦ n + 1) ?_ ?_ ?_ ?_ ?_ <;> intro n hn
    · simp only [mem_Icc, mem_range] at hn ⊢; omega
    · simp only [mem_Icc, mem_range] at hn ⊢; omega
    · simp only [mem_Icc] at hn; omega
    · rfl
    · simp only [mem_Icc] at hn
      congr 3
      rw [Nat.sub_add_cancel hn.1]
  rw [hreindex]
  simp_rw [hterm, ← Finset.sum_div,
    Finset.sum_range_sub' (fun n ↦ bernoulliFun k (x - n)) ⌊x⌋₊]
  have hfl : (⌊x⌋₊ : ℝ) = ⌊x⌋ := by
    rw [← Int.cast_natCast, Int.natCast_floor_eq_floor hx.le]
  rw [Nat.cast_zero, sub_zero, hfl, macleodFun, Int.fract]

/-! ### MacLeod's identity -/

/-- **MacLeod's identity**: for every natural `k : ℕ` and real `x ≥ 1`,
`∑_{n ≤ x} μ(n) φ_k(x / n) = k (1 - 1 / x) ^ (k - 1)`. -/
theorem sum_moebius_mul_macleodFun (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * macleodFun k (x / n) =
      k * (1 - 1 / x) ^ (k - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hsum :
      ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * macleodFun k (x / n) =
        ∑ n ∈ Icc 1 ⌊x⌋₊, μ n •
          ∑ m ∈ Icc 1 (⌊x⌋₊ / n),
            (k : ℝ) * (1 - ((n * m : ℕ) : ℝ) / x) ^ (k - 1) := by
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hxn : 0 < x / n := div_pos hx0 hn0
    rw [zsmul_eq_mul, macleodFun_eq_sum k hxn, Nat.floor_div_natCast]
    congr 1
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    congr 2
    rw [Nat.cast_mul]
    field_simp
  rw [hsum, ArithmeticFunction.sum_moebius_smul_sum_div ⌊x⌋₊
    (fun n ↦ (k : ℝ) * (1 - (n : ℝ) / x) ^ (k - 1))]
  have h1 : 1 ≤ ⌊x⌋₊ := Nat.succ_le_of_lt (Nat.floor_pos.mpr hx)
  simp [h1]

end TauCeti
