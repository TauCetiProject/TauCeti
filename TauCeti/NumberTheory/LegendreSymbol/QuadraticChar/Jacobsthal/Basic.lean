/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import TauCeti.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import TauCeti.Data.Int.SumSquares

/-!
# Jacobsthal sums

Let `F` be a finite field with `q` elements and quadratic character `η`. The Jacobsthal sums are
`φ_n(a) = ∑_x η(x) η(x^n + a)` (`TauCeti.jacobsthalPhi`) and `ψ_n(a) = ∑_x η(x^n + a)`
(`TauCeti.jacobsthalPsi`), with values in `ℤ`.

For `a ≠ 0` in odd characteristic, `φ_1(a)` is a quadratic Jacobi sum, so `φ_1(a) = -1`, and
grouping `x` by `x²` gives `ψ_2(a) = ψ_1(a) + φ_1(a) = -1`. The substitution `x = s y` scales
`φ_n(a sⁿ)` by `η(s)^(n + 1)`. The second moment `∑_e φ_2(e)²` is `q (q - 1) (1 + η(-1))`: after
the square is expanded, the sum over `e` is a quadratic Jacobi sum again. When `q ≡ 1 (mod 4)`,
`φ_2(e)²` takes one value on the nonzero squares and one value on the non-squares, so the second
moment gives Jacobsthal's representation of `q` as a sum of two squares.

The Jacobi-sum expansions of `ψ_n` and `φ_n` are in
`TauCeti.NumberTheory.LegendreSymbol.QuadraticChar.Jacobsthal.JacobiSum`.

## Main results

* `TauCeti.jacobsthalPhi_def`, `TauCeti.jacobsthalPsi_def`: the defining formulas.
* `TauCeti.jacobsthalPhi_one`, `TauCeti.jacobsthalPsi_two`: `φ_1(a) = ψ_2(a) = -1` for `a ≠ 0`, in
  odd characteristic.
* `TauCeti.sum_quadraticChar_sub_sq`: `∑_x η(c - x²) = -η(-1)` for `c ≠ 0`, in odd
  characteristic.
* `TauCeti.jacobsthalPhi_zero_right_of_even`, `TauCeti.jacobsthalPhi_zero_right_of_odd`:
  `φ_n(0)` is `0` for even `n` in odd characteristic, and `q - 1` for odd `n`.
* `TauCeti.jacobsthalPhi_mul_pow`: `φ_n(a sⁿ) = η(s)^(n + 1) φ_n(a)` for `s ≠ 0`, and
  `TauCeti.jacobsthalPhi_two_mul_sq`: `φ_2(a s²) = η(s) φ_2(a)` for every `s`, in odd
  characteristic.
* `TauCeti.jacobsthalPhi_eq_zero_of_even`: `φ_n(a) = 0` for even `n` when `η(-1) = -1`.
* `TauCeti.sum_jacobsthalPhi_two_sq`: `∑_e φ_2(e)² = q (q - 1) (1 + η(-1))` in odd
  characteristic.
* `TauCeti.jacobsthalPhi_two_sq_add_sq`: **Jacobsthal's two-squares identity**. If
  `q ≡ 1 (mod 4)` and `r` is not a square, then `q = (φ_2(1) / 2)² + (φ_2(r) / 2)²`.

## References

* E. Jacobsthal, *Über die Darstellung der Primzahlen der Form 4n+1 als Summe zweier Quadrate*,
  J. Reine Angew. Math. 132 (1907), 238–245, §2.
-/

public section

open Finset

namespace TauCeti

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The Jacobsthal sum `φ_n(a) = ∑_x η(x) η(x^n + a)`, for the quadratic character `η` of the
finite field `F`. -/
def jacobsthalPhi (n : ℕ) (a : F) : ℤ :=
  ∑ x : F, quadraticChar F x * quadraticChar F (x ^ n + a)

/-- The Jacobsthal sum `ψ_n(a) = ∑_x η(x^n + a)`, for the quadratic character `η` of the finite
field `F`. -/
def jacobsthalPsi (n : ℕ) (a : F) : ℤ :=
  ∑ x : F, quadraticChar F (x ^ n + a)

/-- The defining formula of `TauCeti.jacobsthalPhi`. -/
theorem jacobsthalPhi_def (n : ℕ) (a : F) :
    jacobsthalPhi n a = ∑ x : F, quadraticChar F x * quadraticChar F (x ^ n + a) :=
  (rfl)

/-- The defining formula of `TauCeti.jacobsthalPsi`. -/
theorem jacobsthalPsi_def (n : ℕ) (a : F) :
    jacobsthalPsi n a = ∑ x : F, quadraticChar F (x ^ n + a) :=
  (rfl)

/-- `φ_1(a) = ∑_x η(x (x + a)) = -1` for `a ≠ 0` in odd characteristic. -/
theorem jacobsthalPhi_one (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    jacobsthalPhi 1 a = -1 := by
  -- This is the autocorrelation of `η` at the shifts `0 ≠ a`.
  have h := sum_quadraticChar_add_mul_add hF 0 a
  rw [ite_eq_right fun h0 ↦ ha h0.symm] at h
  rw [jacobsthalPhi_def, ← h]
  simp only [pow_one, add_zero]

/-- `ψ_2(a) = ∑_x η(x² + a) = -1` for `a ≠ 0` in odd characteristic. -/
theorem jacobsthalPsi_two (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    jacobsthalPsi 2 a = -1 := by
  -- Group `x` by `u = x²`: `ψ_2(a) = ∑_u (1 + η(u)) η(u + a) = ∑_u η(u + a) + φ_1(a)`.
  have h := sum_comp_mul_sq hF one_ne_zero fun u ↦ quadraticChar F (u + a)
  simp only [one_mul, smul_eq_mul, add_mul, sum_add_distrib] at h
  rw [jacobsthalPsi, h, sum_quadraticChar_add hF a, zero_add, ← jacobsthalPhi_one hF ha,
    jacobsthalPhi_def]
  simp only [pow_one]

/-- `∑_x η(c - x²) = -η(-1)` for `c ≠ 0` in odd characteristic. -/
theorem sum_quadraticChar_sub_sq (hF : ringChar F ≠ 2) {c : F} (hc : c ≠ 0) :
    ∑ x : F, quadraticChar F (c - x ^ 2) = -quadraticChar F (-1) := by
  -- `η(c - x²) = η(-1) η(x² - c)`, and `∑_x η(x² - c) = ψ_2(-c) = -1`.
  have h := jacobsthalPsi_two hF (neg_ne_zero.mpr hc)
  rw [jacobsthalPsi_def] at h
  have e (x : F) : c - x ^ 2 = -1 * (x ^ 2 + -c) := by ring
  simp_rw [e, map_mul, ← mul_sum, h, mul_neg_one]

/-- `φ_n(0) = ∑_x η(x)^(n + 1) = 0` for even `n` in odd characteristic. -/
theorem jacobsthalPhi_zero_right_of_even (hF : ringChar F ≠ 2) {n : ℕ} (hn : Even n) :
    jacobsthalPhi n (0 : F) = 0 := by
  obtain ⟨k, rfl⟩ := hn
  rw [jacobsthalPhi, ← quadraticChar_sum_zero hF]
  refine sum_congr rfl fun x _ ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [add_zero, map_pow, ← two_mul, pow_mul, quadraticChar_sq_one hx, one_pow, mul_one]

/-- `φ_n(0) = ∑_x η(x)^(n + 1) = q - 1` for odd `n`. -/
theorem jacobsthalPhi_zero_right_of_odd {n : ℕ} (hn : Odd n) :
    jacobsthalPhi n (0 : F) = Fintype.card F - 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [jacobsthalPhi, ← sum_quadraticChar_sq]
  refine sum_congr rfl fun x _ ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [add_zero, map_pow, ← pow_succ', show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul,
      quadraticChar_sq_one hx, one_pow]

/-- **Scaling**: `φ_n(a sⁿ) = η(s)^(n + 1) φ_n(a)` for `s ≠ 0`. -/
theorem jacobsthalPhi_mul_pow (n : ℕ) (a : F) {s : F} (hs : s ≠ 0) :
    jacobsthalPhi n (a * s ^ n) = quadraticChar F s ^ (n + 1) * jacobsthalPhi n a := by
  -- Substitute `x = s y`.
  rw [jacobsthalPhi, jacobsthalPhi, mul_sum]
  refine (Fintype.sum_bijective (s * ·) (mulLeft_bijective₀ s hs) _ _ fun y ↦ ?_).symm
  rw [show (s * y) ^ n + a * s ^ n = s ^ n * (y ^ n + a) by ring, map_mul, map_mul, map_pow]
  ring

/-- **Scaling**: `φ_2(a s²) = η(s) φ_2(a)` for every `s` in odd characteristic. -/
theorem jacobsthalPhi_two_mul_sq (hF : ringChar F ≠ 2) (a s : F) :
    jacobsthalPhi 2 (a * s ^ 2) = quadraticChar F s * jacobsthalPhi 2 a := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [zero_pow two_ne_zero, mul_zero, quadraticChar_zero, zero_mul]
    exact jacobsthalPhi_zero_right_of_even hF even_two
  · rw [jacobsthalPhi_mul_pow 2 a hs, pow_succ, quadraticChar_sq_one hs, one_mul]

/-- `φ_n(a) = 0` for even `n` when `-1` is not a square. -/
theorem jacobsthalPhi_eq_zero_of_even {n : ℕ} (hn : Even n) (h : quadraticChar F (-1) = -1)
    (a : F) : jacobsthalPhi n a = 0 := by
  -- `η(x) η(xⁿ + a) = η(x (xⁿ + a))`, and `x ↦ x (xⁿ + a)` is odd, so `x ↦ -x` changes the sign
  -- of every term.
  simp_rw [jacobsthalPhi, ← map_mul]
  exact quadraticChar_sum_comp_eq_zero_of_odd (quadraticChar_neg_one_iff_not_isSquare.mp h)
    fun x ↦ by rw [hn.neg_pow]; ring

/-- For `x ≠ 0` in odd characteristic, `∑_y η(y) (q [x² = y²] - 1) = q (η(x) + η(-x))`. -/
private lemma sum_quadraticChar_mul_ite (hF : ringChar F ≠ 2) {x : F} (hx : x ≠ 0) :
    ∑ y : F, quadraticChar F y * (if x ^ 2 = y ^ 2 then (Fintype.card F : ℤ) - 1 else -1) =
      Fintype.card F * (quadraticChar F x * (1 + quadraticChar F (-1))) := by
  have hxx : x ≠ -x := fun h ↦ hx ((Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h.symm)
  have key : ∀ y : F,
      quadraticChar F y * (if x ^ 2 = y ^ 2 then (Fintype.card F : ℤ) - 1 else -1) =
        ((if y = x then (Fintype.card F : ℤ) * quadraticChar F x else 0) +
          if y = -x then (Fintype.card F : ℤ) * quadraticChar F (-x) else 0) -
          quadraticChar F y := by
    intro y
    by_cases h1 : y = x
    · rw [h1, ite_eq_left rfl, ite_eq_left rfl, ite_eq_right hxx]
      ring
    by_cases h2 : y = -x
    · rw [h2, ite_eq_left (neg_sq x).symm, ite_eq_right hxx.symm, ite_eq_left rfl]
      ring
    rw [ite_eq_right fun h ↦ (sq_eq_sq_iff_eq_or_eq_neg.mp h.symm).elim h1 h2, ite_eq_right h1,
      ite_eq_right h2]
    ring
  rw [sum_congr rfl fun y _ ↦ key y, sum_sub_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq',
    quadraticChar_sum_zero hF]
  simp only [mem_univ, ↓reduceIte, sub_zero]
  rw [show quadraticChar F (-x) = quadraticChar F (-1) * quadraticChar F x by
    rw [← map_mul, neg_one_mul]]
  ring

/-- **The second moment** of `φ_2`: `∑_e φ_2(e)² = q (q - 1) (1 + η(-1))` in odd
characteristic. -/
theorem sum_jacobsthalPhi_two_sq (hF : ringChar F ≠ 2) :
    ∑ e : F, jacobsthalPhi 2 e ^ 2 =
      Fintype.card F * (Fintype.card F - 1) * (1 + quadraticChar F (-1)) := by
  -- Expand the square, then sum over `e` first.
  calc ∑ e : F, jacobsthalPhi 2 e ^ 2
      = ∑ e : F, ∑ x : F, ∑ y : F, quadraticChar F x * quadraticChar F y *
          (quadraticChar F (e + x ^ 2) * quadraticChar F (e + y ^ 2)) := by
        refine sum_congr rfl fun e _ ↦ ?_
        rw [jacobsthalPhi, sq, sum_mul_sum]
        exact sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ by
          rw [add_comm e, add_comm e]
          ring
    _ = ∑ x : F, quadraticChar F x * ∑ y : F, quadraticChar F y *
          (if x ^ 2 = y ^ 2 then (Fintype.card F : ℤ) - 1 else -1) := by
        simp_rw [← sum_quadraticChar_add_mul_add hF, mul_sum, ← mul_assoc]
        conv_lhs => rw [sum_comm]
        exact sum_congr rfl fun x _ ↦ sum_comm
    _ = ∑ x : F, Fintype.card F * (1 + quadraticChar F (-1)) * quadraticChar F x ^ 2 := by
        refine sum_congr rfl fun x _ ↦ ?_
        rcases eq_or_ne x 0 with rfl | hx
        · simp
        · rw [sum_quadraticChar_mul_ite hF hx]
          ring
    _ = _ := by
        rw [← mul_sum, sum_quadraticChar_sq]
        ring

/-- **Jacobsthal's two-squares identity**: over a finite field with `q ≡ 1 (mod 4)` elements,
`q = (φ_2(1) / 2)² + (φ_2(r) / 2)²` for every non-square `r`. Here `φ_2(1)` and `φ_2(r)` are
even, since their squares sum to `4 q`, so the divisions in `ℤ` are exact. -/
theorem jacobsthalPhi_two_sq_add_sq (hq : Fintype.card F % 4 = 1) {r : F} (hr : ¬IsSquare r) :
    (jacobsthalPhi 2 (1 : F) / 2) ^ 2 + (jacobsthalPhi 2 r / 2) ^ 2 = Fintype.card F := by
  have hF : ringChar F ≠ 2 := by
    rw [Ne, FiniteField.even_card_iff_char_two]
    omega
  have hη : quadraticChar F (-1) = 1 := by
    rw [quadraticChar_neg_one hF, ZMod.χ₄_nat_one_mod_four hq]
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr IsSquare.zero
  have hηr : quadraticChar F r = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hr
  -- Sum `φ_2(e)²` over the squares `e = t²` and over the non-squares `e = r t²`.
  have h1 := sum_comp_mul_sq hF one_ne_zero fun e ↦ jacobsthalPhi 2 e ^ 2
  have h2 := sum_comp_mul_sq hF hr0 fun e ↦ jacobsthalPhi 2 e ^ 2
  simp only [jacobsthalPhi_two_mul_sq hF, mul_pow, smul_eq_mul] at h1 h2
  simp only [one_mul] at h1
  simp only [map_mul, hηr] at h2
  rw [← sum_mul, sum_quadraticChar_sq] at h1 h2
  have hsum : ((Fintype.card F : ℤ) - 1) * jacobsthalPhi 2 (1 : F) ^ 2 +
      ((Fintype.card F : ℤ) - 1) * jacobsthalPhi 2 r ^ 2 = 2 * ∑ e : F, jacobsthalPhi 2 e ^ 2 := by
    rw [h1, h2, ← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun e _ ↦ by ring
  rw [sum_jacobsthalPhi_two_sq hF, hη] at hsum
  have hq1 : (Fintype.card F : ℤ) - 1 ≠ 0 := by
    have := Fintype.one_lt_card (α := F)
    omega
  refine div_two_sq_add_div_two_sq_of_sq_add_sq_eq_four_mul (mul_left_cancel₀ hq1 ?_)
  linear_combination hsum

end TauCeti
