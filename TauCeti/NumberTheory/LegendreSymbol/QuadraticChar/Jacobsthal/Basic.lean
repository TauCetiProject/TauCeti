/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import TauCeti.NumberTheory.LegendreSymbol.QuadraticChar.Basic

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
* `TauCeti.jacobsthalPhi_one`, `TauCeti.jacobsthalPsi_two`: `φ_1(a) = ψ_2(a) = -1` for `a ≠ 0`.
* `TauCeti.jacobsthalPhi_zero_right_of_even`, `TauCeti.jacobsthalPhi_zero_right_of_odd`:
  `φ_n(0)` is `0` for even `n` and `q - 1` for odd `n`.
* `TauCeti.jacobsthalPhi_mul_pow`: `φ_n(a sⁿ) = η(s)^(n + 1) φ_n(a)` for `s ≠ 0`, and
  `TauCeti.jacobsthalPhi_two_mul_sq`: `φ_2(a s²) = η(s) φ_2(a)` for every `s`.
* `TauCeti.jacobsthalPhi_two_eq_zero`: `φ_2(a) = 0` when `η(-1) = -1`.
* `TauCeti.sum_jacobsthalPhi_two_sq`: `∑_e φ_2(e)² = q (q - 1) (1 + η(-1))`.
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

/-- The sum of `η(x)²` over a finite field is `q - 1`. -/
private lemma sum_quadraticChar_sq : ∑ x : F, quadraticChar F x ^ 2 = Fintype.card F - 1 := by
  have h := MulChar.sum_one_eq_card_units (R := F) (R' := ℤ)
  rw [Fintype.card_units, Nat.cast_sub Fintype.card_pos, Nat.cast_one] at h
  rw [← h]
  refine sum_congr rfl fun x _ ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp [MulChar.map_nonunit (1 : MulChar F ℤ) not_isUnit_zero]
  · rw [quadraticChar_sq_one hx, MulChar.one_apply (IsUnit.mk0 x hx)]

/-- `φ_1(a) = ∑_x η(x (x + a)) = -1` for `a ≠ 0` in odd characteristic. -/
theorem jacobsthalPhi_one (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    jacobsthalPhi 1 a = -1 := by
  -- `x (x + a) = -(x (-a - x))`, so this is the quadratic Jacobi sum at `c = -a`.
  have h := sum_quadraticChar_mul_sub hF (-a)
  rw [ite_eq_right (neg_ne_zero.mpr ha)] at h
  have hη : quadraticChar F (-1) * quadraticChar F (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  calc jacobsthalPhi 1 a
      = ∑ x : F, quadraticChar F (-1) * quadraticChar F (x * (-a - x)) := by
        refine sum_congr rfl fun x _ ↦ ?_
        rw [← map_mul, ← map_mul, pow_one]
        congr 1
        ring
    _ = -1 := by rw [← mul_sum, h, ← mul_assoc, hη, one_mul]

/-- `ψ_2(a) = ∑_x η(x² + a) = -1` for `a ≠ 0` in odd characteristic. -/
theorem jacobsthalPsi_two (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    jacobsthalPsi 2 a = -1 := by
  -- Group `x` by `u = x²`: `ψ_2(a) = ∑_u (1 + η(u)) η(u + a) = ∑_u η(u + a) + φ_1(a)`.
  have h := sum_comp_mul_sq hF one_ne_zero fun u ↦ quadraticChar F (u + a)
  simp only [one_mul, smul_eq_mul, add_mul, sum_add_distrib] at h
  have h0 : ∑ u : F, quadraticChar F (u + a) = 0 := by
    rw [Fintype.sum_equiv (Equiv.addRight a) (fun u ↦ quadraticChar F (u + a)) _ fun _ ↦ rfl,
      quadraticChar_sum_zero hF]
  rw [jacobsthalPsi, h, h0, zero_add]
  simpa [jacobsthalPhi] using jacobsthalPhi_one hF ha

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

/-- `φ_2(a) = 0` when `-1` is not a square, since `x ↦ -x` changes the sign of every term. -/
theorem jacobsthalPhi_two_eq_zero (h : quadraticChar F (-1) = -1) (a : F) :
    jacobsthalPhi 2 a = 0 := by
  have hneg : jacobsthalPhi 2 a = -jacobsthalPhi 2 a := by
    rw [jacobsthalPhi, ← sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.neg F) _ _ fun x ↦ ?_
    rw [Equiv.neg_apply, neg_sq, ← neg_one_mul x, map_mul, h]
    ring
  omega

/-- The inner sum of the second moment: `∑_e η(x² + e) η(y² + e)` is `q - 1` if `x² = y²` and
`-1` otherwise. -/
private lemma sum_quadraticChar_sq_add_mul_sq_add (hF : ringChar F ≠ 2) (x y : F) :
    ∑ e : F, quadraticChar F (x ^ 2 + e) * quadraticChar F (y ^ 2 + e) =
      if x ^ 2 = y ^ 2 then (Fintype.card F : ℤ) - 1 else -1 := by
  -- Shift `u = x² + e`: then `(x² + e) (y² + e) = -(u (c - u))` with `c = x² - y²`.
  have h := sum_quadraticChar_mul_sub hF (x ^ 2 - y ^ 2)
  have hη : quadraticChar F (-1) * quadraticChar F (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  calc ∑ e : F, quadraticChar F (x ^ 2 + e) * quadraticChar F (y ^ 2 + e)
      = ∑ u : F, quadraticChar F (-1) * quadraticChar F (u * (x ^ 2 - y ^ 2 - u)) := by
        refine Fintype.sum_equiv (Equiv.addLeft (x ^ 2)) _ _ fun e ↦ ?_
        simp only [Equiv.coe_addLeft, ← map_mul]
        congr 1
        ring
    _ = _ := by
        rw [← mul_sum, h, ← mul_assoc, hη, one_mul]
        simp only [sub_eq_zero]

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
          (quadraticChar F (x ^ 2 + e) * quadraticChar F (y ^ 2 + e)) := by
        refine sum_congr rfl fun e _ ↦ ?_
        rw [jacobsthalPhi, sq, sum_mul_sum]
        exact sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ by ring
    _ = ∑ x : F, quadraticChar F x * ∑ y : F, quadraticChar F y *
          (if x ^ 2 = y ^ 2 then (Fintype.card F : ℤ) - 1 else -1) := by
        simp_rw [← sum_quadraticChar_sq_add_mul_sq_add hF, mul_sum, ← mul_assoc]
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

/-- If `a² + b² = 4 n` in `ℤ`, then `a` and `b` are even and `(a / 2)² + (b / 2)² = n`. -/
private lemma sq_div_two_add_sq_div_two {a b n : ℤ} (h : a ^ 2 + b ^ 2 = 4 * n) :
    (a / 2) ^ 2 + (b / 2) ^ 2 = n := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' a <;> obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' b
  · rw [show 2 * k / 2 = k by omega, show 2 * m / 2 = m by omega]
    ring_nf at h ⊢
    omega
  all_goals
    ring_nf at h
    omega

/-- **Jacobsthal's two-squares identity**: over a finite field with `q ≡ 1 (mod 4)` elements,
`q = (φ_2(1) / 2)² + (φ_2(r) / 2)²` for every non-square `r`. The division in `ℤ` is exact: the
proof gives `φ_2(1)² + φ_2(r)² = 4 q` with `q` odd, so both sums are even. -/
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
  refine sq_div_two_add_sq_div_two (mul_left_cancel₀ hq1 ?_)
  linear_combination hsum

end TauCeti
