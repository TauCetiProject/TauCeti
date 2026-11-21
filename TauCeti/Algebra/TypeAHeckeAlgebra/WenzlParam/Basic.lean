/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Wenzl's discrete Markov trace parameters

For an integer `d ≠ 0` and a parameter `Q`, Wenzl's discrete trace parameter is

`a_d(Q) = (1 - Q ^ (d + 1)) / ((1 + Q) * (1 - Q ^ d))`,

with the removable value `a_d(1) = (d + 1) / (2 * d)`. In Wenzl's classification of positive
Markov traces on the type-A Hecke algebras, which is not proved here, the projection parameters at
`Q = q ^ 2 > 0` form a closed interval together with the discrete values `a_d(Q)`, and at the
roots of unity `Q = exp (± 2 π i / l)` they are the values `a_k(Q)`, `1 ≤ k ≤ l - 1`. This file
develops the algebraic theory of the parameters themselves, characterizes the closed and open real
interval at `Q > -1` by the quadratic relation `a_(-2)(Q) ≤ η * (1 - η)`, and expresses
`a_(-r)(Q)` in terms of geometric weights. Continuity and exponential evaluations are in
`TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam.Analytic`, root-of-unity evaluations are in
`TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam.RootOfUnity`, and the identification with the Ocneanu
trace of the geometric atomic model is in
`TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Geometric`.

We define `a_d(Q)` (`TauCeti.wenzlParam`) without division by `1 - Q`: for `d = r ≥ 0` and for
`d = -r`, with `[n]_Q = ∑ i < n, Q ^ i`,

`a_r(Q) = [r + 1]_Q / ((1 + Q) * [r]_Q)` and `a_(-r)(Q) = Q * [r - 1]_Q / ((1 + Q) * [r]_Q)`.

This is a regular function of `Q` wherever `(1 + Q) * [|d|]_Q ≠ 0`, it agrees with the closed form
whenever `Q ≠ 0, 1`, and its value at `Q = 1` is the removable limit.

## Main definitions

* `TauCeti.wenzlParam d Q`: the parameter `a_d(Q)`.

## Main results

* `TauCeti.wenzlParam_eq_div` and `TauCeti.map_wenzlParam`: the closed form
  `(1 - Q ^ (d + 1)) / ((1 + Q) * (1 - Q ^ d))`, and compatibility with field homomorphisms.
* `TauCeti.wenzlParam_one`: the value `(d + 1) / (2 * d)` at `Q = 1`.
* `TauCeti.wenzlParam_add_wenzlParam_neg`: the complement identity `a_d + a_(-d) = 1`.
* `TauCeti.wenzlParam_inv`: the inversion symmetry `a_d(Q⁻¹) = a_d(Q)`.
* `TauCeti.wenzlParam_neg_one`, `TauCeti.wenzlParam_one_left`, `TauCeti.wenzlParam_natCast_zero`,
  `TauCeti.wenzlParam_neg_natCast_zero`, `TauCeti.wenzlParam_neg_two`, `TauCeti.wenzlParam_two`,
  and `TauCeti.wenzlParam_neg_two_sq`: the scalar values `a_(-1) = 0`, `a_1 = 1`, the `Q = 0`
  values, and the Jones values `a_(-2)(Q) = Q / (1 + Q) ^ 2 = (q + q⁻¹)⁻²` and `a_2(Q)`.
* `TauCeti.wenzlParam_neg_two_eq_mul_one_sub_iff`,
  `TauCeti.wenzlParam_neg_two_le_mul_one_sub_iff`, and
  `TauCeti.wenzlParam_neg_two_lt_mul_one_sub_iff`: `a_(-2)(Q) = η * (1 - η)` characterizes the
  endpoints `1 / (1 + Q)` and `Q / (1 + Q)`, and `≤` / `<` characterize the closed and open
  intervals between them whenever `1 + Q ≠ 0`.
* `TauCeti.wenzlParam_add_of_pow_eq_one`: `a_d` is periodic in `d` modulo the order of `Q`; in
  particular `a_(l - 2) = a_(-2)` when `Q ^ l = 1`.
* `TauCeti.wenzlParam_neg_natCast_eq_sum`: for the normalized geometric weights
  `p_i = Q ^ i / [r]_Q`, `i < r`, the sum `∑ i < j, p_i * p_j` is `a_(-r)(Q)`.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383,
  §3, for the parameters `a_k` and the classification of positive Markov traces.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §11, for the Jones parameter `τ = (q + q⁻¹)⁻²`.
-/

public section

open Finset

namespace TauCeti

variable {K : Type*} [Field K]

/-- **Wenzl's discrete trace parameter** `a_d(Q)`. For `d = r ≥ 0` it is
`[r + 1]_Q / ((1 + Q) * [r]_Q)`, and for `d = -(r + 1)` it is `Q * [r]_Q / ((1 + Q) * [r + 1]_Q)`,
where `[n]_Q = ∑ i < n, Q ^ i`. When `Q ≠ 0, 1` it is
`(1 - Q ^ (d + 1)) / ((1 + Q) * (1 - Q ^ d))` (`TauCeti.wenzlParam_eq_div`). The value at `d = 0`
is the junk value `0`. -/
noncomputable def wenzlParam : ℤ → K → K
  | (r : ℕ), Q => (∑ i ∈ range (r + 1), Q ^ i) / ((1 + Q) * ∑ i ∈ range r, Q ^ i)
  | .negSucc r, Q => Q * (∑ i ∈ range r, Q ^ i) / ((1 + Q) * ∑ i ∈ range (r + 1), Q ^ i)

/-- The parameter `a_r(Q) = [r + 1]_Q / ((1 + Q) * [r]_Q)` for `r ≥ 0`. -/
theorem wenzlParam_natCast (r : ℕ) (Q : K) :
    wenzlParam (r : ℤ) Q = (∑ i ∈ range (r + 1), Q ^ i) / ((1 + Q) * ∑ i ∈ range r, Q ^ i) :=
  (rfl)

/-- The junk value `a_0(Q) = 0`. -/
@[simp]
theorem wenzlParam_zero (Q : K) : wenzlParam 0 Q = 0 := by
  rw [← Nat.cast_zero (R := ℤ), wenzlParam_natCast]
  simp

/-- The parameter `a_(-r)(Q) = Q * [r - 1]_Q / ((1 + Q) * [r]_Q)` for `r ≥ 0`. -/
theorem wenzlParam_neg_natCast (r : ℕ) (Q : K) :
    wenzlParam (-(r : ℤ)) Q =
      Q * (∑ i ∈ range (r - 1), Q ^ i) / ((1 + Q) * ∑ i ∈ range r, Q ^ i) := by
  rcases r with _ | r
  · simp
  · rw [Nat.cast_succ, ← Int.negSucc_eq, wenzlParam, Nat.add_sub_cancel]

/-! ### The closed form and the value at `Q = 1` -/

/-- **The closed form** `a_d(Q) = (1 - Q ^ (d + 1)) / ((1 + Q) * (1 - Q ^ d))` for `Q ≠ 0, 1`. -/
theorem wenzlParam_eq_div {Q : K} (hQ₀ : Q ≠ 0) (hQ₁ : Q ≠ 1) (d : ℤ) :
    wenzlParam d Q = (1 - Q ^ (d + 1)) / ((1 + Q) * (1 - Q ^ d)) := by
  have hQ : Q - 1 ≠ 0 := sub_ne_zero.2 hQ₁
  obtain ⟨r, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · rw [wenzlParam_natCast, ← mul_div_mul_right _ _ hQ, mul_assoc, geom_sum_mul, geom_sum_mul,
      ← neg_div_neg_eq]
    norm_cast
    ring_nf
  · rw [wenzlParam_neg_natCast]
    rcases r with _ | r
    · simp
    have h₁ : Q ^ (r + 1 : ℕ) * Q ^ (-((r + 1 : ℕ) : ℤ) + 1) = Q := by
      rw [← zpow_natCast, ← zpow_add₀ hQ₀]
      simp
    have h₂ : Q ^ (r + 1 : ℕ) * Q ^ (-((r + 1 : ℕ) : ℤ)) = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ hQ₀]
      simp
    simp only [Nat.add_sub_cancel]
    -- Clear `Q - 1` on the left and the negative powers on the right.
    conv_lhs => rw [← mul_div_mul_right _ _ hQ]
    conv_rhs => rw [← mul_div_mul_left _ _ (pow_ne_zero (r + 1) hQ₀)]
    congr 1
    · linear_combination Q * geom_sum_mul Q r + h₁
    · linear_combination (1 + Q) * geom_sum_mul Q (r + 1) + (1 + Q) * h₂

/-- **The value at `Q = 1`**: `a_d(1) = (d + 1) / (2 * d)`. -/
@[simp]
theorem wenzlParam_one (d : ℤ) : wenzlParam d (1 : K) = (d + 1) / (2 * d) := by
  obtain ⟨r, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · simp only [wenzlParam_natCast, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    push_cast
    ring_nf
  · rcases r with _ | r
    · simp
    simp only [wenzlParam_neg_natCast, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one,
      Nat.add_sub_cancel, one_mul]
    rw [← neg_div_neg_eq]
    push_cast
    ring_nf

/-! ### Symmetries -/

/-- **The complement identity** `a_d(Q) + a_(-d)(Q) = 1`, whenever the common denominator
`(1 + Q) * [|d|]_Q` is nonzero. -/
theorem wenzlParam_add_wenzlParam_neg {Q : K} {d : ℤ}
    (h : (1 + Q) * ∑ i ∈ range d.natAbs, Q ^ i ≠ 0) :
    wenzlParam d Q + wenzlParam (-d) Q = 1 := by
  suffices ∀ r : ℕ, (1 + Q) * ∑ i ∈ range r, Q ^ i ≠ 0 →
      wenzlParam (r : ℤ) Q + wenzlParam (-(r : ℤ)) Q = 1 by
    obtain ⟨r, rfl | rfl⟩ := Int.eq_nat_or_neg d
    · exact this r (by simpa using h)
    · rw [neg_neg, add_comm]
      exact this r (by simpa using h)
  intro r hr
  rcases r with _ | r
  · simp at hr
  rw [wenzlParam_natCast, wenzlParam_neg_natCast, Nat.add_sub_cancel, ← add_div,
    div_eq_one_iff_eq hr]
  linear_combination geom_sum_succ (x := Q) (n := r + 1) - geom_sum_succ (x := Q) (n := r)

/-- **The inversion symmetry** `a_d(Q⁻¹) = a_d(Q)`: the parameters are unchanged by the change of
root `Q ↦ Q⁻¹`. -/
@[simp]
theorem wenzlParam_inv (d : ℤ) (Q : K) : wenzlParam d Q⁻¹ = wenzlParam d Q := by
  rcases eq_or_ne Q 0 with rfl | hQ₀
  · rw [inv_zero]
  rcases eq_or_ne Q 1 with rfl | hQ₁
  · rw [inv_one]
  rw [wenzlParam_eq_div (inv_ne_zero hQ₀) (inv_ne_one.2 hQ₁), wenzlParam_eq_div hQ₀ hQ₁, inv_zpow,
    inv_zpow, zpow_add_one₀ hQ₀]
  have hy : Q ^ d ≠ 0 := zpow_ne_zero d hQ₀
  generalize Q ^ d = y at hy ⊢
  -- Multiply the numerator and denominator on the left by `y * Q`.
  conv_lhs => rw [← mul_div_mul_left _ _ (mul_ne_zero hy hQ₀)]
  rw [← neg_div_neg_eq]
  congr 1 <;> field_simp <;> ring

/-- **Periodicity at a root of unity.** If `Q ^ l = 1` and `Q ≠ 1`, then `a_(d + l)(Q) = a_d(Q)`. In
particular `a_(l - 2)(Q) = a_(-2)(Q)`, the Jones parameter. -/
theorem wenzlParam_add_of_pow_eq_one {Q : K} (hQ₁ : Q ≠ 1) {l : ℕ} (hl : Q ^ l = 1) (d : ℤ) :
    wenzlParam (d + l) Q = wenzlParam d Q := by
  rcases l.eq_zero_or_pos with rfl | hl₀
  · simp
  have hQ₀ : Q ≠ 0 := by
    rintro rfl
    simp [zero_pow hl₀.ne'] at hl
  have h : Q ^ (l : ℤ) = 1 := by rw [zpow_natCast, hl]
  rw [wenzlParam_eq_div hQ₀ hQ₁, wenzlParam_eq_div hQ₀ hQ₁, add_right_comm d,
    zpow_add₀ hQ₀ (d + 1) l, zpow_add₀ hQ₀ d l, h, mul_one, mul_one]

/-- `wenzlParam` commutes with every ring homomorphism between fields. -/
theorem map_wenzlParam {L F : Type*} [Field L] [FunLike F K L] [RingHomClass F K L] (f : F)
    (d : ℤ) (Q : K) : f (wenzlParam d Q) = wenzlParam d (f Q) := by
  obtain ⟨r, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · simp [wenzlParam_natCast]
  · simp [wenzlParam_neg_natCast]

/-! ### Scalar values, the Jones parameter, and the interval boundary relation -/

/-- The scalar endpoint value `a_(-1)(Q) = 0`. -/
@[simp]
theorem wenzlParam_neg_one (Q : K) : wenzlParam (-1) Q = 0 := by
  simpa using wenzlParam_neg_natCast 1 Q

/-- The scalar endpoint value `a_1(Q) = 1`, whenever `1 + Q ≠ 0`. -/
theorem wenzlParam_one_left {Q : K} (hQ : 1 + Q ≠ 0) : wenzlParam 1 Q = 1 := by
  have h := wenzlParam_natCast 1 Q
  simp only [Nat.cast_one, sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one,
    mul_one] at h
  rw [h, div_self hQ]

/-- At `Q = 0`, `a_r(0) = 1` for every positive natural `r`. -/
@[simp]
theorem wenzlParam_natCast_zero {r : ℕ} (hr : r ≠ 0) : wenzlParam (r : ℤ) (0 : K) = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  rw [wenzlParam_natCast]
  simp [sum_range_succ']

/-- At `Q = 0`, `a_(-r)(0) = 0` for every natural `r`. -/
@[simp]
theorem wenzlParam_neg_natCast_zero (r : ℕ) : wenzlParam (-(r : ℤ)) (0 : K) = 0 := by
  simp [wenzlParam_neg_natCast]

/-- The parameter `a_(-2)(Q) = Q / (1 + Q) ^ 2`. -/
theorem wenzlParam_neg_two (Q : K) : wenzlParam (-2) Q = Q / (1 + Q) ^ 2 := by
  have h := wenzlParam_neg_natCast 2 Q
  push_cast at h
  rw [h]
  simp [sum_range_succ, sq]

/-- The complementary Jones parameter `a_2(Q) = (1 + Q + Q ^ 2) / (1 + Q) ^ 2`. -/
theorem wenzlParam_two (Q : K) :
    wenzlParam 2 Q = (1 + Q + Q ^ 2) / (1 + Q) ^ 2 := by
  have h := wenzlParam_natCast 2 Q
  push_cast at h
  rw [h]
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one, sq]

/-- **The Jones parameter.** At `Q = q ^ 2`, `a_(-2)(Q) = (q + q⁻¹)⁻²`, the parameter `τ` of the
Jones quotient. -/
theorem wenzlParam_neg_two_sq (q : K) :
    wenzlParam (-2) (q ^ 2) = ((q + q⁻¹) ^ 2)⁻¹ := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [wenzlParam_neg_two]
  rw [wenzlParam_neg_two, show q + q⁻¹ = (1 + q ^ 2) / q by field_simp; ring, div_pow, inv_div]

/-- **Factorization of the boundary defect `a_(-2)(Q) - η * (1 - η)`.** When `1 + Q ≠ 0`,
`a_(-2)(Q) - η * (1 - η) = (η - 1 / (1 + Q)) * (η - Q / (1 + Q))`. -/
theorem wenzlParam_neg_two_sub_mul_one_sub {Q : K} (hQ : 1 + Q ≠ 0) (η : K) :
    wenzlParam (-2) Q - η * (1 - η) = (η - 1 / (1 + Q)) * (η - Q / (1 + Q)) := by
  rw [wenzlParam_neg_two]
  field_simp
  ring

/-- **Boundary characterization `τ = η * (1 - η)`.** When `1 + Q ≠ 0`, the Jones parameter
`a_(-2)(Q)` equals `η * (1 - η)` if and only if `η = 1 / (1 + Q)` or `η = Q / (1 + Q)`. -/
theorem wenzlParam_neg_two_eq_mul_one_sub_iff {Q η : K} (hQ : 1 + Q ≠ 0) :
    wenzlParam (-2) Q = η * (1 - η) ↔ η = 1 / (1 + Q) ∨ η = Q / (1 + Q) := by
  rw [← sub_eq_zero, wenzlParam_neg_two_sub_mul_one_sub hQ, mul_eq_zero, sub_eq_zero, sub_eq_zero]

private theorem wenzlParam_neg_two_sub_mul_one_sub_eq_min_max [LinearOrder K] {Q : K}
    (hQ : 1 + Q ≠ 0) (η : K) :
    wenzlParam (-2) Q - η * (1 - η) =
      (η - min (1 / (1 + Q)) (Q / (1 + Q))) * (η - max (1 / (1 + Q)) (Q / (1 + Q))) := by
  rw [wenzlParam_neg_two_sub_mul_one_sub hQ]
  rcases le_total (1 / (1 + Q)) (Q / (1 + Q)) with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, mul_comm]

/-- **Closed-interval characterization `τ ≤ η * (1 - η)`.** Over a linear ordered field, when
`1 + Q ≠ 0`, the inequality `a_(-2)(Q) ≤ η * (1 - η)` holds if and only if `η` lies in the closed
interval between `1 / (1 + Q)` and `Q / (1 + Q)`. -/
theorem wenzlParam_neg_two_le_mul_one_sub_iff [LinearOrder K] [IsStrictOrderedRing K] {Q η : K}
    (hQ : 1 + Q ≠ 0) :
    wenzlParam (-2) Q ≤ η * (1 - η) ↔
      η ∈ Set.Icc (min (1 / (1 + Q)) (Q / (1 + Q))) (max (1 / (1 + Q)) (Q / (1 + Q))) := by
  rw [← sub_nonpos, wenzlParam_neg_two_sub_mul_one_sub_eq_min_max hQ, mul_nonpos_iff,
    sub_nonneg, sub_nonpos, sub_nonpos, sub_nonneg, Set.mem_Icc]
  exact ⟨fun h ↦ h.elim id fun ⟨h1, h2⟩ ↦ ⟨min_le_max.trans h2, h1.trans min_le_max⟩, Or.inl⟩

/-- **Open-interval characterization `τ < η * (1 - η)`.** Over a linear ordered field, when
`1 + Q ≠ 0`, the strict inequality `a_(-2)(Q) < η * (1 - η)` holds if and only if `η` lies in the
open interval between `1 / (1 + Q)` and `Q / (1 + Q)`. -/
theorem wenzlParam_neg_two_lt_mul_one_sub_iff [LinearOrder K] [IsStrictOrderedRing K] {Q η : K}
    (hQ : 1 + Q ≠ 0) :
    wenzlParam (-2) Q < η * (1 - η) ↔
      η ∈ Set.Ioo (min (1 / (1 + Q)) (Q / (1 + Q))) (max (1 / (1 + Q)) (Q / (1 + Q))) := by
  rw [← sub_neg, wenzlParam_neg_two_sub_mul_one_sub_eq_min_max hQ, mul_neg_iff,
    sub_pos, sub_neg, sub_neg, sub_pos, Set.mem_Ioo]
  exact ⟨fun h ↦ h.elim id fun ⟨h1, h2⟩ ↦ absurd (h2.trans h1) (not_lt_of_ge min_le_max), Or.inl⟩

/-! ### Geometric weights -/

/-- **The second elementary symmetric function of geometric weights.** For the normalized weights
`p_i = Q ^ i / [r]_Q`, `i < r`, the sum `∑ i < j, p_i * p_j` is `a_(-r)(Q)`, provided
`1 + Q ≠ 0`. -/
theorem wenzlParam_neg_natCast_eq_sum {Q : K} (hQ : 1 + Q ≠ 0) (r : ℕ) :
    wenzlParam (-(r : ℤ)) Q = ∑ j ∈ range r, ∑ i ∈ range j,
      Q ^ i / (∑ k ∈ range r, Q ^ k) * (Q ^ j / ∑ k ∈ range r, Q ^ k) := by
  -- The unnormalized identity `(1 + Q) * ∑ i < j < r, Q ^ i * Q ^ j = Q * [r]_Q * [r - 1]_Q`.
  have key : ∀ r : ℕ, (1 + Q) * ∑ j ∈ range (r + 1), ∑ i ∈ range j, Q ^ i * Q ^ j =
      Q * (∑ i ∈ range (r + 1), Q ^ i) * ∑ i ∈ range r, Q ^ i := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [sum_range_succ _ (r + 1), mul_add, ih, ← sum_mul]
      linear_combination (-Q * ∑ i ∈ range (r + 1), Q ^ i) *
        (sum_range_succ (fun i ↦ Q ^ i) (r + 1) + sum_range_succ (fun i ↦ Q ^ i) r)
  simp_rw [div_mul_div_comm, ← sum_div]
  rw [wenzlParam_neg_natCast]
  rcases r with _ | r
  · simp
  rw [Nat.add_sub_cancel]
  rcases eq_or_ne (∑ k ∈ range (r + 1), Q ^ k) 0 with hZ | hZ
  · simp [hZ]
  rw [eq_div_iff (mul_ne_zero hZ hZ), div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hQ hZ)]
  linear_combination -(∑ k ∈ range (r + 1), Q ^ k) * key r

end TauCeti
