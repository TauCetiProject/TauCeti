/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Wenzl's discrete Markov trace parameters

For an integer `d ≠ 0` and a parameter `Q`, Wenzl's discrete trace parameter is

`a_d(Q) = (1 - Q ^ (d + 1)) / ((1 + Q) * (1 - Q ^ d))`,

with the removable value `a_d(1) = (d + 1) / (2 * d)`. In Wenzl's classification of positive
Markov traces on the type-A Hecke algebras, which is not proved here, the projection parameters at
`Q = q ^ 2 > 0` form a closed interval together with the discrete values `a_d(Q)`, and at the
roots of unity `Q = exp (± 2 π i / l)` they are the values `a_k(Q)`, `1 ≤ k ≤ l - 1`. This file
develops the parameters themselves, characterizes the closed and open real interval at `Q > -1` by
the quadratic relation `a_(-2)(Q) ≤ η * (1 - η)`, and expresses `a_(-r)(Q)` in terms of geometric
weights. (The identification with the Ocneanu trace of the geometric atomic model is in
`TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Geometric`.)

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
* `TauCeti.wenzlParam_one` and `TauCeti.tendsto_one_sub_zpow_div_nhdsNE_one`: the value
  `(d + 1) / (2 * d)` at `Q = 1`, and the closed form tends to it as `Q → 1`.
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
* `TauCeti.wenzlParam_exp_two_mul`, `TauCeti.wenzlParam_exp_neg_two_mul`,
  `TauCeti.wenzlParam_real_exp_two_mul`, `TauCeti.wenzlParam_real_exp_neg_two_mul`, and
  `TauCeti.wenzlParam_neg_two_exp_neg_two_mul`:
  `a_k(exp (± 2 θ)) = sinh ((k + 1) θ) / (2 cosh θ sinh (k θ))` and
  `a_(-2)(exp (± 2 θ)) = (4 cosh² θ)⁻¹`.
* `TauCeti.wenzlParam_exp_mul_I`: `a_k(exp (2 θ i)) = sin ((k + 1) θ) / (2 cos θ sin (k θ))`;
  `TauCeti.wenzlParam_exp_two_pi_mul_I_div`, `TauCeti.wenzlParam_neg_exp_two_pi_mul_I_div`,
  `TauCeti.wenzlParam_sub_exp_two_pi_mul_I_div`,
  `TauCeti.wenzlParam_exp_two_pi_mul_I_div_two_mul`, and
  `TauCeti.exists_mem_Ioo_wenzlParam_exp_two_pi_mul_I_div_iff` give the real values, complementary
  pairs `a_(l - k) = a_(-k) = 1 - a_k`, middle value `a_m = 1 / 2`, and separation of the scalar
  endpoints `k ∈ {1, l - 1}` (all of `l = 3`) from the `(0, 1)` interior cases `2 ≤ k ≤ l - 2` at
  `exp (± 2 π i / l)`.
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

/-! ### Continuity and the removable value at `Q = 1` -/

section Topology

open Filter Topology

variable [TopologicalSpace K] [IsTopologicalDivisionRing K]

/-- `a_d` is continuous at every `Q` where its denominator `(1 + Q) * [|d|]_Q` is nonzero. -/
theorem continuousAt_wenzlParam {d : ℤ} {Q : K} (h : (1 + Q) * ∑ i ∈ range d.natAbs, Q ^ i ≠ 0) :
    ContinuousAt (wenzlParam d) Q := by
  obtain ⟨r, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · rw [funext (wenzlParam_natCast r)]
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using h)
  · rw [funext (wenzlParam_neg_natCast r)]
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using h)

/-- **The removable limit.** As `Q → 1`, the closed form
`(1 - Q ^ (d + 1)) / ((1 + Q) * (1 - Q ^ d))` tends to `a_d(1) = (d + 1) / (2 * d)`. -/
theorem tendsto_one_sub_zpow_div_nhdsNE_one [T1Space K] [CharZero K] {d : ℤ} (hd : d ≠ 0) :
    Tendsto (fun Q : K ↦ (1 - Q ^ (d + 1)) / ((1 + Q) * (1 - Q ^ d))) (𝓝[≠] 1)
      (𝓝 ((d + 1) / (2 * d))) := by
  rw [← wenzlParam_one]
  have hc : ContinuousAt (wenzlParam d) (1 : K) :=
    continuousAt_wenzlParam (by simp [one_add_one_eq_two, hd])
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_ne_nhds (one_ne_zero (α := K)))] with Q hQ₁ hQ₀
  exact wenzlParam_eq_div hQ₀ hQ₁ d

end Topology

/-! ### Roots of unity -/

section RootOfUnity

open Complex
open scoped Real

/-- **The trigonometric form.** At `Q = exp (2 θ i)`,
`a_k(Q) = sin ((k + 1) θ) / (2 * cos θ * sin (k θ))`, whenever `cos θ ≠ 0` and `sin (k θ) ≠ 0`. -/
theorem wenzlParam_exp_mul_I (k : ℤ) {θ : ℂ} (hθ : cos θ ≠ 0) (hk : sin (k * θ) ≠ 0) :
    wenzlParam k (exp (2 * θ * I)) = sin ((k + 1) * θ) / (2 * cos θ * sin (k * θ)) := by
  have e₁ (x : ℂ) : exp (-x * I) * exp (x * I) = 1 := by rw [← exp_add]; simp
  have e₂ (x : ℂ) : exp (x * I) * exp (x * I) = exp (2 * x * I) := by rw [← exp_add]; ring_nf
  -- `1 - exp (2 x i) = -i * (2 * sin x) * exp (x i)` and `1 + exp (2 x i) = 2 * cos x * exp (x i)`.
  have one_sub_exp (x : ℂ) : 1 - exp (2 * x * I) = -I * (2 * sin x) * exp (x * I) := by
    rw [two_sin]
    linear_combination (-1) * e₁ x + e₂ x + (exp (-x * I) - exp (x * I)) * exp (x * I) * I_sq
  have one_add_exp (x : ℂ) : 1 + exp (2 * x * I) = 2 * cos x * exp (x * I) := by
    simpa only [mul_assoc, cosh_mul_I] using one_add_exp_two_mul (x * I)
  have hpow (n : ℤ) : 1 - exp (2 * θ * I) ^ n = -I * (2 * sin (n * θ)) * exp (n * θ * I) := by
    rw [← exp_intCast_mul, ← one_sub_exp]
    ring_nf
  have hk' : 1 - exp (2 * θ * I) ^ k ≠ 0 := by
    rw [hpow]
    simp [hk, exp_ne_zero, I_ne_zero]
  have hQ₁ : exp (2 * θ * I) ≠ 1 := by
    rintro h
    simp [h] at hk'
  have hexp : exp ((k + 1) * θ * I) = exp (θ * I) * exp (k * θ * I) := by
    rw [← exp_add]
    ring_nf
  rw [wenzlParam_eq_div (exp_ne_zero _) hQ₁, hpow, hpow, one_add_exp]
  push_cast
  rw [hexp]
  field_simp [exp_ne_zero, I_ne_zero]

/-- **The hyperbolic form at `exp (2 θ)`.** At `Q = exp (2 * θ)`,
`a_k(Q) = sinh ((k + 1) * θ) / (2 * cosh θ * sinh (k * θ))`, whenever `cosh θ ≠ 0` and
`sinh (k * θ) ≠ 0`. -/
theorem wenzlParam_exp_two_mul (k : ℤ) {θ : ℂ} (hθ : cosh θ ≠ 0) (hk : sinh (k * θ) ≠ 0) :
    wenzlParam k (exp (2 * θ)) = sinh ((k + 1) * θ) / (2 * cosh θ * sinh (k * θ)) := by
  have hcos : cos (-(θ * I)) ≠ 0 := by simpa [cos_mul_I] using hθ
  have hsin : sin ((k : ℂ) * -(θ * I)) ≠ 0 := by
    rw [mul_neg, ← mul_assoc, sin_neg, sin_mul_I, neg_ne_zero]
    exact mul_ne_zero hk I_ne_zero
  have h := wenzlParam_exp_mul_I k hcos hsin
  have hphase : 2 * -(θ * I) * I = 2 * θ := by linear_combination -2 * θ * I_sq
  rw [hphase, cos_neg, cos_mul_I, mul_neg, mul_neg, ← mul_assoc, ← mul_assoc, sin_neg, sin_neg,
    sin_mul_I, sin_mul_I] at h
  rw [h]
  field_simp [I_ne_zero]

/-- **The hyperbolic form at `exp (-2 θ)`.** At `Q = exp (-2 * θ)`,
`a_k(Q) = sinh ((k + 1) * θ) / (2 * cosh θ * sinh (k * θ))`, whenever `cosh θ ≠ 0` and
`sinh (k * θ) ≠ 0`. -/
theorem wenzlParam_exp_neg_two_mul (k : ℤ) {θ : ℂ} (hθ : cosh θ ≠ 0) (hk : sinh (k * θ) ≠ 0) :
    wenzlParam k (exp (-2 * θ)) = sinh ((k + 1) * θ) / (2 * cosh θ * sinh (k * θ)) := by
  rw [neg_mul, exp_neg, wenzlParam_inv, wenzlParam_exp_two_mul k hθ hk]

/-- **The real hyperbolic form at `Real.exp (2 θ)`.** For `k ≠ 0` and real `θ ≠ 0`,
`a_k(exp (2 * θ)) = sinh ((k + 1) * θ) / (2 * cosh θ * sinh (k * θ))`. -/
theorem wenzlParam_real_exp_two_mul {k : ℤ} (hk : k ≠ 0) {θ : ℝ} (hθ : θ ≠ 0) :
    wenzlParam k (Real.exp (2 * θ)) =
      Real.sinh ((k + 1) * θ) / (2 * Real.cosh θ * Real.sinh (k * θ)) := by
  apply Complex.ofReal_injective
  have hs : sinh ((k : ℂ) * θ) ≠ 0 := by
    simpa using sinh_ofReal_ne_zero.2 (mul_ne_zero (Int.cast_ne_zero.2 hk) hθ)
  rw [← Complex.ofRealHom_eq_coe, map_wenzlParam]
  simpa using wenzlParam_exp_two_mul k (cosh_ofReal_ne_zero θ) hs

/-- **The real hyperbolic form at `Real.exp (-2 θ)`.** For `k ≠ 0` and real `θ ≠ 0`,
`a_k(exp (-2 * θ)) = sinh ((k + 1) * θ) / (2 * cosh θ * sinh (k * θ))`. -/
theorem wenzlParam_real_exp_neg_two_mul {k : ℤ} (hk : k ≠ 0) {θ : ℝ} (hθ : θ ≠ 0) :
    wenzlParam k (Real.exp (-2 * θ)) =
      Real.sinh ((k + 1) * θ) / (2 * Real.cosh θ * Real.sinh (k * θ)) := by
  rw [neg_mul, Real.exp_neg, wenzlParam_inv, wenzlParam_real_exp_two_mul hk hθ]

/-- **The hyperbolic Jones parameter at `exp (2 θ)`.** For every `θ : ℂ`,
`a_(-2)(exp (2 * θ)) = (4 * cosh θ ^ 2)⁻¹`. -/
theorem wenzlParam_neg_two_exp_two_mul (θ : ℂ) :
    wenzlParam (-2) (exp (2 * θ)) = (4 * cosh θ ^ 2)⁻¹ := by
  have e₂ : exp θ * exp θ = exp (2 * θ) := by rw [← exp_add]; ring_nf
  have hsq : (1 + exp (2 * θ)) ^ 2 = exp (2 * θ) * (4 * cosh θ ^ 2) := by
    rw [one_add_exp_two_mul]
    linear_combination 4 * cosh θ ^ 2 * e₂
  rw [wenzlParam_neg_two, hsq, div_mul_eq_div_div, div_self (exp_ne_zero _), one_div]

/-- **The Jones parameter on the unit circle.** At `Q = exp (2 θ i)`,
`a_(-2)(Q) = (4 * cos θ ^ 2)⁻¹` for every `θ : ℂ`. -/
theorem wenzlParam_neg_two_exp_mul_I (θ : ℂ) :
    wenzlParam (-2) (exp (2 * θ * I)) = (4 * cos θ ^ 2)⁻¹ := by
  simpa only [mul_assoc, cosh_mul_I] using wenzlParam_neg_two_exp_two_mul (θ * I)

/-- **The hyperbolic Jones parameter at `exp (-2 θ)`.** For every `θ : ℂ`,
`a_(-2)(exp (-2 * θ)) = (4 * cosh θ ^ 2)⁻¹`. -/
theorem wenzlParam_neg_two_exp_neg_two_mul (θ : ℂ) :
    wenzlParam (-2) (exp (-2 * θ)) = (4 * cosh θ ^ 2)⁻¹ := by
  rw [neg_mul, exp_neg, wenzlParam_inv, wenzlParam_neg_two_exp_two_mul]

/-- **The real hyperbolic Jones parameter at `Real.exp (2 θ)`.** For every `θ : ℝ`,
`a_(-2)(exp (2 * θ)) = (4 * cosh θ ^ 2)⁻¹`. -/
theorem wenzlParam_neg_two_real_exp_two_mul (θ : ℝ) :
    wenzlParam (-2) (Real.exp (2 * θ)) = (4 * Real.cosh θ ^ 2)⁻¹ := by
  apply Complex.ofReal_injective
  rw [← Complex.ofRealHom_eq_coe, map_wenzlParam]
  simpa using wenzlParam_neg_two_exp_two_mul (θ : ℂ)

/-- **The real hyperbolic Jones parameter at `Real.exp (-2 θ)`.** For every `θ : ℝ`,
`a_(-2)(exp (-2 * θ)) = (4 * cosh θ ^ 2)⁻¹`. -/
theorem wenzlParam_neg_two_real_exp_neg_two_mul (θ : ℝ) :
    wenzlParam (-2) (Real.exp (-2 * θ)) = (4 * Real.cosh θ ^ 2)⁻¹ := by
  rw [neg_mul, Real.exp_neg, wenzlParam_inv, wenzlParam_neg_two_real_exp_two_mul]

private theorem cos_pi_div_natCast_pos {l : ℕ} (hl : 3 ≤ l) : 0 < Real.cos (π / l) :=
  cos_pi_div_pos (by exact_mod_cast (by omega : 2 < l))

private theorem sin_natCast_mul_pi_div_natCast_pos {l k : ℕ} (hk₀ : 0 < k) (hkl : k < l) :
    0 < Real.sin (k * π / l) :=
  sin_mul_pi_div_pos (Nat.cast_pos.2 hk₀) (Nat.cast_lt.2 hkl)

private theorem two_mul_pi_div_mul_I (l : ℕ) : 2 * (π / (l : ℂ)) * I = 2 * π * I / l := by
  ring

private theorem isPrimitiveRoot_exp_two_pi_mul_I_div {l : ℕ} (hl : 3 ≤ l) :
    IsPrimitiveRoot (exp (2 * π * I / l)) l :=
  Complex.isPrimitiveRoot_exp l (by omega)

private theorem one_add_exp_two_pi_mul_I_div_ne_zero {l : ℕ} (hl : 3 ≤ l) :
    1 + exp (2 * π * I / l) ≠ 0 := by
  intro h0
  have hζ : exp (2 * π * I / l) = -1 := eq_neg_of_add_eq_zero_right h0
  have hsq : exp (2 * π * I / l) ^ 2 = 1 := by rw [hζ]; norm_num
  exact (isPrimitiveRoot_exp_two_pi_mul_I_div hl).pow_ne_one_of_pos_of_lt two_ne_zero (by omega) hsq

/-- **The values at the roots of unity.** For `l ≥ 3` and `0 < k < l`, at `Q = exp (2 π i / l)`,
`a_k(Q) = sin ((k + 1) π / l) / (2 * cos (π / l) * sin (k π / l))`, a real number. -/
theorem wenzlParam_exp_two_pi_mul_I_div {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k) (hkl : k < l) :
    wenzlParam (k : ℤ) (exp (2 * π * I / l)) =
      ↑(Real.sin ((k + 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l))) := by
  have hcos : 0 < Real.cos (π / l) := cos_pi_div_natCast_pos hl
  have hsin : 0 < Real.sin (k * π / l) := sin_natCast_mul_pi_div_natCast_pos hk₀ hkl
  have h := wenzlParam_exp_mul_I k (θ := π / l) (by exact_mod_cast hcos.ne')
    (by rw [Int.cast_natCast, ← mul_div_assoc]; exact_mod_cast hsin.ne')
  rw [two_mul_pi_div_mul_I] at h
  rw [h]
  push_cast
  ring_nf

/-- The values at the conjugate roots of unity `Q = exp (-2 π i / l)` agree with those at
`exp (2 π i / l)`. -/
theorem wenzlParam_exp_neg_two_pi_mul_I_div {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k) (hkl : k < l) :
    wenzlParam (k : ℤ) (exp (-(2 * π * I / l))) =
      ↑(Real.sin ((k + 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l))) := by
  rw [exp_neg, wenzlParam_inv, wenzlParam_exp_two_pi_mul_I_div hl hk₀ hkl]

/-- **The negative-index values at the roots of unity.** For `l ≥ 3` and `0 < k < l`, at
`Q = exp (2 π i / l)`, `a_(-k)(Q) = sin ((k - 1) π / l) / (2 * cos (π / l) * sin (k π / l))`. -/
theorem wenzlParam_neg_exp_two_pi_mul_I_div {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k) (hkl : k < l) :
    wenzlParam (-(k : ℤ)) (exp (2 * π * I / l)) =
      ↑(Real.sin ((k - 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l))) := by
  have hcos : 0 < Real.cos (π / l) := cos_pi_div_natCast_pos hl
  have hsin : 0 < Real.sin (k * π / l) := sin_natCast_mul_pi_div_natCast_pos hk₀ hkl
  have h := wenzlParam_exp_mul_I (-(k : ℤ)) (θ := π / l) (by exact_mod_cast hcos.ne')
    (by rw [Int.cast_neg, Int.cast_natCast, neg_mul, sin_neg, neg_ne_zero, ← mul_div_assoc]
        exact_mod_cast hsin.ne')
  have hnum : (-(k : ℂ) + 1) * (π / l) = -(((k : ℂ) - 1) * π / l) := by ring
  have hden : -(k : ℂ) * (π / l) = -(k * π / l) := by ring
  rw [two_mul_pi_div_mul_I, Int.cast_neg, Int.cast_natCast, hnum, hden, sin_neg, sin_neg] at h
  rw [h]
  push_cast
  field_simp

/-- The negative-index values at `Q = exp (-2 π i / l)` agree with those at `exp (2 π i / l)`. -/
theorem wenzlParam_neg_exp_neg_two_pi_mul_I_div {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    wenzlParam (-(k : ℤ)) (exp (-(2 * π * I / l))) =
      ↑(Real.sin ((k - 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l))) := by
  rw [exp_neg, wenzlParam_inv, wenzlParam_neg_exp_two_pi_mul_I_div hl hk₀ hkl]

/-- **Complement identity at the roots of unity.** For `l ≥ 3` and `0 < k < l`, at
`Q = exp (2 π i / l)`, `a_k(Q) + a_(-k)(Q) = 1`. -/
theorem wenzlParam_add_wenzlParam_neg_exp_two_pi_mul_I_div {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    wenzlParam (k : ℤ) (exp (2 * π * I / l)) + wenzlParam (-(k : ℤ)) (exp (2 * π * I / l)) = 1 := by
  have hζ := isPrimitiveRoot_exp_two_pi_mul_I_div hl
  have hsum : ∑ i ∈ range k, exp (2 * π * I / l) ^ i ≠ 0 := by
    intro h0
    have hgeom := geom_sum_mul (exp (2 * π * I / l)) k
    rw [h0, zero_mul] at hgeom
    exact sub_ne_zero.2 (hζ.pow_ne_one_of_pos_of_lt hk₀.ne' hkl) hgeom.symm
  have hden : (1 + exp (2 * π * I / l)) * ∑ i ∈ range (k : ℤ).natAbs, exp (2 * π * I / l) ^ i ≠ 0 :=
    mul_ne_zero (one_add_exp_two_pi_mul_I_div_ne_zero hl) (by simpa using hsum)
  exact wenzlParam_add_wenzlParam_neg hden

/-- **Complementary index `l - k` at the roots of unity.** For `l ≥ 3` and `k ≤ l`, at
`Q = exp (2 π i / l)`, `a_(l - k)(Q) = a_(-k)(Q)`. -/
theorem wenzlParam_sub_exp_two_pi_mul_I_div {l k : ℕ} (hl : 3 ≤ l) (hkl : k ≤ l) :
    wenzlParam ((l - k : ℕ) : ℤ) (exp (2 * π * I / l)) =
      wenzlParam (-(k : ℤ)) (exp (2 * π * I / l)) := by
  have hζ := isPrimitiveRoot_exp_two_pi_mul_I_div hl
  rw [Nat.cast_sub hkl, sub_eq_neg_add]
  exact wenzlParam_add_of_pow_eq_one (hζ.ne_one (by omega)) hζ.pow_eq_one (-(k : ℤ))

/-- At `Q = exp (-2 π i / l)`, `a_(l - k)(Q) = a_(-k)(Q)` for `l ≥ 3` and `k ≤ l`. -/
theorem wenzlParam_sub_exp_neg_two_pi_mul_I_div {l k : ℕ} (hl : 3 ≤ l) (hkl : k ≤ l) :
    wenzlParam ((l - k : ℕ) : ℤ) (exp (-(2 * π * I / l))) =
      wenzlParam (-(k : ℤ)) (exp (-(2 * π * I / l))) := by
  rw [exp_neg, wenzlParam_inv, wenzlParam_inv, wenzlParam_sub_exp_two_pi_mul_I_div hl hkl]

/-- **The middle value.** For `l = 2 * m ≥ 4`, at `Q = exp (2 π i / l)`, `a_m(Q) = 1 / 2`. -/
theorem wenzlParam_exp_two_pi_mul_I_div_two_mul {m : ℕ} (hm : 2 ≤ m) :
    wenzlParam (m : ℤ) (exp (2 * π * I / (2 * m))) = 1 / 2 := by
  have h := wenzlParam_exp_two_pi_mul_I_div (l := 2 * m) (k := m) (by omega) (by omega) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  have hcos : Real.cos (π / (2 * m)) ≠ 0 := by
    simpa using (cos_pi_div_natCast_pos (by omega : 3 ≤ 2 * m)).ne'
  -- With `θ = π / (2 * m)`: `sin ((m + 1) θ) = cos θ` and `sin (m θ) = 1`.
  have h₁ : (m + 1) * π / (2 * m) = π / (2 * m) + π / 2 := by field_simp; ring
  have h₂ : m * π / (2 * m) = π / 2 := by field_simp
  rw [h, h₁, h₂, Real.sin_add_pi_div_two, Real.sin_pi_div_two, mul_one,
    div_mul_cancel_right₀ hcos]
  norm_num

/-- At `Q = exp (2 π i / l)` with `l ≥ 3`, the first positive parameter `a_1(Q)` is `1`. -/
theorem wenzlParam_one_exp_two_pi_mul_I_div {l : ℕ} (hl : 3 ≤ l) :
    wenzlParam 1 (exp (2 * π * I / l)) = 1 :=
  wenzlParam_one_left (one_add_exp_two_pi_mul_I_div_ne_zero hl)

/-- At `Q = exp (2 π i / l)` with `l ≥ 3`, the last parameter `a_(l - 1)(Q)` is `0`. -/
theorem wenzlParam_sub_one_exp_two_pi_mul_I_div {l : ℕ} (hl : 3 ≤ l) :
    wenzlParam ((l - 1 : ℕ) : ℤ) (exp (2 * π * I / l)) = 0 := by
  rw [wenzlParam_sub_exp_two_pi_mul_I_div hl (by omega), Nat.cast_one, wenzlParam_neg_one]

/-- At `Q = exp (2 π i / l)` with `l ≥ 3`, `a_(-(l - 1))(Q) = 1`. -/
theorem wenzlParam_neg_sub_one_exp_two_pi_mul_I_div {l : ℕ} (hl : 3 ≤ l) :
    wenzlParam (-((l - 1 : ℕ) : ℤ)) (exp (2 * π * I / l)) = 1 := by
  have h := wenzlParam_add_wenzlParam_neg_exp_two_pi_mul_I_div (l := l) (k := l - 1) hl
    (by omega) (by omega)
  rwa [wenzlParam_sub_one_exp_two_pi_mul_I_div hl, zero_add] at h

/-- **Strict `(0, 1)` interior values for `2 ≤ k ≤ l - 2` (`l ≥ 4`).** When `2 ≤ k` and
`k + 2 ≤ l`, `a_k(exp (2 π i / l))` is a real number `η ∈ (0, 1)`, and `a_(-k)(exp (2 π i / l))` is
`1 - η ∈ (0, 1)`. -/
theorem exists_mem_Ioo_wenzlParam_exp_two_pi_mul_I_div {l k : ℕ} (hk : 2 ≤ k) (hkl : k + 2 ≤ l) :
    ∃ η ∈ Set.Ioo (0 : ℝ) 1,
      wenzlParam (k : ℤ) (exp (2 * π * I / l)) = η ∧
        wenzlParam (-(k : ℤ)) (exp (2 * π * I / l)) = ↑(1 - η) := by
  have hl : 3 ≤ l := by omega
  have hk₀ : 0 < k := by omega
  have hkl₀ : k < l := by omega
  have hcos : 0 < Real.cos (π / l) := cos_pi_div_natCast_pos hl
  have hsin_k : 0 < Real.sin (k * π / l) := sin_natCast_mul_pi_div_natCast_pos hk₀ hkl₀
  have hsin_add : 0 < Real.sin ((k + 1) * π / l) := by
    simpa using sin_natCast_mul_pi_div_natCast_pos (l := l) (k := k + 1) (by omega) (by omega)
  have hsin_sub : 0 < Real.sin ((k - 1) * π / l) := by
    have hk_sub : 1 ≤ k := by omega
    simpa [Nat.cast_sub hk_sub] using
      sin_natCast_mul_pi_div_natCast_pos (l := l) (k := k - 1) (by omega) (by omega)
  set r₁ := Real.sin ((k + 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l))
  set r₂ := Real.sin ((k - 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l))
  have hr₁ : 0 < r₁ := by positivity
  have hr₂ : 0 < r₂ := by positivity
  have hsum_c := wenzlParam_add_wenzlParam_neg_exp_two_pi_mul_I_div hl hk₀ hkl₀
  rw [wenzlParam_exp_two_pi_mul_I_div hl hk₀ hkl₀,
    wenzlParam_neg_exp_two_pi_mul_I_div hl hk₀ hkl₀, ← ofReal_add, ← ofReal_one] at hsum_c
  have hsum : r₁ + r₂ = 1 := Complex.ofReal_injective hsum_c
  have hsub : 1 - r₁ = r₂ := by linarith
  refine ⟨r₁, ⟨hr₁, by linarith⟩, wenzlParam_exp_two_pi_mul_I_div hl hk₀ hkl₀, ?_⟩
  rw [wenzlParam_neg_exp_two_pi_mul_I_div hl hk₀ hkl₀, hsub]

/-- **Characterization of nontrivial root-of-unity parameters.** For `l ≥ 3` and `0 < k < l`,
`a_k(exp (2 π i / l))` lies strictly in `(0, 1)` if and only if `2 ≤ k` and `k + 2 ≤ l` (so in
particular `l ≥ 4`). -/
theorem exists_mem_Ioo_wenzlParam_exp_two_pi_mul_I_div_iff {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    (∃ η ∈ Set.Ioo (0 : ℝ) 1, wenzlParam (k : ℤ) (exp (2 * π * I / l)) = η) ↔
      2 ≤ k ∧ k + 2 ≤ l := by
  refine ⟨fun ⟨η, hη, heq⟩ ↦ ?_, fun ⟨hk, hkl'⟩ ↦ ?_⟩
  · by_contra h
    have hk_end : k = 1 ∨ k = l - 1 := by omega
    rcases hk_end with rfl | rfl
    · rw [Nat.cast_one, wenzlParam_one_exp_two_pi_mul_I_div hl, ← ofReal_one] at heq
      exact hη.2.ne' (Complex.ofReal_injective heq)
    · rw [wenzlParam_sub_one_exp_two_pi_mul_I_div hl, ← ofReal_zero] at heq
      exact hη.1.ne (Complex.ofReal_injective heq)
  · obtain ⟨η, hη, h1, _⟩ := exists_mem_Ioo_wenzlParam_exp_two_pi_mul_I_div hk hkl'
    exact ⟨η, hη, h1⟩

/-- **Characterization of scalar root-of-unity parameters.** For `l ≥ 3` and `0 < k < l`,
`a_k(exp (2 π i / l))` belongs to `{0, 1}` if and only if `k = 1` or `k + 1 = l`. In particular, for
`l = 3` every `0 < k < 3` gives a scalar endpoint `{0, 1}`. -/
theorem wenzlParam_exp_two_pi_mul_I_div_mem_pair_iff {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    wenzlParam (k : ℤ) (exp (2 * π * I / l)) ∈ ({0, 1} : Set ℂ) ↔ k = 1 ∨ k + 1 = l := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hnot
    obtain ⟨η, hη, heq, _⟩ := exists_mem_Ioo_wenzlParam_exp_two_pi_mul_I_div (l := l) (k := k)
      (by omega) (by omega)
    rw [heq, Set.mem_insert_iff, Set.mem_singleton_iff, ← ofReal_zero, ← ofReal_one] at h
    rcases h with h | h
    · exact hη.1.ne' (Complex.ofReal_injective h)
    · exact hη.2.ne (Complex.ofReal_injective h)
  · rcases h with rfl | h
    · simp [wenzlParam_one_exp_two_pi_mul_I_div hl]
    · obtain rfl : k = l - 1 := by omega
      simp [wenzlParam_sub_one_exp_two_pi_mul_I_div hl]

end RootOfUnity

end TauCeti
