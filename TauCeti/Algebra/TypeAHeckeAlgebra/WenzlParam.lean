/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection
public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.GeomSum
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
develops the parameters themselves, and identifies `a_(r + 1)(q ^ 2)` as the projection parameter
of the Ocneanu trace realized by the atomic model on `r + 1` positive letters with geometric
weights.

We define `a_d(Q)` (`TauCeti.wenzlParam`) without division by `1 - Q`: for `d = r ≥ 0` and for
`d = -r`, with `[n]_Q = ∑ i < n, Q ^ i`,

`a_r(Q) = [r + 1]_Q / ((1 + Q) * [r]_Q)` and `a_(-r)(Q) = Q * [r - 1]_Q / ((1 + Q) * [r]_Q)`.

This is a regular function of `Q` wherever `(1 + Q) * [|d|]_Q ≠ 0`, it agrees with the closed form
whenever `Q ≠ 0, 1`, and its value at `Q = 1` is the removable limit.

## Main definitions

* `TauCeti.wenzlParam d Q`: the parameter `a_d(Q)`.

## Main results

* `TauCeti.wenzlParam_eq_div`: the closed form `(1 - Q ^ (d + 1)) / ((1 + Q) * (1 - Q ^ d))`.
* `TauCeti.wenzlParam_one` and `TauCeti.tendsto_one_sub_zpow_div_nhdsNE_one`: the value
  `(d + 1) / (2 * d)` at `Q = 1`, and the closed form tends to it as `Q → 1`.
* `TauCeti.wenzlParam_add_wenzlParam_neg`: the complement identity `a_d + a_(-d) = 1`.
* `TauCeti.wenzlParam_inv`: the inversion symmetry `a_d(Q⁻¹) = a_d(Q)`.
* `TauCeti.wenzlParam_neg_two_sq`: the Jones value `a_(-2)(q ^ 2) = (q + q⁻¹)⁻²`.
* `TauCeti.wenzlParam_exp_mul_I`: `a_k(exp (2 θ i)) = sin ((k + 1) θ) / (2 cos θ sin (k θ))`;
  `TauCeti.wenzlParam_exp_two_pi_mul_I_div`, `TauCeti.wenzlParam_exp_neg_two_pi_mul_I_div` and
  `TauCeti.wenzlParam_exp_two_pi_mul_I_div_two_mul` give the real values at the roots of unity
  `exp (± 2 π i / l)` and the middle value `a_m = 1 / 2` for `l = 2 * m`.
* `TauCeti.wenzlParam_add_of_pow_eq_one`: `a_d` is periodic in `d` modulo the order of `Q`; in
  particular `a_(l - 2) = a_(-2)` when `Q ^ l = 1`.
* `TauCeti.wenzlParam_neg_natCast_eq_sum`: for the normalized geometric weights
  `p_i = Q ^ i / [r]_Q`, `i < r`, the sum `∑ i < j, p_i * p_j` is `a_(-r)(Q)`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_mul_eigenprojection_geometric`: the Ocneanu
  trace realized by the atomic model on `r + 1` positive letters with geometric weights
  (`TauCeti.TypeAHeckeAlgebra.atomicTrace_geometric_eq`) has projection parameter
  `a_(r + 1)(q ^ 2)`.

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

/-! ### The Jones parameter -/

/-- The parameter `a_(-2)(Q) = Q / (1 + Q) ^ 2`. -/
theorem wenzlParam_neg_two (Q : K) : wenzlParam (-2) Q = Q / (1 + Q) ^ 2 := by
  have h := wenzlParam_neg_natCast 2 Q
  push_cast at h
  rw [h]
  simp [sum_range_succ, sq]

/-- **The Jones parameter.** At `Q = q ^ 2`, `a_(-2)(Q) = (q + q⁻¹)⁻²`, the parameter `τ` of the
Jones quotient. -/
theorem wenzlParam_neg_two_sq (q : K) :
    wenzlParam (-2) (q ^ 2) = ((q + q⁻¹) ^ 2)⁻¹ := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [wenzlParam_neg_two]
  rw [wenzlParam_neg_two, show q + q⁻¹ = (1 + q ^ 2) / q by field_simp; ring, div_pow, inv_div]

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

private lemma cos_pi_div_pos {x : ℝ} (hx : 2 < x) : 0 < Real.cos (π / x) := by
  have hx₀ : 0 < x := by linarith
  refine Real.cos_pos_of_mem_Ioo ⟨by linarith [div_pos Real.pi_pos hx₀, Real.pi_pos], ?_⟩
  rwa [div_lt_div_iff_of_pos_left Real.pi_pos hx₀ two_pos]

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
    rw [two_cos]
    linear_combination -e₁ x - e₂ x
  have hpow (n : ℤ) : 1 - exp (2 * θ * I) ^ n = -I * (2 * sin (n * θ)) * exp (n * θ * I) := by
    rw [← exp_int_mul, ← one_sub_exp]
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

/-- **The values at the roots of unity.** For `l ≥ 3` and `0 < k < l`, at `Q = exp (2 π i / l)`,
`a_k(Q) = sin ((k + 1) π / l) / (2 * cos (π / l) * sin (k π / l))`, a real number. -/
theorem wenzlParam_exp_two_pi_mul_I_div {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k) (hkl : k < l) :
    wenzlParam (k : ℤ) (exp (2 * π * I / l)) =
      ↑(Real.sin ((k + 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l))) := by
  have hl₀ : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hcos : 0 < Real.cos (π / l) := cos_pi_div_pos (by exact_mod_cast (by omega : 2 < l))
  have hsin : 0 < Real.sin (k * π / l) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    rw [div_lt_iff₀ hl₀, mul_comm π]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hkl) Real.pi_pos
  have h := wenzlParam_exp_mul_I k (θ := π / l) (by exact_mod_cast hcos.ne')
    (by rw [Int.cast_natCast, ← mul_div_assoc]; exact_mod_cast hsin.ne')
  rw [show 2 * (π / l : ℂ) * I = 2 * π * I / l by ring] at h
  rw [h]
  push_cast
  ring_nf

/-- The values at the conjugate roots of unity `Q = exp (-2 π i / l)` agree with those at
`exp (2 π i / l)`. -/
theorem wenzlParam_exp_neg_two_pi_mul_I_div {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k) (hkl : k < l) :
    wenzlParam (k : ℤ) (exp (-(2 * π * I / l))) =
      ↑(Real.sin ((k + 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l))) := by
  rw [exp_neg, wenzlParam_inv, wenzlParam_exp_two_pi_mul_I_div hl hk₀ hkl]

/-- **The middle value.** For `l = 2 * m ≥ 4`, at `Q = exp (2 π i / l)`, `a_m(Q) = 1 / 2`. -/
theorem wenzlParam_exp_two_pi_mul_I_div_two_mul {m : ℕ} (hm : 2 ≤ m) :
    wenzlParam (m : ℤ) (exp (2 * π * I / (2 * m))) = 1 / 2 := by
  have h := wenzlParam_exp_two_pi_mul_I_div (l := 2 * m) (k := m) (by omega) (by omega) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  have hcos : Real.cos (π / (2 * m)) ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    exact (cos_pi_div_pos (by linarith)).ne'
  -- With `θ = π / (2 * m)`: `sin ((m + 1) θ) = cos θ` and `sin (m θ) = 1`.
  have h₁ : (m + 1) * π / (2 * m) = π / (2 * m) + π / 2 := by field_simp; ring
  have h₂ : m * π / (2 * m) = π / 2 := by field_simp
  rw [h, h₁, h₂, Real.sin_add_pi_div_two, Real.sin_pi_div_two, mul_one,
    div_mul_cancel_right₀ hcos]
  norm_num

end RootOfUnity

/-! ### The discrete Markov traces of the geometric atomic models -/

namespace InfiniteTypeAHeckeAlgebra

variable {q : Kˣ}

/-- **The projection parameter of a geometric atomic model.** Let `Q = q ^ 2` and
`c * [r + 1]_Q = 1`. The Ocneanu trace with parameter `z = c * q ^ (2 * r + 1)`, which the atomic
model on `r + 1` positive letters with weights `c * Q ^ a` realizes
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_geometric_eq`), multiplies by `a_(r + 1)(Q)` when the
eigenprojection `s⁻¹ • (T n + q⁻¹)`, `s = q + q⁻¹`, is appended to an element of the stage on
`n + 1` strands. -/
theorem ocneanuTrace_mul_eigenprojection_geometric (s : Kˣ) (hs : (s : K) = q + ↑q⁻¹) {r : ℕ}
    {c : K} (hc : c * ∑ a ∈ range (r + 1), ((q : K) ^ 2) ^ a = 1) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra K q} (hx : x ∈ stage K q (n + 1)) :
    ocneanuTrace K q (c * (q : K) ^ (2 * r + 1))
        (x * (↑s⁻¹ : K) • (T q n + algebraMap K _ (↑q⁻¹ : K))) =
      wenzlParam ((r + 1 : ℕ) : ℤ) ((q : K) ^ 2) *
        ocneanuTrace K q (c * (q : K) ^ (2 * r + 1)) x := by
  refine (isMarkovTrace_ocneanuTrace _).map_mul_eigenprojection s hs ?_ hx
  have hq : (q : K) ≠ 0 := q.ne_zero
  have hZ : ∑ a ∈ range (r + 1), ((q : K) ^ 2) ^ a ≠ 0 := right_ne_zero_of_mul_eq_one hc
  -- `1 + q ^ 2 = q * s` is nonzero since `s` is a unit.
  have hQ : 1 + (q : K) ^ 2 ≠ 0 := by
    rw [show 1 + (q : K) ^ 2 = q * s by rw [hs, Units.val_inv_eq_inv_val]; field_simp; ring]
    exact mul_ne_zero hq s.ne_zero
  rw [wenzlParam_natCast, Units.val_inv_eq_inv_val, geom_sum_succ' (n := r + 1)]
  field_simp
  linear_combination ((1 + (q : K) ^ 2) * (q : K) ^ (2 * r + 2)) * hc

end InfiniteTypeAHeckeAlgebra

end TauCeti
