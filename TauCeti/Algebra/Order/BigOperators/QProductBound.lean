/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Ring.Defs

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lower bounds for finite `q`-products

For an element `q > 1` in a linearly ordered commutative ring (or field) and a natural number `m`,
we establish the inductive lower bound
`(q - m) * q ^ m * ∏ i ∈ range m, q ^ i ≤ q * ∏ i ∈ range m, (q ^ (i + 1) - 1)`,
together with its divided form
`1 - m / q ≤ ∏ i ∈ range m, (1 - (q ^ (i + 1))⁻¹)`
and the equivalent matrix-group density bound
`(q - m) * q ^ (m * m - 1) ≤ ∏ i ∈ range m, (q ^ m - q ^ i)` (for `m ≥ 1`).

## Main statements

* `TauCeti.sub_mul_pow_mul_prod_le_mul_prod`: the ring-level `q`-product inequality for `q > 1`.
* `TauCeti.one_sub_div_le_prod_one_sub_inv_pow`: the field-level inequality
  `1 - m / q ≤ ∏ i ∈ range m, (1 - (q ^ (i + 1))⁻¹)`.
* `TauCeti.mul_pow_sq_le_q_mul_prod_sub`: the `GL_m`-cardinality form
  `(q - m) * q ^ (m * m) ≤ q * ∏ i ∈ range m, (q ^ m - q ^ i)`.

## Provenance

Adapted from `sub_mul_pow_mul_prod_le_mul_prod` in
`grh/src/Lib/LocalGL/Green/TauFunctions.lean` of `grh-lean`
(<https://github.com/lsernau/grh-lean>, commit `72fead102f663d5c7a407964a13dc0cf9d977207`),
generalized from `ℝ` to any linearly ordered commutative ring / field, and complemented with
the divided `q`-Pochhammer lower bound and the `GL_m` density bound.
-/

@[expose] public section

open Finset

namespace TauCeti

/-- For `q > 1` in a linearly ordered commutative ring and `m : ℕ`,
`(q - m) * q ^ m * ∏ i ∈ range m, q ^ i ≤ q * ∏ i ∈ range m, (q ^ (i + 1) - 1)`. -/
theorem sub_mul_pow_mul_prod_le_mul_prod {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {q : R} (hq : 1 < q) (m : ℕ) :
    (q - m) * q ^ m * ∏ i ∈ range m, q ^ i ≤
      q * ∏ i ∈ range m, (q ^ (i + 1) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h_factor_nonneg : 0 ≤ q ^ (m + 1) - 1 := sub_nonneg.2 (one_le_pow₀ hq.le)
    have h_key : (q - (m + 1)) * q ^ (m + 1) ≤ (q - m) * (q ^ (m + 1) - 1) := by
      have hpow : q ≤ q ^ (m + 1) := le_self_pow₀ hq.le m.add_one_ne_zero
      have : (0 : R) ≤ m := Nat.cast_nonneg m
      linarith
    have : 0 ≤ ∏ i ∈ range m, q ^ i :=
      prod_nonneg fun _ _ ↦ pow_nonneg (zero_le_one.trans hq.le) _
    have : 0 ≤ q ^ m := pow_nonneg (zero_le_one.trans hq.le) _
    push_cast [prod_range_succ]
    calc (q - (m + 1)) * q ^ (m + 1) * ((∏ i ∈ range m, q ^ i) * q ^ m)
        ≤ (q - m) * (q ^ (m + 1) - 1) * ((∏ i ∈ range m, q ^ i) * q ^ m) := by gcongr
      _ = (q - m) * q ^ m * (∏ i ∈ range m, q ^ i) * (q ^ (m + 1) - 1) := by ring
      _ ≤ q * (∏ i ∈ range m, (q ^ (i + 1) - 1)) * (q ^ (m + 1) - 1) := by gcongr
      _ = q * ((∏ i ∈ range m, (q ^ (i + 1) - 1)) * (q ^ (m + 1) - 1)) := by ring

/-- Divided `q`-Pochhammer lower bound: for `q > 1` in a linearly ordered field and `m : ℕ`,
`1 - m / q ≤ ∏ i ∈ range m, (1 - (q ^ (i + 1))⁻¹)`. -/
theorem one_sub_div_le_prod_one_sub_inv_pow {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {q : K} (hq : 1 < q) (m : ℕ) :
    1 - (m : K) / q ≤ ∏ i ∈ range m, (1 - (q ^ (i + 1))⁻¹) := by
  have hq_pos : 0 < q := zero_lt_one.trans hq
  have hden_pos : 0 < q * (q ^ m * ∏ i ∈ range m, q ^ i) := by positivity
  have h_prod : (q ^ m * ∏ i ∈ range m, q ^ i) * ∏ i ∈ range m, (1 - (q ^ (i + 1))⁻¹) =
      ∏ i ∈ range m, (q ^ (i + 1) - 1) := by
    have hq_pow : q ^ m * ∏ i ∈ range m, q ^ i = ∏ i ∈ range m, q ^ (i + 1) := by
      simp [pow_succ, prod_mul_distrib, mul_comm]
    rw [hq_pow, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ ↦ ?_
    have hqi : q ^ (i + 1) ≠ 0 := pow_ne_zero _ hq_pos.ne'
    rw [mul_sub, mul_one, mul_inv_cancel₀ hqi]
  rw [← mul_le_mul_iff_right₀ hden_pos]
  calc q * (q ^ m * ∏ i ∈ range m, q ^ i) * (1 - (m : K) / q)
      = (q - m) * q ^ m * ∏ i ∈ range m, q ^ i := by
        field_simp [hq_pos.ne']
    _ ≤ q * ∏ i ∈ range m, (q ^ (i + 1) - 1) := sub_mul_pow_mul_prod_le_mul_prod hq m
    _ = q * (q ^ m * ∏ i ∈ range m, q ^ i) * ∏ i ∈ range m, (1 - (q ^ (i + 1))⁻¹) := by
        rw [← h_prod]; ring

/-- Lower bound for the `GL_m`-style product `∏ i ∈ range m, (q ^ m - q ^ i)`:
for `q > 1` in a linearly ordered commutative ring and `m : ℕ`,
`(q - m) * q ^ (m * m) ≤ q * ∏ i ∈ range m, (q ^ m - q ^ i)`. -/
theorem mul_pow_sq_le_q_mul_prod_sub {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {q : R} (hq : 1 < q) (m : ℕ) :
    (q - m) * q ^ (m * m) ≤ q * ∏ i ∈ range m, (q ^ m - q ^ i) := by
  have hq_nonneg : 0 ≤ q := zero_le_one.trans hq.le
  have h_prod_rev : ∏ i ∈ range m, (q ^ m - q ^ i) =
      (∏ i ∈ range m, q ^ i) * ∏ i ∈ range m, (q ^ (i + 1) - 1) := by
    have h1 : ∏ i ∈ range m, (q ^ m - q ^ i) =
        ∏ i ∈ range m, q ^ i * (q ^ (m - i) - 1) := by
      refine prod_congr rfl fun i hi ↦ ?_
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt (mem_range.mp hi))]
    rw [h1, prod_mul_distrib]
    congr 1
    rw [← prod_range_reflect (fun i ↦ q ^ (i + 1) - 1) m]
    refine prod_congr rfl fun i hi ↦ ?_
    have hi' : i < m := mem_range.mp hi
    congr 2
    omega
  have h_pow : (q ^ m * ∏ i ∈ range m, q ^ i) * ∏ i ∈ range m, q ^ i = q ^ (m * m) := by
    rw [prod_pow_eq_pow_sum, ← pow_add, ← pow_add]
    congr 1
    rcases m with _ | m
    · simp
    · have h2 := Finset.sum_range_id_mul_two (m + 1)
      simp only [Nat.add_sub_cancel] at h2
      have h3 : (m + 1) * m + (m + 1) = (m + 1) * (m + 1) := by ring
      omega
  have h_base := sub_mul_pow_mul_prod_le_mul_prod hq m
  have : 0 ≤ ∏ i ∈ range m, q ^ i := prod_nonneg fun _ _ ↦ pow_nonneg hq_nonneg _
  calc (q - m) * q ^ (m * m)
      = (q - m) * q ^ m * (∏ i ∈ range m, q ^ i) * ∏ i ∈ range m, q ^ i := by
        rw [← h_pow]; ring
    _ ≤ q * (∏ i ∈ range m, (q ^ (i + 1) - 1)) * ∏ i ∈ range m, q ^ i := by gcongr
    _ = q * ∏ i ∈ range m, (q ^ m - q ^ i) := by rw [h_prod_rev]; ring

end TauCeti
