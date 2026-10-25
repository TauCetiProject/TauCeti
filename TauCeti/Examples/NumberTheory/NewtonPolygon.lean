/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.NumberTheory.NewtonPolygon.Roots
public import TauCeti.NumberTheory.Padics.LogGauge

/-!
# Polynomial Newton slopes over the p-adic field

These calculations use the actual valuation on `ℚ_[p]`, normalized by `v(p) = 1`.
They check products of distinct slopes, repeated slopes, collinear coefficient points,
and the separate contribution of zero roots.
-/

public section

open Polynomial TauCeti

namespace TauCeti.Examples.Newton

variable (p : ℕ) [Fact p.Prime]

private theorem slopes_one_sub_X :
    (1 - X : ℚ_[p][X]).newtonSlopes (Padic.realAddValuation p) = {0} := by
  have h : (1 - X : ℚ_[p][X]) = C (-1) * (X - C 1) := by
    simp only [map_neg, map_one, neg_mul, one_mul, neg_sub]
  rw [h, newtonSlopes_C_mul _ _ (by
    simp only [AddValuation.map_neg, AddValuation.map_one, ne_eq,
      LinearOrderedAddCommGroupWithTop.zero_ne_top, not_false_eq_true]),
    newtonSlopes_X_sub_C _ (by
      simp only [AddValuation.map_one, ne_eq,
        LinearOrderedAddCommGroupWithTop.zero_ne_top, not_false_eq_true])]
  simp only [AddValuation.map_one, WithTop.untop₀_zero, neg_zero]

private theorem slopes_one_sub_prime_mul_X :
    (1 - C (p : ℚ_[p]) * X).newtonSlopes (Padic.realAddValuation p) = {1} := by
  have h : (1 - C (p : ℚ_[p]) * X) = (1 - X : ℚ_[p][X]).comp (C (p : ℚ_[p]) * X) := by
    simp only [map_natCast, sub_comp, one_comp, X_comp]
  rw [h, newtonSlopes_comp_C_mul_X _ _ (by rw [Padic.realAddValuation_p]; exact WithTop.coe_ne_top)]
  simp only [slopes_one_sub_X, Padic.realAddValuation_p, WithTop.untop₀_one,
    Multiset.map_singleton, zero_add]

/-- The product of two linear factors has one edge of each slope. -/
theorem newtonSlopes_one_sub_X_mul_one_sub_prime_mul_X :
    ((1 - X) * (1 - C (p : ℚ_[p]) * X)).newtonSlopes (Padic.realAddValuation p) = {0, 1} := by
  rw [newtonSlopes_mul]
  · rw [slopes_one_sub_X, slopes_one_sub_prime_mul_X]
    rfl
  all_goals apply newtonPolygon_ne_top_of_ne_zero (fun x hx => (AddValuation.top_iff _).mp hx)
  all_goals
    intro h
    have h0 := congrArg (fun f : ℚ_[p][X] => f.coeff 0) h
    simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, coeff_zero,
      mul_coeff_zero, mul_zero, one_ne_zero] at h0

/-- Multiplying by a power of `X` does not create finite slopes. -/
theorem newtonSlopes_X_sq_mul_one_sub_prime_mul_X :
    (X ^ 2 * (1 - C (p : ℚ_[p]) * X)).newtonSlopes (Padic.realAddValuation p) = {1} := by
  rw [newtonSlopes_X_pow_mul, slopes_one_sub_prime_mul_X]

/-- A collinear middle coefficient does not split the slope. -/
theorem newtonSlopes_one_add_prime_mul_X_add_prime_sq_mul_X_sq :
    (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 2) * X ^ 2).newtonSlopes
    (Padic.realAddValuation p) = {1, 1} := by
  let d : FiniteSlopeData ℝ := ⟨0, 0, 2, fun _ => 1, monotone_const⟩
  have hd : d.heights =
      (1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 2) * X ^ 2).newtonPolygon
        (Padic.realAddValuation p) := by
    have ha : (fun n => Padic.realAddValuation p
        ((1 + C (p : ℚ_[p]) * X + C ((p : ℚ_[p]) ^ 2) * X ^ 2).coeff n)) =
        d.heights := by
      funext n
      rcases n with _ | _ | _ | n
      all_goals simp only [coeff_add, coeff_C_mul, coeff_one, coeff_X, coeff_X_pow]
      all_goals norm_num [d, FiniteSlopeData.heights_def, prefixSum_succ, prefixSum_zero,
        Padic.realAddValuation_p, AddValuation.map_pow]
    rw [newtonPolygon_def, ha, d.isConvexSeq_heights.lowerConvexEnvelope_eq]
  rw [newtonSlopes_eq_slopeMultiset hd, FiniteSlopeData.slopeMultiset_def]
  rfl

/-- A repeated linear factor gives a repeated slope. -/
theorem newtonSlopes_one_sub_prime_mul_X_sq :
    ((1 - C (p : ℚ_[p]) * X) ^ 2).newtonSlopes (Padic.realAddValuation p) = {1, 1} := by
  have h : (1 - C (p : ℚ_[p]) * X).newtonPolygon (Padic.realAddValuation p) ≠ ⊤ := by
    apply newtonPolygon_ne_top_of_ne_zero (fun x hx => (AddValuation.top_iff _).mp hx)
    intro h
    have h0 := congrArg (fun f : ℚ_[p][X] => f.coeff 0) h
    simp only [coeff_sub, coeff_one_zero, mul_coeff_zero, coeff_X_zero,
      mul_zero, sub_zero, coeff_zero, one_ne_zero] at h0
  rw [pow_two, newtonSlopes_mul _ _ _ h h, slopes_one_sub_prime_mul_X]
  rfl

/-- The same polynomial has a zero of multiplicity two, separately from its finite slope. -/
theorem natTrailingDegree_X_sq_mul_one_sub_prime_mul_X :
    (X ^ 2 * (1 - C (p : ℚ_[p]) * X)).natTrailingDegree = 2 := by
  have h : (1 - C (p : ℚ_[p]) * X).coeff 0 ≠ 0 := by
    simp only [coeff_sub, coeff_one_zero, mul_coeff_zero, coeff_X_zero, mul_zero,
      sub_zero, ne_eq, one_ne_zero, not_false_eq_true]
  rw [mul_comm, natTrailingDegree_mul_X_pow (by intro hf; exact h (by rw [hf, coeff_zero])),
    natTrailingDegree_eq_zero_of_constantCoeff_ne_zero h, zero_add]

end TauCeti.Examples.Newton
