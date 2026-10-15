/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.SupNorm.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# Root bounds in terms of the coefficient sup norm

Reversing the coefficients preserves the sup norm. Cauchy's root bound,
together with the fact that a nonzero integer has modulus at least one,
bounds every real or complex root of an integer polynomial by its sup norm plus one.
Applying this to the reversed polynomial also bounds nonzero roots away from zero.

## References

* J.-H. Evertse, *Diophantine Approximation* (2019), ch. 3, Exercise 3.1(ii).

The root estimate uses Mathlib's `Polynomial.IsRoot.norm_lt_cauchyBound`.
-/

public section

open Polynomial
open scoped NNReal

namespace TauCeti

variable {K : Type*} [RCLike K]

/-- A real or complex root of a nonzero integer polynomial has modulus strictly less
than its coefficient sup norm plus one. -/
theorem _root_.Polynomial.norm_lt_supNorm_add_one_of_aeval_eq_zero (p : ℤ[X])
    (hp : p ≠ 0) {z : K} (hz : aeval z p = 0) : ‖z‖ < p.supNorm + 1 := by
  let q := p.map (Int.castRingHom K)
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hp
  have hroot : q.IsRoot z := by
    simpa only [q, IsRoot.def, eval_map, ← algebraMap_int_eq, ← aeval_def] using hz
  have hlc : (1 : ℝ≥0) ≤ ‖q.leadingCoeff‖₊ := by
    rw [leadingCoeff_map_of_injective (RingHom.injective_int _)]
    simpa only [eq_intCast, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one,
      ← RCLike.ofReal_intCast (K := K), RCLike.norm_ofReal] using
      (by exact_mod_cast Int.one_le_abs (Polynomial.leadingCoeff_ne_zero.mpr hp) :
        (1 : ℝ) ≤ |(p.leadingCoeff : ℝ)|)
  have hsup : (Finset.range q.natDegree).sup (fun i ↦ ‖q.coeff i‖₊) ≤
      p.supNorm.toNNReal := by
    refine Finset.sup_le fun i _ ↦ ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ p.supNorm_nonneg]
    simpa only [q, coeff_map, eq_intCast, coe_nnnorm,
      ← RCLike.ofReal_intCast (K := K), RCLike.norm_ofReal, Int.norm_eq_abs] using p.le_supNorm i
  have hcb : q.cauchyBound ≤ p.supNorm.toNNReal + 1 := by
    simpa only [cauchyBound, add_comm] using
      add_le_add_right ((div_le_self (by positivity) hlc).trans hsup) (1 : ℝ≥0)
  have h := NNReal.coe_lt_coe.mpr ((hroot.norm_lt_cauchyBound hq).trans_le hcb)
  simpa only [coe_nnnorm, NNReal.coe_add, NNReal.coe_one,
    Real.coe_toNNReal _ p.supNorm_nonneg] using h

/-- A nonzero real or complex root of a nonzero integer polynomial has modulus
strictly greater than the reciprocal of its coefficient sup norm plus one. -/
theorem _root_.Polynomial.inv_supNorm_add_one_lt_norm_of_aeval_eq_zero (p : ℤ[X])
    (hp : p ≠ 0) {z : K} (hz : aeval z p = 0) (hz0 : z ≠ 0) :
    (p.supNorm + 1)⁻¹ < ‖z‖ := by
  let := invertibleOfNonzero hz0
  have hr : aeval z⁻¹ p.reverse = 0 := by
    simpa only [aeval_def, invOf_eq_inv] using
      (eval₂_reverse_eq_zero_iff (algebraMap ℤ K) z p).mpr hz
  have h := p.reverse.norm_lt_supNorm_add_one_of_aeval_eq_zero
    (Polynomial.reverse_eq_zero.not.mpr hp) hr
  rw [supNorm_reverse, norm_inv] at h
  exact (inv_lt_comm₀ (by linarith [p.supNorm_nonneg]) (norm_pos_iff.mpr hz0)).mpr h

end TauCeti
