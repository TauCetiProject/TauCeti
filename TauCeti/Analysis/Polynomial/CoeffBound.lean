/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Polynomial

/-!
# Coefficient bounds in terms of root bounds

Mathlib's `Polynomial.coeff_le_of_roots_le` bounds every coefficient of a monic polynomial by
`B ^ (p.natDegree - i)` times a binomial coefficient, where `B` bounds all its roots. This file
adds the estimate for the constant coefficient that keeps the factor of a distinguished root `w`
separate:

  `‖p.coeff 0‖ ≤ ‖w‖ * B ^ (p.natDegree - 1)`

for a monic `p` with a root `w` and all roots in the closed disc of radius `B`.

## Main results

* `Polynomial.norm_coeff_zero_le_norm_mul_pow_of_roots_le`: the constant coefficient of a monic
  polynomial with bounded roots is at most `‖w‖ * B ^ (p.natDegree - 1)` at each root `w`.
-/

public section

open Polynomial

namespace Polynomial

variable {K : Type*} [NormedField K]

/-- **The constant coefficient against a distinguished root.** A monic polynomial `p` that splits
over a normed field, all of whose roots are bounded by `B`, has constant coefficient at most
`‖w‖ * B ^ (p.natDegree - 1)` at each root `w`: it is `±w` times the product of the remaining
roots, each of modulus at most `B`. -/
theorem norm_coeff_zero_le_norm_mul_pow_of_roots_le {p : K[X]} {B : ℝ} (hp : p.Monic)
    (hs : Splits p) (hB : ∀ z ∈ p.roots, ‖z‖ ≤ B) {w : K} (hw : p.IsRoot w) :
    ‖p.coeff 0‖ ≤ ‖w‖ * B ^ (p.natDegree - 1) := by
  set q := p /ₘ (X - C w)
  have hfac : (X - C w) * q = p := mul_divByMonic_eq_iff_isRoot.mpr hw
  have hqmono : q.Monic := by
    have h := congrArg leadingCoeff hfac
    rw [leadingCoeff_mul, (monic_X_sub_C w).leadingCoeff, one_mul, hp.leadingCoeff] at h
    exact h
  have hq0 : q ≠ 0 := hqmono.ne_zero
  have hqdeg : q.natDegree = p.natDegree - 1 := by
    have h := congrArg natDegree hfac
    rw [natDegree_mul (monic_X_sub_C w).ne_zero hq0, natDegree_X_sub_C] at h
    omega
  -- every root of the quotient is a root of `p`
  have hqr : ∀ z ∈ q.roots, ‖z‖ ≤ B := by
    intro z hz
    refine hB z ((mem_roots hp.ne_zero).mpr ?_)
    rw [Polynomial.IsRoot.def, ← hfac, eval_mul, eval_sub, eval_X, eval_C]
    exact mul_eq_zero_of_right _ ((mem_roots hq0).mp hz)
  have hcoeff : ‖q.coeff 0‖ ≤ B ^ q.natDegree := by
    have hqp : q ∣ p := ⟨X - C w, by rw [← hfac, mul_comm]⟩
    have h := coeff_le_of_roots_le (p := q) (f := RingHom.id K) (B := B) 0 hqmono
      (by simpa using hs.of_dvd hp.ne_zero hqp) (by simpa using hqr)
    simpa only [map_id, tsub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] using h
  -- the constant term of `p` is `-w` times that of the quotient
  have hconst : p.coeff 0 = -w * q.coeff 0 := by
    rw [coeff_zero_eq_eval_zero, ← hfac, eval_mul, eval_sub, eval_X, eval_C, zero_sub,
      coeff_zero_eq_eval_zero]
  rw [hconst, norm_mul, norm_neg, ← hqdeg]
  exact mul_le_mul_of_nonneg_left hcoeff (norm_nonneg w)

end Polynomial
