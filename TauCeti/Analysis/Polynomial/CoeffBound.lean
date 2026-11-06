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

/-- **The coefficients against a distinguished root.** A monic polynomial `p` that splits over a
normed field, with a root `w` of norm at most `B` whose remaining roots have norm at most `1`,
has its coefficient of `X ^ (n - k)`, for `0 < k < n = p.natDegree`, bounded in norm by
`C(n-1, k-1) * B + C(n-1, k)`: it is `q_(n-k-1) - w * q_(n-k)` for the cofactor `q` of `X - w`,
whose coefficients are bounded by Mathlib's `coeff_le_of_roots_le`. -/
theorem norm_coeff_le_of_roots_erase_le [DecidableEq K] {p : K[X]} {B : ℝ} (hp : p.Monic)
    (hs : Splits p) {w : K} (hw : p.IsRoot w) (hwB : ‖w‖ ≤ B)
    (hB : ∀ z ∈ p.roots.erase w, ‖z‖ ≤ 1) {k : ℕ} (hk : 0 < k) (hkn : k < p.natDegree) :
    ‖p.coeff (p.natDegree - k)‖ ≤
      (p.natDegree - 1).choose (k - 1) * B + (p.natDegree - 1).choose k := by
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
  have hqroots : q.roots = p.roots.erase w := by
    rw [← hfac, roots_mul (hfac ▸ hp.ne_zero), roots_X_sub_C]
    simp
  have hqcoeff : ∀ j, ‖q.coeff j‖ ≤ (p.natDegree - 1).choose j := fun j => by
    have hqp : q ∣ p := ⟨X - C w, by rw [← hfac, mul_comm]⟩
    have h := coeff_le_of_roots_le (p := q) (f := RingHom.id K) (B := 1) j hqmono
      (by simpa using hs.of_dvd hp.ne_zero hqp) (by simpa [hqroots] using hB)
    simpa [hqdeg] using h
  have hsplit : p.coeff (p.natDegree - k) =
      q.coeff (p.natDegree - k - 1) - w * q.coeff (p.natDegree - k) := by
    have h := coeff_X_sub_C_mul (p := q) (r := w) (a := p.natDegree - k - 1)
    rwa [hfac, show p.natDegree - k - 1 + 1 = p.natDegree - k by omega] at h
  have hsym1 : (p.natDegree - 1).choose (p.natDegree - k - 1) = (p.natDegree - 1).choose k := by
    rw [show p.natDegree - k - 1 = p.natDegree - 1 - k by omega,
      Nat.choose_symm (Nat.le_sub_one_of_lt hkn)]
  have hsym2 : (p.natDegree - 1).choose (p.natDegree - k) =
      (p.natDegree - 1).choose (k - 1) := by
    rw [show p.natDegree - k = p.natDegree - 1 - (k - 1) by omega,
      Nat.choose_symm (Nat.sub_le_sub_right hkn.le 1)]
  rw [hsplit]
  calc ‖q.coeff (p.natDegree - k - 1) - w * q.coeff (p.natDegree - k)‖
      ≤ ‖q.coeff (p.natDegree - k - 1)‖ + ‖w‖ * ‖q.coeff (p.natDegree - k)‖ := by
        rw [← norm_mul]; exact norm_sub_le _ _
    _ ≤ (p.natDegree - 1).choose k + B * (p.natDegree - 1).choose (k - 1) := by
        refine add_le_add (by rw [← hsym1]; exact hqcoeff _) (mul_le_mul hwB
          (by rw [← hsym2]; exact hqcoeff _) (norm_nonneg _) (hwB.trans' (norm_nonneg w)))
    _ = (p.natDegree - 1).choose (k - 1) * B + (p.natDegree - 1).choose k := by ring

end Polynomial
