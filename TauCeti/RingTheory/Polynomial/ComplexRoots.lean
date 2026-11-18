/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Monic
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.RingTheory.RootsOfUnity.Complex.Exp

/-!
# The complex roots of `Xⁿ + 1` and of `1 + X + ⋯ + Xⁿ`

Both polynomials split over `ℂ` with distinct roots, all of them roots of unity:

* `Polynomial.roots_X_pow_add_one`: the roots of `Xⁿ + 1` are `exp (2πi (2k + 1) / 2n)` for
  `k < n`, each once.
* `Polynomial.roots_geom_sum_X`: the roots of `1 + X + ⋯ + X^{m+1}` are `exp (2πi k / (m + 2))`
  for `k = 1, …, m + 1`, each once.
-/

public section

open Polynomial

namespace Polynomial

/-- **The roots of `Xⁿ + 1`** are `exp (2πi (2k + 1) / 2n)` for `k < n`, each once. -/
theorem roots_X_pow_add_one {n : ℕ} (hn : n ≠ 0) :
    (X ^ n + 1 : ℂ[X]).roots = ((List.range n).map fun k : ℕ =>
      Complex.exp (2 * Real.pi * Complex.I * (((2 * k + 1 : ℕ) : ℂ) / ((2 * n : ℕ) : ℂ))) :
        Multiset ℂ) := by
  have hζ := Complex.isPrimitiveRoot_exp (2 * n) (by omega)
  have hn1 : Complex.exp (2 * Real.pi * Complex.I / ((2 * n : ℕ) : ℂ)) ^ n = -1 := by
    have := hζ.pow_of_dvd hn (dvd_mul_left n 2)
    rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hn)] at this
    exact this.eq_neg_one_of_two_right
  have hmon : (X ^ n + 1 : ℂ[X]).Monic := by simpa using monic_X_pow_add_C (1 : ℂ) hn
  refine roots_eq_of_natDegree_le_card_of_ne_zero (S := ⟨_, ?_⟩) ?_ ?_ hmon.ne_zero
  · refine Multiset.coe_nodup.2 (List.Nodup.map_on (fun x hx y hy hxy => ?_) List.nodup_range)
    simp only [Complex.exp_two_pi_I_mul_div_eq_pow] at hxy
    rw [List.mem_range] at hx hy
    have := hζ.pow_inj (by omega) (by omega) hxy
    omega
  · intro z hz
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 (Finset.mem_mk.1 hz))
    simp only [Complex.exp_two_pi_I_mul_div_eq_pow, eval_add, eval_pow, eval_X, eval_one]
    rw [← pow_mul, mul_comm (2 * k + 1) n, pow_mul, hn1, Odd.neg_one_pow ⟨k, rfl⟩, neg_add_cancel]
  · simp

/-- **The roots of `1 + X + ⋯ + X^{m+1}`** are `exp (2πi k / (m + 2))` for `k = 1, …, m + 1`, each
once. -/
theorem roots_geom_sum_X (m : ℕ) :
    (∑ i ∈ Finset.range (m + 2), (X : ℂ[X]) ^ i).roots = ((List.range (m + 1)).map fun k : ℕ =>
      Complex.exp (2 * Real.pi * Complex.I * (((k + 1 : ℕ) : ℂ) / ((m + 2 : ℕ) : ℂ))) :
        Multiset ℂ) := by
  have hζ := Complex.isPrimitiveRoot_exp (m + 2) (by omega)
  have hmon : (∑ i ∈ Finset.range (m + 2), (X : ℂ[X]) ^ i).Monic := monic_geom_sum_X (by omega)
  refine roots_eq_of_natDegree_le_card_of_ne_zero (S := ⟨_, ?_⟩) ?_ ?_ hmon.ne_zero
  · refine Multiset.coe_nodup.2 (List.Nodup.map_on (fun x hx y hy hxy => ?_) List.nodup_range)
    simp only [Complex.exp_two_pi_I_mul_div_eq_pow] at hxy
    rw [List.mem_range] at hx hy
    have := hζ.pow_inj (by omega) (by omega) hxy
    omega
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 (Finset.mem_mk.1 hz))
    rw [List.mem_range] at hk
    simp only [Complex.exp_two_pi_I_mul_div_eq_pow, eval_finsetSum, eval_pow, eval_X]
    set z := Complex.exp (2 * Real.pi * Complex.I / ((m + 2 : ℕ) : ℂ)) ^ (k + 1)
    have hne : z ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)
    have hz1 : z ^ (m + 2) = 1 := by
      rw [← pow_mul, mul_comm (k + 1) (m + 2), pow_mul, hζ.pow_eq_one, one_pow]
    have := geom_sum_mul z (m + 2)
    rw [hz1, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  · exact (natDegree_geom_sum_X (m + 1)).le.trans ((List.length_map _).trans List.length_range).ge

end Polynomial

end
