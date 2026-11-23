/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Monic
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.RingTheory.RootsOfUnity.Complex.Exp

/-!
# The complex roots of `Xⁿ + 1` and of `1 + X + ⋯ + Xⁿ`

Both polynomials split over `ℂ` with distinct roots, all of them roots of unity:

* `Polynomial.roots_X_pow_add_one`: the roots of `Xⁿ + 1` are `exp (2πi (2k + 1) / 2n)` for
  `k < n`, each once.
* `Polynomial.roots_geom_sum_X`: the roots of `1 + X + ⋯ + Xⁿ` are `exp (2πi k / (n + 1))` for
  `k = 1, …, n`, each once.
-/

public section

open Polynomial

namespace Polynomial

/-- **The roots of `Xⁿ + 1`** are `exp (2πi (2k + 1) / 2n)` for `k < n`, each once: they are the
`n`-th roots of `-1 = exp (πi / n) ^ n` (`IsPrimitiveRoot.nthRoots_eq`). -/
theorem roots_X_pow_add_one {n : ℕ} (hn : n ≠ 0) :
    (X ^ n + 1 : ℂ[X]).roots = ((List.range n).map fun k : ℕ =>
      Complex.exp (2 * Real.pi * Complex.I * (((2 * k + 1 : ℕ) : ℂ) / ((2 * n : ℕ) : ℂ))) :
        Multiset ℂ) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hα : Complex.exp (Real.pi * Complex.I / n) ^ n = -1 := by
    rw [← Complex.exp_natCast_mul, mul_div_cancel₀ _ hn', Complex.exp_pi_mul_I]
  have hX : (X ^ n + 1 : ℂ[X]) = X ^ n - C (-1) := by rw [C_neg, C_1, sub_neg_eq_add]
  rw [hX, ← nthRoots, (Complex.isPrimitiveRoot_exp n hn).nthRoots_eq hα, ← Multiset.coe_range,
    Multiset.map_coe]
  refine congrArg _ (List.map_congr_left fun k _ => ?_)
  rw [← Complex.exp_natCast_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp

/-- **The roots of `1 + X + ⋯ + Xⁿ`** are `exp (2πi k / (n + 1))` for `k = 1, …, n`, each once. -/
theorem roots_geom_sum_X (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (X : ℂ[X]) ^ i).roots = ((List.range n).map fun k : ℕ =>
      Complex.exp (2 * Real.pi * Complex.I * (((k + 1 : ℕ) : ℂ) / ((n + 1 : ℕ) : ℂ))) :
        Multiset ℂ) := by
  have hζ := Complex.isPrimitiveRoot_exp (n + 1) (by omega)
  have hmon : (∑ i ∈ Finset.range (n + 1), (X : ℂ[X]) ^ i).Monic := monic_geom_sum_X (by omega)
  refine roots_eq_of_natDegree_le_card_of_ne_zero (S := ⟨_, ?_⟩) ?_ ?_ hmon.ne_zero
  · refine Multiset.coe_nodup.2 (List.Nodup.map_on (fun x hx y hy hxy => ?_) List.nodup_range)
    simp only [TauCeti.exp_two_pi_I_mul_div_eq_pow] at hxy
    rw [List.mem_range] at hx hy
    have := hζ.pow_inj (by omega) (by omega) hxy
    omega
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 (Finset.mem_mk.1 hz))
    rw [List.mem_range] at hk
    simp only [TauCeti.exp_two_pi_I_mul_div_eq_pow, eval_finsetSum, eval_pow, eval_X]
    set z := Complex.exp (2 * Real.pi * Complex.I / ((n + 1 : ℕ) : ℂ)) ^ (k + 1)
    have hne : z ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)
    have hz1 : z ^ (n + 1) = 1 := by
      rw [← pow_mul, mul_comm (k + 1) (n + 1), pow_mul, hζ.pow_eq_one, one_pow]
    rw [geom_sum_eq hne, hz1, sub_self, zero_div]
  · exact (natDegree_geom_sum_X n).le.trans ((List.length_map _).trans List.length_range).ge

end Polynomial

end
