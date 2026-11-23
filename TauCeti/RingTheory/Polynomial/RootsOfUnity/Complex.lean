/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.RingTheory.Polynomial.RootsOfUnity.Basic
import Mathlib.Data.Multiset.MapFold

/-!
# Complex roots of geometric sums and `X ^ m + 1`

Specializes `Polynomial.roots_geom_sum_of_isPrimitiveRoot` and `IsPrimitiveRoot.nthRoots_eq` to
`ℂ` via `Complex.isPrimitiveRoot_exp`, expressing the roots of `∑_{k=0}^n X^k` and `X^m + 1` in
terms of `Complex.exp (2πi e / h)` (`Polynomial.roots_geom_sum_complex` and
`Polynomial.roots_X_pow_add_one_complex`).
-/

public section

namespace Polynomial

open Complex Real

/-- The complex roots of `∑_{k=0}^n X^k` are `exp (2πi e / (n + 1))` for `e = 1, …, n`, each with
multiplicity one. -/
theorem roots_geom_sum_complex (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (X : ℂ[X]) ^ k).roots =
      (((List.range n).map (· + 1) : List ℕ) : Multiset ℕ).map fun e : ℕ ↦
        Complex.exp (2 * Real.pi * Complex.I * (e / (n + 1 : ℕ))) := by
  rw [roots_geom_sum_of_isPrimitiveRoot (Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n))]
  refine Multiset.map_congr rfl fun e _ ↦ ?_
  rw [← Complex.exp_natCast_mul]
  congr 1
  ring

/-- The complex roots of `X^m + 1` (`1 ≤ m`) are `exp (2πi e / (2m))` for `e = 1, 3, …, 2m - 1`,
each with multiplicity one. -/
theorem roots_X_pow_add_one_complex {m : ℕ} (hm : 1 ≤ m) :
    ((X : ℂ[X]) ^ m + 1).roots =
      (((List.range m).map (2 * · + 1) : List ℕ) : Multiset ℕ).map fun e : ℕ ↦
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * m : ℕ))) := by
  have hm0 : m ≠ 0 := by omega
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hα : (Complex.exp (Real.pi * Complex.I / m)) ^ m = -1 := by
    rw [← Complex.exp_natCast_mul, mul_div_cancel₀ _ hmC, Complex.exp_pi_mul_I]
  have hnth : nthRoots m (-1 : ℂ) =
      (Multiset.range m).map ((Complex.exp (2 * Real.pi * Complex.I / m)) ^ · *
        Complex.exp (Real.pi * Complex.I / m)) :=
    (Complex.isPrimitiveRoot_exp m hm0).nthRoots_eq hα
  have hlhs : ((X : ℂ[X]) ^ m + 1).roots = nthRoots m (-1 : ℂ) := by
    simp [nthRoots, sub_neg_eq_add]
  rw [hlhs, hnth, ← Multiset.coe_range, Multiset.map_coe, Multiset.map_coe, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ ↦ ?_
  simp only [Function.comp_apply]
  rw [← Complex.exp_natCast_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp

end Polynomial
