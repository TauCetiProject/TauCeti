/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.RingTheory.Polynomial.Cyclotomic.Roots
import TauCeti.RingTheory.RootsOfUnity.Complex.Exp

/-!
# Complex roots of geometric sums and `X ^ m + 1`

Specializes `Polynomial.roots_sum_range_X_pow` and `Polynomial.roots_X_pow_add_one` to `ℂ` via
`Complex.isPrimitiveRoot_exp`, expressing the roots of `∑_{k=0}^n X^k` and `X^m + 1` in terms of
`Complex.exp (2πi e / h)` (`Polynomial.roots_geom_sum_complex` and
`Polynomial.roots_X_pow_add_one_complex`).
-/

public section

namespace Polynomial

open Complex Real TauCeti

/-- The complex roots of `∑_{k=0}^n X^k` are `exp (2πi e / (n + 1))` for `e = 1, …, n`, each with
multiplicity one. -/
theorem roots_geom_sum_complex (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (X : ℂ[X]) ^ k).roots =
      (((List.range n).map (· + 1) : List ℕ) : Multiset ℕ).map fun e : ℕ ↦
        Complex.exp (2 * Real.pi * Complex.I * (e / (n + 1 : ℕ))) := by
  rw [roots_sum_range_X_pow (Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n))]
  simp [List.map_map, Function.comp_def, exp_two_pi_I_div_pow]

/-- The complex roots of `X^m + 1` (`1 ≤ m`) are `exp (2πi e / (2m))` for `e = 1, 3, …, 2m - 1`,
each with multiplicity one. -/
theorem roots_X_pow_add_one_complex {m : ℕ} (hm : 1 ≤ m) :
    ((X : ℂ[X]) ^ m + 1).roots =
      (((List.range m).map (2 * · + 1) : List ℕ) : Multiset ℕ).map fun e : ℕ ↦
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * m : ℕ))) := by
  rw [roots_X_pow_add_one hm (Complex.isPrimitiveRoot_exp (2 * m) (by omega))]
  simp [List.map_map, Function.comp_def, exp_two_pi_I_div_pow]

end Polynomial
