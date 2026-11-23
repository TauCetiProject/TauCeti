/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Roots of geometric sums at primitive roots of unity

Over any integral domain, a primitive `(n + 1)`-th root of unity `ζ` displays the roots of the
geometric sum `∑_{k=0}^n X^k` as `ζ¹, …, ζⁿ` (`Polynomial.roots_geom_sum_of_isPrimitiveRoot`).
-/

public section

namespace Polynomial

/-- Over an integral domain, if `ζ` is a primitive `(n + 1)`-th root of unity, the roots of the
geometric sum `∑_{k=0}^n X^k` are `ζ¹, …, ζⁿ`, counted with multiplicity. -/
theorem roots_geom_sum_of_isPrimitiveRoot {K : Type*} [CommRing K] [IsDomain K] {n : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ (n + 1)) :
    (∑ k ∈ Finset.range (n + 1), (X : K[X]) ^ k).roots =
      (((List.range n).map (· + 1) : List ℕ) : Multiset ℕ).map (ζ ^ ·) := by
  have hnth : nthRoots (n + 1) (1 : K) = (Multiset.range (n + 1)).map (ζ ^ · * 1) :=
    hζ.nthRoots_eq (one_pow (n + 1))
  have hlhs : nthRoots (n + 1) (1 : K) =
      (∑ k ∈ Finset.range (n + 1), (X : K[X]) ^ k).roots + {1} := by
    rw [nthRoots, map_one, ← geom_sum_mul (X : K[X]) (n + 1),
      roots_mul (by rw [geom_sum_mul]; simpa using X_pow_sub_C_ne_zero (Nat.succ_pos n) (1 : K))]
    congr 1
    simpa using roots_X_sub_C (1 : K)
  have hrhs : (Multiset.range (n + 1)).map (ζ ^ · * 1) =
      ((((List.range n).map (· + 1) : List ℕ) : Multiset ℕ).map (ζ ^ ·)) + {1} := by
    rw [← Multiset.coe_range, List.range_succ_eq_map, ← Multiset.cons_coe, Multiset.map_cons,
      pow_zero, one_mul, ← Multiset.singleton_add, add_comm]
    congr 1
    exact Multiset.map_congr rfl fun e _ ↦ mul_one _
  exact add_right_cancel (hlhs.symm.trans (hnth.trans hrhs))

end Polynomial
