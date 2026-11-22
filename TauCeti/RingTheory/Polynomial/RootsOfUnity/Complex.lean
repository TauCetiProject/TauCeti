/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Data.Multiset.MapFold

/-!
# Roots of geometric sums and `X ^ m + 1` at roots of unity

Over any integral domain, a primitive `(n + 1)`-th root of unity `ζ` displays the roots of the
geometric sum `∑_{k=0}^n X^k` as `ζ¹, …, ζⁿ` (`Polynomial.roots_geom_sum_of_isPrimitiveRoot`),
and a primitive `m`-th root `ζ` together with an `m`-th root `α` of `-1` displays the roots of
`X^m + 1` as `ζᵏ α` for `k < m` (`Polynomial.roots_X_pow_add_one_of_isPrimitiveRoot`).

Specializing to `ℂ` via `Complex.isPrimitiveRoot_exp` expresses both multisets in terms of
`Complex.exp (2πi e / h)` (`Polynomial.roots_geom_sum_complex` and
`Polynomial.roots_X_pow_add_one_complex`).
-/

public section

namespace Polynomial

open Complex Real

/-- Over an integral domain, if `ζ` is a primitive `(n + 1)`-th root of unity, the roots of the
geometric sum `∑_{k=0}^n X^k` are `ζ¹, …, ζⁿ`, counted with multiplicity. -/
theorem roots_geom_sum_of_isPrimitiveRoot {K : Type*} [CommRing K] [IsDomain K] {n : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ (n + 1)) :
    (∑ k ∈ Finset.range (n + 1), (X : K[X]) ^ k).roots =
      (Multiset.ofList ((List.range n).map (· + 1))).map (ζ ^ ·) := by
  have hnth : nthRoots (n + 1) (1 : K) = (Multiset.range (n + 1)).map (ζ ^ · * 1) :=
    hζ.nthRoots_eq (one_pow (n + 1))
  have hlhs : nthRoots (n + 1) (1 : K) =
      (∑ k ∈ Finset.range (n + 1), (X : K[X]) ^ k).roots + {1} := by
    rw [nthRoots, map_one, ← geom_sum_mul (X : K[X]) (n + 1),
      roots_mul (by rw [geom_sum_mul]; simpa using X_pow_sub_C_ne_zero (Nat.succ_pos n) (1 : K))]
    congr 1
    simpa using roots_X_sub_C (1 : K)
  have hrhs : (Multiset.range (n + 1)).map (ζ ^ · * 1) =
      ((Multiset.ofList ((List.range n).map (· + 1))).map (ζ ^ ·)) + {1} := by
    rw [← Multiset.coe_range, List.range_succ_eq_map, ← Multiset.cons_coe, Multiset.map_cons,
      pow_zero, one_mul, ← Multiset.singleton_add, add_comm]
    congr 1
    exact Multiset.map_congr rfl fun e _ ↦ mul_one _
  exact add_right_cancel (hlhs.symm.trans (hnth.trans hrhs))

/-- Over an integral domain, if `ζ` is a primitive `m`-th root of unity and `α^m = -1`,
the roots of `X^m + 1` are `ζᵏ α` for `0 ≤ k < m`, counted with multiplicity. -/
theorem roots_X_pow_add_one_of_isPrimitiveRoot {K : Type*} [CommRing K] [IsDomain K] {m : ℕ}
    {ζ α : K} (hζ : IsPrimitiveRoot ζ m) (hα : α ^ m = -1) :
    ((X : K[X]) ^ m + 1).roots = (Multiset.ofList (List.range m)).map fun k ↦ ζ ^ k * α := by
  have hnth : nthRoots m (-1 : K) = (Multiset.range m).map (ζ ^ · * α) :=
    hζ.nthRoots_eq hα
  have hlhs : ((X : K[X]) ^ m + 1).roots = nthRoots m (-1 : K) := by
    simp [nthRoots, sub_neg_eq_add]
  rw [hlhs, hnth, ← Multiset.coe_range]

/-- The complex roots of `∑_{k=0}^n X^k` are `exp (2πi e / (n + 1))` for `e = 1, …, n`, each with
multiplicity one. -/
theorem roots_geom_sum_complex (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (X : ℂ[X]) ^ k).roots =
      (Multiset.ofList ((List.range n).map (· + 1))).map fun e : ℕ ↦
        Complex.exp (2 * Real.pi * Complex.I * (e / (n + 1 : ℕ))) := by
  rw [roots_geom_sum_of_isPrimitiveRoot (Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n))]
  refine Multiset.map_congr rfl fun e _ ↦ ?_
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- The complex roots of `X^m + 1` (`1 ≤ m`) are `exp (2πi e / (2m))` for `e = 1, 3, …, 2m - 1`,
each with multiplicity one. -/
theorem roots_X_pow_add_one_complex {m : ℕ} (hm : 1 ≤ m) :
    ((X : ℂ[X]) ^ m + 1).roots =
      (Multiset.ofList ((List.range m).map (2 * · + 1))).map fun e : ℕ ↦
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * m : ℕ))) := by
  have hm0 : m ≠ 0 := by omega
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hα : (Complex.exp (Real.pi * Complex.I / m)) ^ m = -1 := by
    rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ hmC, Complex.exp_pi_mul_I]
  rw [roots_X_pow_add_one_of_isPrimitiveRoot (Complex.isPrimitiveRoot_exp m hm0) hα]
  have hcoe : ∀ l : List ℕ, Multiset.ofList l = (l : Multiset ℕ) := fun _ ↦ rfl
  rw [hcoe, hcoe, Multiset.map_coe, Multiset.map_coe, List.map_map]
  refine congrArg Multiset.ofList (List.map_congr_left fun k _ ↦ ?_)
  simp only [Function.comp_apply]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp

end Polynomial

namespace TauCeti

/-- A duplicate-free multiset of complex numbers whose elements are exactly `exp (2πi e / h)` as
`e` runs over a duplicate-free list `es` of residues `< h` equals `(Multiset.ofList es).map _`. -/
theorem multiset_eq_map_exp_of_mem_iff_of_nodup {s : Multiset ℂ} {es : List ℕ} {h : ℕ}
    (hh : 0 < h) (hes_nd : es.Nodup) (hes_lt : ∀ e ∈ es, e < h) (hs_nd : s.Nodup)
    (hmem : ∀ ζ : ℂ, ζ ∈ s ↔
      ∃ e ∈ es, Complex.exp (2 * Real.pi * Complex.I * (e / (h : ℕ))) = ζ) :
    s = (Multiset.ofList es).map fun e : ℕ ↦
      Complex.exp (2 * Real.pi * Complex.I * (e / (h : ℕ))) := by
  let ζ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hζ : IsPrimitiveRoot ζ h := Complex.isPrimitiveRoot_exp h hh.ne'
  have hpow : ∀ e : ℕ, Complex.exp (2 * Real.pi * Complex.I * (e / (h : ℕ))) = ζ ^ e := fun e ↦ by
    dsimp [ζ]; rw [← Complex.exp_nat_mul]; congr 1; ring
  refine (Multiset.Nodup.ext hs_nd (Multiset.Nodup.map_on (fun x hx y hy hxy ↦ ?_)
    (Multiset.coe_nodup.mpr hes_nd))).mpr fun z ↦ ?_
  · rw [hpow, hpow] at hxy
    exact hζ.pow_inj (hes_lt x hx) (hes_lt y hy) hxy
  · simp [hmem]

end TauCeti
