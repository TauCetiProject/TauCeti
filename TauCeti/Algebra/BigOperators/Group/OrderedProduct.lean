/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs

/-!
# Ordered coordinate products in groups

For a linearly ordered index type `I`, a family `U : I → G` in a (not necessarily commutative)
group `G`, and an integer exponent vector `a : I →₀ ℤ`, `TauCeti.orderedCoordProd U a` multiplies
the integer powers `U i ^ a i` along `a.support` in increasing order of `I`. Because zero exponents
contribute `1`, the product agrees with the product along any sorted finite superset of `a.support`
(`TauCeti.orderedCoordProd_eq_sort_prod`), and in particular along `Finset.univ.sort (· ≤ ·)` when
`I` is finite (`TauCeti.orderedCoordProd_eq_univ_sort`).
-/

public section

namespace TauCeti

variable {I G : Type*} [Group G]

/-- The ordered coordinate product `∏_{i ∈ a.support} U_i^{a_i}` in a group `G`, taken in
increasing order of `I`. -/
noncomputable def orderedCoordProd [_ord : LinearOrder I] (U : I → G) (a : I →₀ ℤ) : G :=
  ((a.support.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod

theorem orderedCoordProd_def [LinearOrder I] (U : I → G) (a : I →₀ ℤ) :
    orderedCoordProd U a = ((a.support.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod :=
  (rfl)

@[simp]
theorem orderedCoordProd_zero [LinearOrder I] (U : I → G) : orderedCoordProd U 0 = 1 := by
  simp [orderedCoordProd]

/-- `orderedCoordProd U a` can be computed over any superset `s ⊇ a.support` sorted in increasing
order, since zero exponents contribute `1`. -/
theorem orderedCoordProd_eq_sort_prod [LinearOrder I] (U : I → G) (a : I →₀ ℤ) {s : Finset I}
    (hs : a.support ⊆ s) :
    orderedCoordProd U a = ((s.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod := by
  have hfilt : (s.sort (· ≤ ·)).filter (· ∈ a.support) = a.support.sort (· ≤ ·) :=
    List.Perm.eq_of_pairwise' ((s.pairwise_sort _).filter _) (a.support.pairwise_sort _) <|
      (List.perm_ext_iff_of_nodup ((s.sort_nodup _).filter _) (a.support.sort_nodup _)).mpr fun i ↦
        by simp only [List.mem_filter, Finset.mem_sort, decide_eq_true_eq, and_iff_right_iff_imp]
           exact fun hi ↦ hs hi
  have hprod (l : List I) : ((l.filter (· ∈ a.support)).map fun i ↦ U i ^ a i).prod =
      (l.map fun i ↦ U i ^ a i).prod := by
    induction l with
    | nil => rfl
    | cons i tl ih =>
      rw [List.filter_cons]
      split_ifs with hp
      · rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ih]
      · rw [List.map_cons, List.prod_cons, (by simpa using hp : a i = 0), zpow_zero, one_mul, ih]
  rw [orderedCoordProd, ← hfilt, hprod]

/-- On a finite index type, `orderedCoordProd U a` equals the product over `Finset.univ.sort`. -/
theorem orderedCoordProd_eq_univ_sort [LinearOrder I] [Fintype I] (U : I → G) (a : I →₀ ℤ) :
    orderedCoordProd U a = ((Finset.univ.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod :=
  orderedCoordProd_eq_sort_prod U a (Finset.subset_univ _)

end TauCeti
