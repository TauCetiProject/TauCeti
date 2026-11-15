/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Filter.Basic

/-!
# Multiplicities of labelled roots

If a finite family enumerates a polynomial's roots with multiplicity, the multiplicity
at each label depends only on which labels coincide. Consequently an eventually constant
collision relation gives eventually constant multiplicities, without any continuity or
splitting assumptions on the polynomial family.

We also count the root zero: it occurs in `f.roots` with multiplicity the order of vanishing
`f.natTrailingDegree`, so the roots satisfying a predicate that holds at zero number
`f.natTrailingDegree` plus the nonzero roots satisfying it. Over any integral domain, summing
`f.rootMultiplicity` over any finite set of points never exceeds `f.natDegree`
(`Polynomial.sum_rootMultiplicity_le_natDegree`), including for `f = 0`.
-/

public section

open Filter Polynomial

namespace TauCeti

/-- A finite enumeration of roots with an eventually constant collision relation has
eventually constant multiplicity at each label. The parameter filter is arbitrary, and
the root enumeration at the reference parameter is supplied separately. -/
theorem eventually_rootMultiplicity_eq_of_roots_eq_map
    {K B ι : Type*} [CommRing K] [IsDomain K]
    {I : Finset ι} {f : ι → B → K} {Q : B → Polynomial K} {x₀ : B} {l : Filter B}
    (hroots₀ : (Q x₀).roots = I.val.map (fun i ↦ f i x₀))
    (hroots : ∀ᶠ x in l, (Q x).roots = I.val.map (fun i ↦ f i x))
    (hrel : ∀ᶠ x in l, ∀ i ∈ I, ∀ j ∈ I, f i x = f j x ↔ f i x₀ = f j x₀) :
    ∀ᶠ x in l, ∀ i ∈ I, (Q x).rootMultiplicity (f i x) =
      (Q x₀).rootMultiplicity (f i x₀) := by
  classical
  filter_upwards [hrel, hroots] with x hx hxroots i hi
  rw [← count_roots, ← count_roots, hxroots, hroots₀,
    Multiset.count_map, Multiset.count_map]
  congr 1
  exact Multiset.filter_congr fun j hj ↦ hx i hi j (Finset.mem_val.mp hj)

end TauCeti

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The root zero occurs in `f.roots` with multiplicity the order of vanishing of `f` at zero. -/
theorem count_zero_roots [DecidableEq R] (f : R[X]) : f.roots.count 0 = f.natTrailingDegree := by
  rw [count_roots, rootMultiplicity_eq_natTrailingDegree']

/-- The number of roots satisfying a predicate that holds at zero is the order of vanishing at
zero plus the number of nonzero roots satisfying it. -/
theorem card_filter_roots_eq_natTrailingDegree_add [DecidableEq R] (f : R[X]) {q : R → Prop}
    [DecidablePred q] (hq : q 0) :
    (f.roots.filter q).card =
      f.natTrailingDegree + (f.roots.filter fun α => α ≠ 0 ∧ q α).card := by
  have hsplit : f.roots.filter q =
      f.roots.filter (· = 0) + f.roots.filter fun α => α ≠ 0 ∧ q α := by
    rw [← Multiset.filter_add_not (· = 0) (f.roots.filter q), Multiset.filter_filter,
      Multiset.filter_filter]
    congr 1
    exact Multiset.filter_congr fun α _ => ⟨And.left, fun h => ⟨h, h ▸ hq⟩⟩
  rw [hsplit, Multiset.card_add, Multiset.filter_eq', Multiset.card_replicate, count_zero_roots]

/-- Over a domain, the sum of root multiplicities of a polynomial `f` across any finite set of
points is at most `f.natDegree` (also when `f = 0`, where every multiplicity vanishes). -/
theorem sum_rootMultiplicity_le_natDegree (f : R[X]) (s : Finset R) :
    ∑ a ∈ s, f.rootMultiplicity a ≤ f.natDegree := by
  classical
  calc ∑ a ∈ s, f.rootMultiplicity a
      = ∑ a ∈ s, f.roots.count a := Finset.sum_congr rfl fun _ _ ↦ (count_roots f).symm
    _ ≤ ∑ a ∈ f.roots.toFinset, f.roots.count a :=
        Finset.sum_le_sum_of_ne_zero fun _ _ ha ↦
          Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero ha))
    _ = f.roots.card := Multiset.toFinset_sum_count_eq f.roots
    _ ≤ f.natDegree := card_roots' f

/-- A nonzero constant multiple of a product of linear factors vanishes exactly at the
`r i`. -/
theorem isRoot_C_mul_prod_X_sub_C_iff {ι : Type*} [Fintype ι] {l : R} (hl : l ≠ 0)
    (r : ι → R) (z : R) : (C l * ∏ i, (X - C (r i))).IsRoot z ↔ ∃ i, r i = z := by
  rw [root_mul, iff_false_intro (not_isRoot_C _ z hl), false_or, isRoot_prod]
  simp [sub_eq_zero, eq_comm]

end Polynomial
