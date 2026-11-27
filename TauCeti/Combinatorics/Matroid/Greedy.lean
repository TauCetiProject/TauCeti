/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Matroid.MaxWeightBase
import Mathlib.Order.Preorder.Finite

/-!
# The matroid greedy theorem

A set is greedily built for a predicate `P` if it can be obtained from the empty set by
inserting an element of greatest weight at each step among the insertions that preserve `P`.

For the independence predicate of a matroid, every greedily built set has greatest weight
among the independent sets of the same cardinality. In particular, a greedily built base is a
base of maximum weight, and is optimal among all independent sets when weights are nonnegative.
On a finite ground set a greedily built set is contained in a greedily built base,
which is therefore a base of maximum weight.

## Main declarations

* `TauCeti.Greedy`: the relation of being greedily built for a set predicate and a weight.
* `TauCeti.Greedy.finsum_le`: the matroid greedy theorem.
* `TauCeti.Greedy.exists_isMaxWeightBase_superset`: extension to a base of maximum weight.

## References

* M. X. Goemans, *Lecture notes on matroid optimization*, 2011, Theorem 4.2.
* A. Schrijver, *A Course in Combinatorial Optimization*, 2017, Theorem 10.1.
-/

public section

open Set

namespace TauCeti

variable {α R : Type*} {P : Set α → Prop} {M : Matroid α} {w : α → R}
  {I J : Set α}

/-- `Greedy P w I` means that `I` is built from the empty set by successively inserting
an element of greatest weight among the new elements whose insertion satisfies `P`. -/
inductive Greedy [LE R] (P : Set α → Prop) (w : α → R) : Set α → Prop
  /-- The empty set starts the construction. -/
  | empty : Greedy P w ∅
  /-- Insert a new element of greatest weight among the feasible insertions. -/
  | step {I : Set α} (hI : Greedy P w I) {e : α} (he : e ∉ I) (hPe : P (insert e I))
      (hmax : ∀ ⦃f⦄, f ∉ I → P (insert f I) → w f ≤ w e) : Greedy P w (insert e I)

namespace Greedy

attribute [simp] Greedy.empty

/-- A greedily built set is finite. -/
theorem finite [LE R] (hI : Greedy P w I) : I.Finite := by
  induction hI with
  | empty => exact finite_empty
  | step _ _ _ _ ih => exact ih.insert _

/-- If the empty set satisfies the predicate, so does every greedily built set. -/
theorem prop [LE R] (hI : Greedy P w I) (hP : P ∅) : P I := by
  cases hI with
  | empty => exact hP
  | step _ _ hPe _ => exact hPe

section LinearOrder

variable [LinearOrder R]

/-- A greedily built set admits a further greedy insertion if the set of feasible new
elements is nonempty and finite. -/
theorem exists_insert (hI : Greedy P w I)
    (hfin : {e | e ∉ I ∧ P (insert e I)}.Finite)
    (hne : ∃ e ∉ I, P (insert e I)) : ∃ e ∉ I, Greedy P w (insert e I) := by
  obtain ⟨e, he, hmax⟩ := Set.exists_max_image _ w hfin hne
  exact ⟨e, he.1, hI.step he.1 he.2 fun _ hf hPf ↦ hmax _ ⟨hf, hPf⟩⟩

/-- If the feasible sets form a finite family closed under subsets and containing the empty
set, every greedily built set is contained in a greedily built maximal member. -/
theorem exists_maximal_superset (hI : Greedy P w I) (h₀ : P ∅) (hP : Antitone P)
    (hfin : {J | P J}.Finite) : ∃ B, Maximal P B ∧ Greedy P w B ∧ I ⊆ B := by
  have hfamily : {J | Greedy P w J ∧ I ⊆ J}.Finite :=
    hfin.subset fun _ hJ ↦ hJ.1.prop h₀
  obtain ⟨B, hB⟩ := hfamily.exists_maximal ⟨I, hI, Subset.rfl⟩
  refine ⟨B, ?_, hB.prop.1, hB.prop.2⟩
  by_contra hnot
  obtain ⟨e, he, hPe⟩ := Set.exists_insert_of_not_maximal (P := P)
    (fun _ _ hJ hKJ ↦ hP hKJ hJ) (hB.prop.1.prop h₀) hnot
  have hfin' : {e | e ∉ B ∧ P (insert e B)}.Finite :=
    hfin.of_injOn (f := fun e ↦ insert e B) (fun _ hf ↦ hf.2)
      ((Function.insert_injOn B).mono fun _ hf ↦ hf.1)
  obtain ⟨f, hf, hBf⟩ := hB.prop.1.exists_insert hfin' ⟨e, he, hPe⟩
  exact hf (hB.mem_of_prop_insert ⟨hBf, hB.prop.2.trans (subset_insert _ _)⟩)

/-- In a matroid with finite ground set, a greedily built set that is not a base admits
a further greedy insertion. -/
theorem exists_insert_of_not_isBase [M.Finite] (hI : Greedy M.Indep w I) (hB : ¬M.IsBase I) :
    ∃ e ∉ I, Greedy M.Indep w (insert e I) := by
  obtain ⟨B, hB'⟩ := M.exists_isBase
  obtain ⟨e, he, hIe⟩ := (hI.prop M.empty_indep).exists_insert_of_not_isBase hB hB'
  exact hI.exists_insert
    (M.ground_finite.subset fun f hf ↦ hf.2.subset_ground (mem_insert f I)) ⟨e, he.2, hIe⟩

/-- Every greedily built set in a matroid with finite ground set is contained in a greedily
built base. -/
theorem exists_isBase_superset [M.Finite] (hI : Greedy M.Indep w I) :
    ∃ B, M.IsBase B ∧ Greedy M.Indep w B ∧ I ⊆ B := by
  have hfin : {J | M.Indep J}.Finite :=
    M.ground_finite.finite_subsets.subset fun _ hJ ↦ Matroid.Indep.subset_ground hJ
  obtain ⟨B, hB, hBg, hIB⟩ :=
    hI.exists_maximal_superset M.empty_indep (fun _ _ hIJ hJ ↦ hJ.subset hIJ) hfin
  exact ⟨B, Matroid.isBase_iff_maximal_indep.2 hB, hBg, hIB⟩

end LinearOrder

section OrderedMonoid

variable [AddCommMonoid R] [Preorder R] [IsOrderedAddMonoid R]

/-- A greedily built independent set has greatest weight among the independent sets of
its cardinality, with no finiteness assumption on the matroid. -/
theorem finsum_le (hI : Greedy M.Indep w I) (hJ : M.Indep J) (hcard : J.encard = I.encard) :
    ∑ᶠ x ∈ J, w x ≤ ∑ᶠ x ∈ I, w x := by
  induction hI generalizing J with
  | empty =>
    have hJ₀ : J = ∅ := by simpa using hcard
    rw [hJ₀]
  | @step I hI e he _ hmax ih =>
    -- Augment the greedy prefix by an element of `J`. Removing that element from `J`
    -- leaves a competitor for the prefix, while the greedy choice dominates its weight.
    have hfin := hI.finite
    have hJfin : J.Finite := (hfin.insert e).finite_of_encard_le hcard.le
    rw [encard_insert_of_notMem he] at hcard
    have hlt : I.encard < J.encard := by
      rw [hcard, ENat.lt_add_one_iff hfin.encard_lt_top.ne]
    obtain ⟨f, hf, hIf⟩ := (hI.prop M.empty_indep).exists_insert_of_encard_lt hJ hlt
    have hcard' : (J \ {f}).encard = I.encard :=
      (ENat.addLECancellable_of_ne_top ENat.one_ne_top).inj_left.1 <|
        (encard_sdiff_singleton_add_one hf.1).trans hcard
    have hsum := ih (hJ.subset sdiff_subset) hcard'
    calc
      ∑ᶠ x ∈ J, w x = w f + ∑ᶠ x ∈ J \ {f}, w x := by
        rw [← finsum_mem_add_sdiff (singleton_subset_iff.2 hf.1) hJfin, finsum_mem_singleton]
      _ ≤ w e + ∑ᶠ x ∈ I, w x := add_le_add (hmax hf.2 hIf) hsum
      _ = ∑ᶠ x ∈ insert e I, w x := (finsum_mem_insert w he hfin).symm

/-- A greedily built base is a base of maximum weight. -/
theorem isMaxWeightBase (hI : Greedy M.Indep w I) (hB : M.IsBase I) : M.IsMaxWeightBase w I :=
  ⟨hB, fun _ hJ ↦ hI.finsum_le hJ.indep (hJ.encard_eq_encard_of_isBase hB)⟩

/-- When weights are nonnegative on the ground set, a greedily built base is optimal
among all independent sets. -/
theorem finsum_le_of_isBase (hI : Greedy M.Indep w I) (hB : M.IsBase I) (hJ : M.Indep J)
    (hw : ∀ e ∈ M.E, 0 ≤ w e) : ∑ᶠ x ∈ J, w x ≤ ∑ᶠ x ∈ I, w x := by
  obtain ⟨B, hB', hJB⟩ := hJ.exists_isBase_superset
  have hfin : B.Finite := hI.finite.finite_of_encard_le (hB'.encard_eq_encard_of_isBase hB).le
  have hJfin := hfin.subset hJB
  refine le_trans ?_ ((hI.isMaxWeightBase hB).finsum_le hB')
  rw [finsum_mem_eq_finite_toFinset_sum _ hJfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finite.toFinset_mono hJB)
    (fun x hx _ ↦ hw x (hB'.subset_ground (hfin.mem_toFinset.1 hx)))

end OrderedMonoid

/-- On a finite ground set, every greedily built set is contained in a base of maximum weight. -/
theorem exists_isMaxWeightBase_superset [AddCommMonoid R] [LinearOrder R] [IsOrderedAddMonoid R]
    [M.Finite] (hI : Greedy M.Indep w I) : ∃ B, M.IsMaxWeightBase w B ∧ I ⊆ B :=
  hI.exists_isBase_superset.imp fun _ ⟨hB, hBg, hIB⟩ ↦ ⟨hBg.isMaxWeightBase hB, hIB⟩

end Greedy

end TauCeti

namespace Matroid

/-- A matroid with finite ground set has a greedily built base. -/
theorem exists_greedy_isBase {α R : Type*} (M : Matroid α) [M.Finite] [LinearOrder R] (w : α → R) :
    ∃ B, M.IsBase B ∧ TauCeti.Greedy M.Indep w B :=
  (TauCeti.Greedy.empty (P := M.Indep) (w := w)).exists_isBase_superset.imp
    fun _ hB ↦ ⟨hB.1, hB.2.1⟩

end Matroid
