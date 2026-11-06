/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Multiset.Basic

/-!
# Sums of singletons over the preimage of a multiset under a partial equivalence

For a partial equivalence `e`, a set of points of the source whose images are exactly the
elements of a duplicate-free multiset `M` contained in the target is the image under `e.symm`
of `M`, each point counted once.

## Main statements

* `PartialEquiv.finsum_mem_singleton_eq_map`: the sum of the singletons over such a set is the
  image under `e.symm` of `M`.
-/

public section

namespace PartialEquiv

variable {X α : Type*}

/-- **Sums of singletons over a set cut out by a multiset.** Let `e` be a partial equivalence and
`T` a set whose elements are exactly the points of the source of `e` with image in a duplicate-free
multiset `M`, all of whose elements lie in the target of `e`. Then the sum of the singletons over
`T` is the image under `e.symm` of `M`. -/
theorem finsum_mem_singleton_eq_map (e : PartialEquiv X α) {M : Multiset α} (hM : M.Nodup)
    {T : Set X} (hmem : ∀ x', x' ∈ T ↔ x' ∈ e.source ∧ e x' ∈ M)
    (hroot : ∀ w ∈ M, w ∈ e.target) :
    ∑ᶠ x' ∈ T, ({x'} : Multiset X) = M.map e.symm := by
  classical
  have hpiece (x' : X) (hx' : x' ∈ T) : x' = e.symm (e x') :=
    (e.left_inv ((hmem x').1 hx').1).symm
  have hfin : T.Finite := by
    refine (M.toFinset.finite_toSet.image e.symm).subset fun x' hx' ↦ ?_
    exact ⟨e x', by simpa using ((hmem x').1 hx').2, (hpiece x' hx').symm⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_eq_multiset_sum,
    Multiset.sum_map_singleton]
  refine (Multiset.Nodup.ext hfin.toFinset.nodup (hM.map_on fun w hw w' hw' h ↦ ?_)).2
    fun x' ↦ ?_
  · exact e.symm.injOn (hroot w hw) (hroot w' hw') h
  · rw [Finset.mem_val, hfin.mem_toFinset, Multiset.mem_map]
    refine ⟨fun hx' ↦ ⟨e x', ((hmem x').1 hx').2, (hpiece x' hx').symm⟩, ?_⟩
    rintro ⟨w, hw, rfl⟩
    rw [hmem, e.right_inv (hroot w hw)]
    exact ⟨e.map_target (hroot w hw), hw⟩

end PartialEquiv
