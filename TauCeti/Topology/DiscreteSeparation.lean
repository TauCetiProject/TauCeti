/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Closure

import Mathlib.Topology.ClusterPt

/-!
# Shrinking an open set to separate part of a non-accumulating set

The open ambient set `V ⊇ K` shrinks to an open neighbourhood of `K` meeting `Z` in exactly
`K ∩ Z` if and only if every point of `K` avoids the closure of `Z \ K`. This is the
localization step for residue computations — a contour region is
shrunk until the only singularities it contains are the intended ones.

## Main declarations

* `TauCeti.exists_isOpen_inter_eq_iff_notMem_closure` (with the accumulation-hypothesis
  corollary `TauCeti.exists_isOpen_inter_eq_of_not_accPt`).
-/

public section

namespace TauCeti

/-- Inside an open ambient set `V ⊇ K`, `K` has an open neighbourhood `U ⊆ V` meeting `Z`
exactly in `K ∩ Z` if and only if no point of `K` lies in the closure of `Z \ K`; for the
reverse direction, remove that closure from `V`. -/
theorem exists_isOpen_inter_eq_iff_notMem_closure {X : Type*} [TopologicalSpace X]
    {V Z K : Set X} (hV : IsOpen V) (hKV : K ⊆ V) :
    (∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ U ⊆ V ∧ U ∩ Z = K ∩ Z) ↔
      ∀ x ∈ K, x ∉ closure (Z \ K) := by
  refine ⟨fun ⟨U, hU, hKU, _, hUZ⟩ x hx hxc => ?_, fun hK => ⟨V \ closure (Z \ K),
    hV.sdiff isClosed_closure, fun x hx => ⟨hKV hx, hK x hx⟩, Set.sdiff_subset, ?_⟩⟩
  · obtain ⟨z, hzU, hzZ, hzK⟩ := mem_closure_iff.mp hxc U hU (hKU hx)
    exact hzK (hUZ.subset ⟨hzU, hzZ⟩).1
  · grind [subset_closure]

/-- The separation under the stronger hypothesis that no point of `K` is an accumulation
point of `Z` at all. -/
theorem exists_isOpen_inter_eq_of_not_accPt {X : Type*} [TopologicalSpace X] {V Z K : Set X}
    (hV : IsOpen V) (hKV : K ⊆ V)
    (hacc : ∀ x ∈ K, ¬AccPt x (Filter.principal Z)) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ U ⊆ V ∧ U ∩ Z = K ∩ Z := by
  refine (exists_isOpen_inter_eq_iff_notMem_closure hV hKV).mpr fun x hx hxc => hacc x hx ?_
  rw [accPt_principal_iff_nhdsWithin]
  exact (mem_closure_iff_nhdsWithin_neBot.mp hxc).mono
    (nhdsWithin_mono _ (Set.sdiff_subset_sdiff_right (Set.singleton_subset_iff.mpr hx)))

end TauCeti

end
