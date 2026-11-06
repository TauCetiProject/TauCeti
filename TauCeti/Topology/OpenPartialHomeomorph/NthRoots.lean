/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Sums over coordinate roots in a chart

For a chart `e : OpenPartialHomeomorph X ℂ`, a set of points whose coordinates are exactly the
`m`-th roots of a nonzero `s` is the image under `e.symm` of the roots, each counted once.

## Main statements

* `OpenPartialHomeomorph.finsum_mem_singleton_eq_map_nthRoots`: the sum of the singletons over
  such a set is the image under `e.symm` of the multiset of `m`-th roots of `s`.
-/

public section

open Polynomial

namespace OpenPartialHomeomorph

variable {X : Type*} [TopologicalSpace X]

/-- **Sums over a set of coordinate `m`-th roots.** Let `e` be a chart and `T` a set of points of
the domain of `e` whose coordinates are exactly the `m`-th roots of a nonzero `s`, all of whose
roots lie in the target of `e`. Then the sum of the singletons over `T` is the image under
`e.symm` of the multiset of `m`-th roots of `s`. -/
theorem finsum_mem_singleton_eq_map_nthRoots {m : ℕ} (hm : 0 < m) {s : ℂ} (hs : s ≠ 0)
    (e : OpenPartialHomeomorph X ℂ) {T : Set X}
    (hmem : ∀ x', x' ∈ T ↔ x' ∈ e.source ∧ e x' ^ m = s)
    (hroot : ∀ w : ℂ, w ^ m = s → w ∈ e.target) :
    ∑ᶠ x' ∈ T, ({x'} : Multiset X) = (nthRoots m s).map e.symm := by
  have hpiece (x' : X) (hx' : x' ∈ T) : x' = e.symm (e x') :=
    (e.left_inv ((hmem x').1 hx').1).symm
  have hfin : T.Finite := by
    refine ((nthRootsFinset m s).finite_toSet.image e.symm).subset fun x' hx' ↦ ?_
    exact ⟨e x', by simpa [mem_nthRootsFinset hm] using ((hmem x').1 hx').2,
      (hpiece x' hx').symm⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_eq_multiset_sum,
    Multiset.sum_map_singleton]
  have hnodup : (nthRoots m s).Nodup :=
    (Complex.isPrimitiveRoot_exp m hm.ne').nthRoots_nodup hs
  refine (Multiset.Nodup.ext hfin.toFinset.nodup (hnodup.map_on fun w hw w' hw' h ↦ ?_)).2
    fun x' ↦ ?_
  · rw [mem_nthRoots hm] at hw hw'
    exact e.symm.injOn (hroot w hw) (hroot w' hw') h
  · rw [Finset.mem_val, hfin.mem_toFinset, Multiset.mem_map]
    refine ⟨fun hx' ↦ ⟨e x', (mem_nthRoots hm).2 ((hmem x').1 hx').2, (hpiece x' hx').symm⟩,
      ?_⟩
    rintro ⟨w, hw, rfl⟩
    rw [mem_nthRoots hm] at hw
    rw [hmem, e.right_inv (hroot w hw)]
    exact ⟨e.map_target (hroot w hw), hw⟩

end OpenPartialHomeomorph
