/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
import TauCeti.Analysis.Sobolev.Local.Locality

/-!
# Locality of the weak Cauchy–Riemann equation

The planar weak equation `TauCeti.IsWeakCauchyRiemannOn p U J η u` has the sheaf property in
the set `U`: it holds on `U` exactly when it holds on a relative neighbourhood of each point of
`U`, and it holds on `U` exactly when it holds on the traces `U ∩ O i` of an open cover. The set
`U` need not be open, so for a half-disc the neighbourhoods are relative ones in the closed upper
half-plane and the `Lᵖ` bounds reach the real axis, as in the definition. The linear equation
`TauCeti.IsWeakLinearCauchyRiemannOn` is an abbreviation for a special case, so these results
apply to it directly.

## Main results

* `TauCeti.isWeakCauchyRiemannOn_iff_forall_inter`: the equation on `U` is the equation on
  `U ∩ O i` for every member of an open cover `O` of `U`.
* `TauCeti.isWeakCauchyRiemannOn_iff_locally`: the equation holds on `U` exactly when every point
  of `U` has a neighbourhood within `U` on which it holds.
* `TauCeti.isWeakCauchyRiemannOn_iSup_iff`: the sheaf property for open covers of an open set.

The codomain is assumed complete: an empty cover carries no weak derivative to supply the
completeness that the weak-derivative predicate demands.

## Implementation notes

Continuity is local by `continuousOn_of_locally_continuousOn`. Membership of `u` in `W^{1,p}_loc`
of `U` is glued by `TauCeti.memWkpLoc_iff_forall_inter`, which also produces a locally `Lᵖ` weak
derivative on the interior of `U`. For the almost-everywhere equation it suffices, by
`TauCeti.isWeakCauchyRiemannOn_iff_forall_hasWeakFDerivOn`, to check it for an arbitrary weak
derivative `D` on the interior of `U`. Its restriction is a weak derivative on the interior of
each `U ∩ O i`, which is `interior U ∩ O i`, so the equation holds almost everywhere there. These
open sets cover the interior of `U`, and countably many of them suffice since `ℂ` is second
countable.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1 and Appendix B.4.
-/

public section

open MeasureTheory Set TopologicalSpace Filter
open scoped Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {p : ENNReal} {U : Set ℂ} {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V}

/-- **Locality on an open cover.** The weak Cauchy–Riemann equation holds on `U` exactly when it
holds on the trace `U ∩ O i` of every member of an open cover `O` of `U`. -/
theorem isWeakCauchyRiemannOn_iff_forall_inter {ι : Type*} (O : ι → Opens ℂ)
    (hU : U ⊆ ⋃ i, (O i : Set ℂ)) :
    IsWeakCauchyRiemannOn p U J η u ↔ ∀ i, IsWeakCauchyRiemannOn p (U ∩ O i) J η u := by
  refine ⟨fun h i => h.mono inter_subset_left, fun h => ?_⟩
  have hint : ∀ i, interior (U ∩ O i) = interior U ∩ O i := fun i => by
    rw [interior_inter, (O i).isOpen.interior_eq]
  refine isWeakCauchyRiemannOn_iff_forall_hasWeakFDerivOn.2 ⟨?_, ?_, fun D hD => ?_⟩
  · refine continuousOn_of_locally_continuousOn fun x hx => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hU hx)
    exact ⟨O i, (O i).isOpen, hi, (h i).continuousOn⟩
  · exact (memWkpLoc_iff_forall_inter O hU).2 fun i => (h i).memWkpLoc_one
  · obtain ⟨T, hT, hTU⟩ := isOpen_iUnion_countable (fun i => interior U ∩ O i)
      fun i => isOpen_interior.inter (O i).isOpen
    have hcover : interior U = ⋃ i ∈ T, interior U ∩ O i := by
      rw [hTU, ← inter_iUnion]
      exact (inter_eq_left.2 (interior_subset.trans hU)).symm
    rw [hcover, ae_restrict_biUnion_iff _ hT]
    intro i _
    rw [← hint i]
    refine (h i).ae_eq_of_hasWeakFDerivOn (hD.mono ?_)
    exact interior_mono inter_subset_left

/-- **Locality.** The weak Cauchy–Riemann equation holds on `U` exactly when every point of `U`
has a neighbourhood within `U` on which it holds. -/
theorem isWeakCauchyRiemannOn_iff_locally :
    IsWeakCauchyRiemannOn p U J η u ↔ ∀ x ∈ U, ∃ W ∈ 𝓝[U] x, IsWeakCauchyRiemannOn p W J η u := by
  refine ⟨fun h _ _ => ⟨U, self_mem_nhdsWithin, h⟩, fun h => ?_⟩
  have hO : ∀ x : U, ∃ O : Opens ℂ, (x : ℂ) ∈ O ∧ IsWeakCauchyRiemannOn p (U ∩ O) J η u :=
    fun x => by
      obtain ⟨W, hW, huW⟩ := h x x.2
      obtain ⟨O, hO, hxO, hOW⟩ := mem_nhdsWithin.1 hW
      exact ⟨⟨O, hO⟩, hxO, huW.mono fun z hz => hOW ⟨hz.2, hz.1⟩⟩
  choose O hxO huO using hO
  exact (isWeakCauchyRiemannOn_iff_forall_inter O
    fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxO ⟨x, hx⟩⟩).2 huO

/-- **The sheaf property.** The weak Cauchy–Riemann equation holds on a union of open sets
exactly when it holds on each of them. -/
theorem isWeakCauchyRiemannOn_iSup_iff {ι : Type*} (W : ι → Opens ℂ) :
    IsWeakCauchyRiemannOn p (⨆ i, W i : Opens ℂ) J η u ↔
      ∀ i, IsWeakCauchyRiemannOn p (W i) J η u := by
  rw [isWeakCauchyRiemannOn_iff_forall_inter W (by simp)]
  simp only [Opens.coe_iSup, inter_eq_right.2 (subset_iUnion (fun i => (W i : Set ℂ)) _)]

end TauCeti
