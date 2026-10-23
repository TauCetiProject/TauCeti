/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# Local homeomorphisms: local path-connectedness and local inverses

A local homeomorphism `p : E → B` identifies a neighbourhood of each point of `E` with an open
subset of `B`, so `E` inherits any property of `B` that is local and stable under passing to open
subspaces. This file records that for local path-connectedness.

The intended use is a covering map, whose total space is therefore locally path-connected as soon
as the base is; this is what lets the covers built over a locally path-connected base be fed back
into results that require a locally path-connected source, such as the lifting criterion.

A local inverse `L` of `p` composed with `p` is a local deck transformation of `p`. Near a point
`z` it agrees with every local deck transformation of `p` that is continuous at `z` and sends `z`
into the target of `L`. This is what identifies the transition maps of charts pushed forward along
`p` with deck transformations.

## Main results

* `IsLocalHomeomorph.locallyPathConnectedSpace`: the domain of a local homeomorphism into a
  locally path-connected space is locally path-connected.
* `IsLocalHomeomorph.localInverseAt_comp_eventuallyEq`: near `z`, a local inverse composed with
  `p` agrees with any continuous local deck transformation sending `z` into the target of that
  local inverse.
-/

public section

open Topology

namespace TauCeti

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

/-- **A local homeomorphism with locally path-connected codomain has locally path-connected
domain.** In particular the total space of a covering of a locally path-connected space is
locally path-connected. -/
theorem _root_.IsLocalHomeomorph.locallyPathConnectedSpace [LocallyPathConnectedSpace B]
    {p : E → B} (hp : IsLocalHomeomorph p) : LocallyPathConnectedSpace E := by
  constructor
  intro e
  rw [Filter.hasBasis_self]
  intro U hU
  obtain ⟨W, hWU, hWopen, heW⟩ := mem_nhds_iff.mp hU
  let φ := hp.localInverseAt e
  have hpe_source : p e ∈ φ.source := hp.apply_self_mem_localInverseAt_source
  have hsource : IsOpen (φ.source ∩ φ ⁻¹' W) :=
    φ.continuousOn_toFun.isOpen_inter_preimage φ.open_source hWopen
  have hpe : p e ∈ φ.source ∩ φ ⁻¹' W := by
    refine ⟨hpe_source, ?_⟩
    simpa only [Set.mem_preimage, φ, hp.localInverseAt_apply_self] using heW
  obtain ⟨V, ⟨hVopen, hpeV, hVpath⟩, hVsub⟩ :=
    (isOpen_isPathConnected_basis (p e)).mem_iff.mp (hsource.mem_nhds hpe)
  refine ⟨φ '' V, ?_, hVpath.image' (φ.continuousOn_toFun.mono fun _ hv => (hVsub hv).1), ?_⟩
  · exact (φ.isOpen_image_of_subset_source hVopen
      (hVsub.trans Set.inter_subset_left)).mem_nhds ⟨p e, hpeV, by simp [φ]⟩
  · rintro z ⟨y, hyV, rfl⟩
    exact hWU (hVsub hyV).2

/-- Let `L` be a local inverse of a local homeomorphism `p` at `e`. If `φ` is continuous at `z`,
satisfies `p ∘ φ = p` near `z`, and sends `z` into the target of `L`, then `L ∘ p` agrees with `φ`
near `z`. -/
theorem _root_.IsLocalHomeomorph.localInverseAt_comp_eventuallyEq {p : E → B}
    (hp : IsLocalHomeomorph p) {e z : E} {φ : E → E} (hφ : ContinuousAt φ z)
    (hφz : φ z ∈ (hp.localInverseAt e).target) (hpφ : p ∘ φ =ᶠ[𝓝 z] p) :
    hp.localInverseAt e ∘ p =ᶠ[𝓝 z] φ := by
  set L := hp.localInverseAt e
  filter_upwards [hφ.preimage_mem_nhds (L.open_target.mem_nhds hφz), hpφ] with w hw hpw
  have hL : L (L.symm (φ w)) = φ w := L.right_inv hw
  rw [hp.localInverseAt_symm] at hL
  rwa [Function.comp_apply, ← hpw]

end TauCeti
