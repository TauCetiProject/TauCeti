/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Local homeomorphisms: local path-connectedness, local inverses, products and base change

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
* `IsLocalHomeomorph.prodMap`: the product of two local homeomorphisms is a local homeomorphism.
* `IsLocalHomeomorph.pullback_snd`: the base change of a local homeomorphism along a continuous
  map is a local homeomorphism.
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

section Prod

variable {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace W]

/-- **The product of two local homeomorphisms is a local homeomorphism**, with the product of
local charts as local charts. -/
theorem _root_.IsLocalHomeomorph.prodMap {f : X → Y} {g : Z → W} (hf : IsLocalHomeomorph f)
    (hg : IsLocalHomeomorph g) : IsLocalHomeomorph (Prod.map f g) := by
  refine IsLocalHomeomorph.mk _ fun p ↦ ?_
  obtain ⟨e, he, rfl⟩ := hf p.1
  obtain ⟨e', he', rfl⟩ := hg p.2
  exact ⟨e.prod e', ⟨he, he'⟩, fun _ _ ↦ rfl⟩

end Prod

section Pullback

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- **Local homeomorphisms are stable under base change.** If `f : X → Y` is a local
homeomorphism and `g : Z → Y` is continuous, the projection from the fiber product `X ×_Y Z` to
`Z` is a local homeomorphism. Over a local chart `e` of `f`, the fiber product is identified with
`g⁻¹ e.target` by `(x, z) ↦ z`, with inverse `z ↦ (e.symm (g z), z)`. -/
theorem _root_.IsLocalHomeomorph.pullback_snd {f : X → Y} {g : Z → Y} (hf : IsLocalHomeomorph f)
    (hg : Continuous g) : IsLocalHomeomorph (Function.Pullback.snd : f.Pullback g → Z) := by
  refine isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun q ↦ ?_
  obtain ⟨e, he, rfl⟩ := hf q.fst
  have hfst : Continuous (Function.Pullback.fst : (⇑e).Pullback g → X) :=
    continuous_fst.comp continuous_subtype_val
  have hsnd : Continuous (Function.Pullback.snd : (⇑e).Pullback g → Z) :=
    continuous_snd.comp continuous_subtype_val
  have hpb (p : (⇑e).Pullback g) : e p.fst = g p.snd := p.2
  let U : Set ((⇑e).Pullback g) := Function.Pullback.fst ⁻¹' e.source
  let W : Set Z := g ⁻¹' e.target
  have hgU (p : U) : g p.1.snd ∈ e.target := hpb p.1 ▸ e.map_source p.2
  have hfW (w : W) : e (e.symm (g w)) = g w := e.right_inv w.2
  -- Over the chart `e`, the projection identifies `U` with `W`.
  let φ : U ≃ₜ W :=
    { toFun p := ⟨p.1.snd, hgU p⟩
      invFun w := ⟨⟨(e.symm (g w), w), hfW w⟩, e.map_target w.2⟩
      left_inv p := by
        refine Subtype.ext (Subtype.ext (Prod.ext ?_ rfl))
        -- The first component of the round trip is `e.symm (g p.1.snd)` by definition of `φ`.
        exact (congrArg e.symm (hpb p.1)).symm.trans (e.left_inv p.2)
      right_inv _ := rfl
      continuous_toFun := (hsnd.comp continuous_subtype_val).subtype_mk _
      continuous_invFun :=
        (((e.continuousOn_symm.comp_continuous (hg.comp continuous_subtype_val) fun w ↦ w.2).prodMk
          continuous_subtype_val).subtype_mk _).subtype_mk _ }
  refine ⟨U, (e.open_source.preimage hfst).mem_nhds he, ?_⟩
  exact ((e.open_target.preimage hg).isOpenEmbedding_subtypeVal.comp φ.isOpenEmbedding :)

end Pullback

end TauCeti
