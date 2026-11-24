/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.NhdsSet
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
import TauCeti.Logic.Equiv.PartialEquiv

/-!
# Germs of open partial homeomorphisms along a subset

Two maps out of a topological space have the same **germ along a subset `S`** when they agree
after shrinking to a neighbourhood of the whole of `S`, that is, when they are eventually equal
for the neighbourhood filter `𝓝ˢ S`. For `S` a single point this is the usual germ at a point; for
`S` the image of a submanifold it is the notion of germ in the neighbourhood theorems of
symplectic and contact geometry, where a map is only constructed on some neighbourhood of `S` and
all statements are insensitive to shrinking that neighbourhood.

This file shows that the operations on open partial homeomorphisms, and so on partial
diffeomorphisms through `PartialDiffeomorph.toOpenPartialHomeomorph`, descend to germs along
subsets of their sources. Only the openness of source and target, continuity and the inverse laws
are used.

* **Inverse.** Near a subset `S` of the source, `e⁻¹ ∘ e` is the identity, and near a subset of
  the target `e ∘ e⁻¹` is
  (`OpenPartialHomeomorph.symm_comp_eventuallyEq_id`,
  `OpenPartialHomeomorph.comp_symm_eventuallyEq_id`).
  The germ of `e⁻¹` along `e(S)` depends only on the germ of `e` along `S`
  (`OpenPartialHomeomorph.symm_eventuallyEq_nhdsSet_image`).
* **Composition.** The germ of `f ∘ e` along `S` depends only on the germ of `e` along `S` and the
  germ of `f` along `e(S)` (`OpenPartialHomeomorph.trans_eventuallyEq_nhdsSet`), because `e` maps
  the neighbourhoods of `S` to those of any set containing `e(S)`
  (`OpenPartialHomeomorph.tendsto_nhdsSet`).
* **Comparison.** If `e₁` and `e₂` agree on a subset `S` of both sources, then `e₁` and `e₂ ∘ θ`
  have the same germ along `S`, for the comparison `θ = e₂⁻¹ ∘ e₁` (`e₁.trans e₂.symm`)
  (`OpenPartialHomeomorph.eventuallyEq_comp_trans_symm`). The pointwise facts behind this are
  `PartialEquiv.subset_trans_symm_source`, `PartialEquiv.trans_symm_apply_eq_self` and
  `PartialEquiv.apply_trans_symm_apply`.

The restriction to an open set containing `S` (`OpenPartialHomeomorph.restrOpen`) has the same
underlying map, hence the same germ along `S`.
-/

public section

open Filter Set Topology

namespace OpenPartialHomeomorph

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {S : Set X}

/-! ### Inverses and composites of germs -/

/-- An open partial homeomorphism maps the neighbourhoods of a subset `S` of its source to those of
any set `T` containing `e(S)`. -/
theorem tendsto_nhdsSet (e : OpenPartialHomeomorph X Y) {T : Set Y} (hS : S ⊆ e.source)
    (hST : MapsTo e S T) : Tendsto e (𝓝ˢ S) (𝓝ˢ T) :=
  e.continuousOn.tendsto_nhdsSet (e.open_source.mem_nhdsSet.2 hS) hST

/-- **The inverse undoes an open partial homeomorphism on germs.** Near a subset `S` of the source,
`e⁻¹ ∘ e` is the identity. -/
theorem symm_comp_eventuallyEq_id (e : OpenPartialHomeomorph X Y) (hS : S ⊆ e.source) :
    ⇑e.symm ∘ e =ᶠ[𝓝ˢ S] id :=
  mem_of_superset (e.open_source.mem_nhdsSet.2 hS) fun _ hx ↦ e.left_inv hx

/-- **An open partial homeomorphism undoes its inverse on germs.** Near a subset `T` of the target,
`e ∘ e⁻¹` is the identity. -/
theorem comp_symm_eventuallyEq_id (e : OpenPartialHomeomorph X Y) {T : Set Y}
    (hT : T ⊆ e.target) : ⇑e ∘ e.symm =ᶠ[𝓝ˢ T] id :=
  e.symm.symm_comp_eventuallyEq_id hT

/-- **The germ of the inverse depends only on the germ.** If two open partial homeomorphisms agree
near a subset `S` of both sources, their inverses agree near `e(S)`. -/
theorem symm_eventuallyEq_nhdsSet_image {e e' : OpenPartialHomeomorph X Y}
    (h : ⇑e =ᶠ[𝓝ˢ S] e') (he : S ⊆ e.source) (he' : S ⊆ e'.source) :
    ⇑e.symm =ᶠ[𝓝ˢ (e '' S)] e'.symm := by
  have hT : e '' S ⊆ e.target := image_subset_iff.2 fun x hx ↦ e.map_source (he hx)
  -- `e⁻¹` maps the neighbourhoods of `e(S)` to those of `S`.
  have hsymm : Tendsto e.symm (𝓝ˢ (e '' S)) (𝓝ˢ S) :=
    e.symm.tendsto_nhdsSet hT (by rintro _ ⟨x, hx, rfl⟩; rwa [e.left_inv (he hx)])
  filter_upwards [hsymm.eventually (h.and (e'.open_source.mem_nhdsSet.2 he')),
    e.open_target.mem_nhdsSet.2 hT] with y ⟨hy, hye'⟩ hyT
  -- At `y = e x`, both inverses return `x`, since `e' x = e x = y`.
  calc e.symm y = e'.symm (e' (e.symm y)) := (e'.left_inv hye').symm
    _ = e'.symm y := by rw [← hy, e.right_inv hyT]

/-- **The germ of a composite depends only on the germs of its factors.** If `e` and `e'` agree
near a subset `S` of the source of `e`, and `f` and `f'` agree near `e(S)`, then `f ∘ e` and
`f' ∘ e'` agree near `S`. -/
theorem trans_eventuallyEq_nhdsSet {e e' : OpenPartialHomeomorph X Y}
    {f f' : OpenPartialHomeomorph Y Z} (he : ⇑e =ᶠ[𝓝ˢ S] e') (hf : ⇑f =ᶠ[𝓝ˢ (e '' S)] f')
    (hS : S ⊆ e.source) : ⇑(e.trans f) =ᶠ[𝓝ˢ S] e'.trans f' := by
  rw [coe_trans, coe_trans]
  exact (hf.comp_tendsto (e.tendsto_nhdsSet hS (mapsTo_image e S))).trans (he.fun_comp f')

/-! ### Comparing two open partial homeomorphisms which agree along a subset -/

/-- If `e₁` and `e₂` agree on a subset `S` of both sources, then `e₁` and `e₂ ∘ θ` have the same
germ along `S`, for the comparison `θ = e₂⁻¹ ∘ e₁`. -/
theorem eventuallyEq_comp_trans_symm {e₁ e₂ : OpenPartialHomeomorph X Y} (h₁ : S ⊆ e₁.source)
    (h₂ : S ⊆ e₂.source) (h : EqOn e₁ e₂ S) : ⇑e₁ =ᶠ[𝓝ˢ S] e₂ ∘ e₁.trans e₂.symm :=
  mem_of_superset ((e₁.trans e₂.symm).open_source.mem_nhdsSet.2
    (PartialEquiv.subset_trans_symm_source (e₁ := e₁.toPartialEquiv) h₁ h₂ h))
    fun _ hx ↦ (PartialEquiv.apply_trans_symm_apply (e₁ := e₁.toPartialEquiv) hx).symm

end OpenPartialHomeomorph
