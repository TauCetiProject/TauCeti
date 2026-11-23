/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Irreducible

/-!
# Irreducible components: preimages and the component through a point

A continuous surjection whose preimages of irreducible components are irreducible induces, by
taking preimages, a bijection between the irreducible components of the target and those of the
source. Over a field, this recognises base changes along which every irreducible component stays
irreducible, that is, geometrically irreducible components.

Mathlib's `irreducibleComponent x` is a maximal irreducible set containing `x`. We bundle it as
an element `irreducibleComponentOf x` of `irreducibleComponents α`, giving a map from points to
irreducible components. When every point lies on a unique irreducible component, as in a scheme
whose stalks are integral domains, this map sends a point to the component containing it.
-/

public section

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- If `f` is a continuous surjection and the preimage of every irreducible component of `Y` is
irreducible, then `Z ↦ f ⁻¹' Z` maps the irreducible components of `Y` bijectively onto those
of `X`. -/
theorem Function.Surjective.bijOn_preimage_irreducibleComponents {f : X → Y}
    (hf : Function.Surjective f) (hc : Continuous f)
    (h : ∀ Z ∈ irreducibleComponents Y, IsIrreducible (f ⁻¹' Z)) :
    BijOn (f ⁻¹' ·) (irreducibleComponents Y) (irreducibleComponents X) := by
  have hmaps : MapsTo (f ⁻¹' ·) (irreducibleComponents Y) (irreducibleComponents X) := by
    refine fun Z hZ ↦ ⟨h Z hZ, fun T hT hZT ↦ ?_⟩
    have hle : Z ⊆ closure (f '' T) :=
      (image_preimage_eq Z hf ▸ image_mono hZT).trans subset_closure
    exact image_subset_iff.mp
      (subset_closure.trans (hZ.2 (hT.image f hc.continuousOn).closure hle))
  refine ⟨hmaps, (Set.preimage_injective.mpr hf).injOn, fun T hT ↦ ?_⟩
  obtain ⟨Z, hZ, hTZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure (f '' T)) (hT.1.image f hc.continuousOn).closure
  have hle : T ⊆ f ⁻¹' Z := image_subset_iff.mp (subset_closure.trans hTZ)
  exact ⟨Z, hZ, subset_antisymm (hT.2 (hmaps hZ).1 hle) hle⟩

/-- A homeomorphism `h : X ≃ₜ Y` induces a bijection of irreducible components, sending a
component to its image under `h` (`Homeomorph.coe_irreducibleComponentsEquiv_apply`). -/
def Homeomorph.irreducibleComponentsEquiv (h : X ≃ₜ Y) :
    irreducibleComponents X ≃ irreducibleComponents Y :=
  (irreducibleComponentsEquivOfIsPreirreducibleFiber h h.continuous h.isOpenMap
    (fun _ ↦ (subsingleton_singleton.preimage h.injective).isPreirreducible)
    h.surjective).symm.toEquiv

/-- The bijection of irreducible components induced by a homeomorphism sends a component to its
image. -/
@[simp]
theorem Homeomorph.coe_irreducibleComponentsEquiv_apply (h : X ≃ₜ Y) (c : irreducibleComponents X) :
    (h.irreducibleComponentsEquiv c : Set Y) = h '' c :=
  (rfl)

namespace TauCeti

variable {α : Type*} [TopologicalSpace α]

/-- An irreducible component containing the point `x`, namely Mathlib's
`irreducibleComponent x`, as an element of `irreducibleComponents α`. -/
noncomputable def irreducibleComponentOf (x : α) : irreducibleComponents α :=
  ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩

/-- The carrier of `irreducibleComponentOf x` is Mathlib's `irreducibleComponent x`. -/
@[simp]
theorem coe_irreducibleComponentOf (x : α) :
    (irreducibleComponentOf x : Set α) = irreducibleComponent x :=
  (rfl)

/-- A point lies on the irreducible component `irreducibleComponentOf x`. -/
theorem mem_irreducibleComponentOf (x : α) : x ∈ (irreducibleComponentOf x : Set α) :=
  mem_irreducibleComponent

/-- When `x` lies on exactly one irreducible component, `irreducibleComponentOf x` is the
irreducible component containing `x`. -/
theorem irreducibleComponentOf_eq_iff_of_existsUnique {x : α}
    (h : ∃! c : irreducibleComponents α, x ∈ (c : Set α)) {c : irreducibleComponents α} :
    irreducibleComponentOf x = c ↔ x ∈ (c : Set α) :=
  ⟨fun hc ↦ hc ▸ mem_irreducibleComponentOf x, h.unique (mem_irreducibleComponentOf x)⟩

end TauCeti
