/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousOn
public import TauCeti.CategoryTheory.Category.QuiverTotal

/-!
# Continuity of composition of total arrows

Let `C` be a category whose total arrows `Quiver.Total C` carry a topology, as for a topological
groupoid, and suppose composition `Quiver.Total.comp` is continuous on the subspace of composable
pairs. If two continuous local sections of the source compose at a point to an arrow in an open
set, then they compose into that open set at every nearby point
(`TauCeti.eventually_comp_mem`). This is how local bisections of an étale groupoid are seen to
compose like the arrows they pass through.
-/

public section

open Set Topology CategoryTheory

namespace TauCeti

variable {C : Type*} [Category C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]

/-- If composition of total arrows is continuous and two local sections `σ` and `τ` of the source
compose at `x` to an arrow in an open set `O`, then they compose into `O` at every source near
`x`. Here `σ y` is followed by `τ` at its target. -/
theorem eventually_comp_mem
    (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      p.1.1.comp p.1.2 p.2)
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C))
    {σ τ : C → Quiver.Total C} {S T : Set C} (hσ : ContinuousOn σ S) (hτ : ContinuousOn τ T)
    (hS : IsOpen S) (hT : IsOpen T) (hτl : ∀ z ∈ T, (τ z).left = z) {x : C} (hxS : x ∈ S)
    (hxT : (σ x).right ∈ T) {O : Set (Quiver.Total C)} (hO : IsOpen O)
    (hOx : ∀ h, (σ x).comp (τ (σ x).right) h ∈ O) :
    ∀ᶠ y in 𝓝 x, ∀ h : (σ y).right = (τ (σ y).right).left, (σ y).comp (τ (σ y).right) h ∈ O := by
  have hσr : ContinuousOn (fun y ↦ (σ y).right) S := ht.comp_continuousOn hσ
  set D := S ∩ (fun y ↦ (σ y).right) ⁻¹' T
  have hD : IsOpen D := hσr.isOpen_inter_preimage hS hT
  -- On `D` both sections are defined, and their composite is continuous.
  let Φ : D → Quiver.Total C := fun y ↦ (σ y).comp (τ (σ y).right) (hτl _ y.2.2).symm
  have hΦ : Continuous Φ := hc.comp <| Continuous.subtype_mk
    ((hσ.comp_continuous continuous_subtype_val fun y ↦ y.2.1).prodMk
      (hτ.comp_continuous (hσr.comp_continuous continuous_subtype_val fun y ↦ y.2.1)
        fun y ↦ y.2.2)) fun y ↦ (hτl _ y.2.2).symm
  rw [← hD.isOpenMap_subtype_val.map_nhds_eq continuous_subtype_val.continuousAt
    (x := ⟨x, hxS, hxT⟩)]
  exact Filter.eventually_map.2
    ((hΦ.continuousAt.eventually_mem (hO.mem_nhds (hOx _))).mono fun y hy _ ↦ hy)

end TauCeti
