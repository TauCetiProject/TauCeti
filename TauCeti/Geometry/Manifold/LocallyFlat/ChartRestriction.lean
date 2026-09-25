/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Restricting a chart to a parametrized coordinate slice

An ambient chart restricts to a chart on a subtype when membership in the subtype is detected by a
parametrized coordinate slice.  This file packages the common topological construction used by
the boundary-chart construction in `TauCeti.Geometry.Manifold.Boundary.Charts` and by subgroup
slice charts.

## Main definition

* `OpenPartialHomeomorph.subtypeCoord` restricts an ambient chart to a subtype and reads its
  coordinates through a retraction onto the parametrized slice.
-/

public section

open Set Topology

namespace OpenPartialHomeomorph

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

open scoped Classical in
/-- Restrict an ambient chart to a subtype represented by a parametrized coordinate slice.

The map `ι : Z → Y` parametrizes the slice and `π : Y → Z` reads its coordinates.  The hypotheses
say that ambient inverse images of slice points belong to `s`, that points of `s` visible in the
chart lie on the slice, and that `π` is a left inverse of `ι`.  Outside the target, the inverse is
assigned the base point `x₀`; its value there is irrelevant to an open partial homeomorphism. -/
noncomputable def subtypeCoord (e : OpenPartialHomeomorph X Y) (s : Set X) (x₀ : s)
    (ι : Z → Y) (π : Y → Z)
    (hι : ∀ {z}, ι z ∈ e.target → e.symm (ι z) ∈ s)
    (hslice : ∀ {x}, x ∈ e.source → x ∈ s → ι (π (e x)) = e x)
    (hπι : Function.LeftInverse π ι) (hιc : Continuous ι) (hπc : Continuous π) :
    OpenPartialHomeomorph s Z where
  toFun x := π (e x.1)
  invFun z := if h : ι z ∈ e.target then ⟨e.symm (ι z), hι h⟩ else x₀
  source := Subtype.val ⁻¹' e.source
  target := ι ⁻¹' e.target
  map_source' x hx := by
    -- Expose the fields currently being defined; their characteristic lemmas are available only
    -- after `subtypeCoord` has been constructed.
    change ι (π (e x.1)) ∈ e.target
    rw [hslice hx x.2]
    exact e.map_source hx
  map_target' z hz := by
    simp only [mem_preimage] at hz ⊢
    rw [dite_eq_left hz]
    exact e.map_target hz
  left_inv' x hx := by
    have htarget : ι (π (e x.1)) ∈ e.target := by
      rw [hslice hx x.2]
      exact e.map_source hx
    rw [dite_eq_left htarget]
    apply Subtype.ext
    -- Reduce equality in the subtype and unfold the selected inverse branch.
    change e.symm (ι (π (e x.1))) = x.1
    rw [hslice hx x.2, e.left_inv hx]
  right_inv' z hz := by
    simp only [mem_preimage] at hz
    rw [dite_eq_left hz]
    change π (e (e.symm (ι z))) = z
    rw [e.right_inv hz]
    exact hπι z
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage hιc
  continuousOn_toFun :=
    hπc.comp_continuousOn
      (e.continuousOn.comp continuous_subtype_val.continuousOn (mapsTo_preimage _ _))
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr
      (e.symm.continuousOn.comp hιc.continuousOn (mapsTo_preimage _ _)) fun z hz => ?_
    simp only [mem_preimage] at hz
    simp [Function.comp_apply, dite_eq_left hz]

/-- The source of `subtypeCoord` is the part of the subtype in the ambient chart source. -/
@[simp]
theorem subtypeCoord_source (e : OpenPartialHomeomorph X Y) (s : Set X) (x₀ : s)
    (ι : Z → Y) (π : Y → Z)
    (hι : ∀ {z}, ι z ∈ e.target → e.symm (ι z) ∈ s)
    (hslice : ∀ {x}, x ∈ e.source → x ∈ s → ι (π (e x)) = e x)
    (hπι : Function.LeftInverse π ι) (hιc : Continuous ι) (hπc : Continuous π) :
    (e.subtypeCoord s x₀ ι π hι hslice hπι hιc hπc).source =
      Subtype.val ⁻¹' e.source :=
  (rfl)

/-- The target of `subtypeCoord` is the preimage of the ambient target under the slice
parametrization. -/
@[simp]
theorem subtypeCoord_target (e : OpenPartialHomeomorph X Y) (s : Set X) (x₀ : s)
    (ι : Z → Y) (π : Y → Z)
    (hι : ∀ {z}, ι z ∈ e.target → e.symm (ι z) ∈ s)
    (hslice : ∀ {x}, x ∈ e.source → x ∈ s → ι (π (e x)) = e x)
    (hπι : Function.LeftInverse π ι) (hιc : Continuous ι) (hπc : Continuous π) :
    (e.subtypeCoord s x₀ ι π hι hslice hπι hιc hπc).target = ι ⁻¹' e.target :=
  (rfl)

/-- `subtypeCoord` reads a subtype point using the ambient chart followed by the coordinate
retraction. -/
@[simp]
theorem subtypeCoord_apply (e : OpenPartialHomeomorph X Y) (s : Set X) (x₀ : s)
    (ι : Z → Y) (π : Y → Z)
    (hι : ∀ {z}, ι z ∈ e.target → e.symm (ι z) ∈ s)
    (hslice : ∀ {x}, x ∈ e.source → x ∈ s → ι (π (e x)) = e x)
    (hπι : Function.LeftInverse π ι) (hιc : Continuous ι) (hπc : Continuous π) (x : s) :
    e.subtypeCoord s x₀ ι π hι hslice hπι hιc hπc x = π (e x.1) :=
  (rfl)

/-- On its target, the inverse of `subtypeCoord` is the ambient inverse evaluated on the
parametrized slice. -/
@[simp]
theorem coe_subtypeCoord_symm_apply (e : OpenPartialHomeomorph X Y) (s : Set X) (x₀ : s)
    (ι : Z → Y) (π : Y → Z)
    (hι : ∀ {z}, ι z ∈ e.target → e.symm (ι z) ∈ s)
    (hslice : ∀ {x}, x ∈ e.source → x ∈ s → ι (π (e x)) = e x)
    (hπι : Function.LeftInverse π ι) (hιc : Continuous ι) (hπc : Continuous π)
    {z : Z} (hz : ι z ∈ e.target) :
    ((e.subtypeCoord s x₀ ι π hι hslice hπι hιc hπc).symm z : X) = e.symm (ι z) := by
  let x : s := ⟨e.symm (ι z), hι hz⟩
  have hx : x ∈ (e.subtypeCoord s x₀ ι π hι hslice hπι hιc hπc).source := by
    rw [subtypeCoord_source]
    exact e.map_target hz
  have htarget : z ∈ (e.subtypeCoord s x₀ ι π hι hslice hπι hιc hπc).target := by
    rw [subtypeCoord_target]
    exact hz
  have heq : x = (e.subtypeCoord s x₀ ι π hι hslice hπι hιc hπc).symm z := by
    rw [(e.subtypeCoord s x₀ ι π hι hslice hπι hιc hπc).eq_symm_apply hx htarget,
      subtypeCoord_apply]
    change π (e (e.symm (ι z))) = z
    rw [e.right_inv hz]
    exact hπι z
  exact (congrArg Subtype.val heq).symm

end OpenPartialHomeomorph
