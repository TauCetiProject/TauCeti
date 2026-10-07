/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Constructions for open partial homeomorphisms

An open partial homeomorphism restricts to a chart on a subtype when membership in the subtype is
detected by a parametrized coordinate slice. This file packages that topological construction;
zero-slice subgroup charts use it after translating an ambient chart. Continuous maps that are
inverse on open sets also give an open partial homeomorphism on their mutual restrictions
(`ContinuousOn.toOpenPartialHomeomorph`).

## Main definitions

* `ContinuousOn.toOpenPartialHomeomorph` constructs an open partial homeomorphism from continuous
  maps inverse on their mutual restrictions.

* `OpenPartialHomeomorph.subtypeCoord` restricts an open partial homeomorphism to a subtype and
  reads its coordinates through a retraction onto the parametrized slice.

## References

This construction abstracts the concrete subtype charts in the following Tau Ceti formalizations:

* `boundaryChart` in `TauCeti/Geometry/Manifold/Boundary/Charts.lean`.
* `TauCeti.levelSetChart` in `TauCeti/Analysis/Fredholm/LevelSet/Basic.lean`.
-/

public section

open Set Topology

namespace OpenPartialHomeomorph

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

open scoped Classical in
/-- Restrict an open partial homeomorphism to a subtype represented by a parametrized coordinate
slice.

The map `ι : Z → Y` parametrizes the slice and `π : Y → Z` reads its coordinates. The hypotheses
say that ambient inverse images of slice points belong to `s`, that points of `s` visible in the
source lie on the slice, and that `π` is a left inverse of `ι` wherever the slice meets the target.
Only continuity of `π` where the parametrized slice meets the target is needed. Outside the target,
the inverse uses the canonical choice supplied by `Nonempty s`; its value there is irrelevant to an
open partial homeomorphism. -/
noncomputable def subtypeCoord (e : OpenPartialHomeomorph X Y) (s : Set X) (hs : Nonempty s)
    (ι : Z → Y) (π : Y → Z)
    (hι : ∀ {z}, ι z ∈ e.target → e.symm (ι z) ∈ s)
    (hslice : ∀ {x}, x ∈ e.source → x ∈ s → ι (π (e x)) = e x)
    (hπι : Set.LeftInvOn π ι (ι ⁻¹' e.target)) (hιc : Continuous ι)
    (hπc : ContinuousOn π (e.target ∩ Set.range ι)) : OpenPartialHomeomorph s Z where
  toFun x := π (e x.1)
  invFun z := if h : ι z ∈ e.target then ⟨e.symm (ι z), hι h⟩ else Classical.choice hs
  source := Subtype.val ⁻¹' e.source
  target := ι ⁻¹' e.target
  map_source' x hx := by
    -- These fields are being defined, so their public equations are not available yet.
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
    -- Reduce equality in the subtype after selecting the on-target inverse branch.
    change e.symm (ι (π (e x.1))) = x.1
    rw [hslice hx x.2, e.left_inv hx]
  right_inv' z hz := by
    simp only [mem_preimage] at hz
    rw [dite_eq_left hz, e.right_inv hz]
    exact hπι hz
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage hιc
  continuousOn_toFun :=
    hπc.comp
      (e.continuousOn.comp continuous_subtype_val.continuousOn (mapsTo_preimage _ _))
      (fun x hx => ⟨e.map_source hx, ⟨π (e x.1), hslice hx x.2⟩⟩)
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr
      (e.symm.continuousOn.comp hιc.continuousOn (mapsTo_preimage _ _)) fun z hz => ?_
    simp only [mem_preimage] at hz
    simp [Function.comp_apply, hz]

/-- The source of `subtypeCoord` is the part of the subtype in the ambient source. -/
@[simp]
theorem subtypeCoord_source (e : OpenPartialHomeomorph X Y) (s : Set X) (hs : Nonempty s)
    (ι : Z → Y) (π : Y → Z)
    (hι : ∀ {z}, ι z ∈ e.target → e.symm (ι z) ∈ s)
    (hslice : ∀ {x}, x ∈ e.source → x ∈ s → ι (π (e x)) = e x)
    (hπι : Set.LeftInvOn π ι (ι ⁻¹' e.target)) (hιc : Continuous ι)
    (hπc : ContinuousOn π (e.target ∩ Set.range ι)) :
    (e.subtypeCoord s hs ι π hι hslice hπι hιc hπc).source = Subtype.val ⁻¹' e.source := by
  unfold subtypeCoord
  rfl

/-- The target of `subtypeCoord` is the preimage of the ambient target under the slice
parametrization. -/
@[simp]
theorem subtypeCoord_target (e : OpenPartialHomeomorph X Y) (s : Set X) (hs : Nonempty s)
    (ι : Z → Y) (π : Y → Z)
    (hι : ∀ {z}, ι z ∈ e.target → e.symm (ι z) ∈ s)
    (hslice : ∀ {x}, x ∈ e.source → x ∈ s → ι (π (e x)) = e x)
    (hπι : Set.LeftInvOn π ι (ι ⁻¹' e.target)) (hιc : Continuous ι)
    (hπc : ContinuousOn π (e.target ∩ Set.range ι)) :
    (e.subtypeCoord s hs ι π hι hslice hπι hιc hπc).target = ι ⁻¹' e.target := by
  unfold subtypeCoord
  rfl

/-- `subtypeCoord` reads a subtype point using the ambient map followed by the coordinate
retraction. -/
@[simp]
theorem subtypeCoord_apply (e : OpenPartialHomeomorph X Y) (s : Set X) (hs : Nonempty s)
    (ι : Z → Y) (π : Y → Z)
    (hι : ∀ {z}, ι z ∈ e.target → e.symm (ι z) ∈ s)
    (hslice : ∀ {x}, x ∈ e.source → x ∈ s → ι (π (e x)) = e x)
    (hπι : Set.LeftInvOn π ι (ι ⁻¹' e.target)) (hιc : Continuous ι)
    (hπc : ContinuousOn π (e.target ∩ Set.range ι)) (x : s) :
    e.subtypeCoord s hs ι π hι hslice hπι hιc hπc x = π (e x.1) := by
  unfold subtypeCoord
  rfl

/-- On its source, `subtypeCoord` recovers the ambient coordinate after applying the slice
parametrization. -/
theorem subtypeCoord_parametrization_apply (e : OpenPartialHomeomorph X Y) (s : Set X)
    (hs : Nonempty s) (ι : Z → Y) (π : Y → Z)
    (hι : ∀ {z}, ι z ∈ e.target → e.symm (ι z) ∈ s)
    (hslice : ∀ {x}, x ∈ e.source → x ∈ s → ι (π (e x)) = e x)
    (hπι : Set.LeftInvOn π ι (ι ⁻¹' e.target)) (hιc : Continuous ι)
    (hπc : ContinuousOn π (e.target ∩ Set.range ι)) {x : s}
    (hx : x ∈ (e.subtypeCoord s hs ι π hι hslice hπι hιc hπc).source) :
    ι (e.subtypeCoord s hs ι π hι hslice hπι hιc hπc x) = e x.1 := by
  rw [subtypeCoord_apply]
  exact hslice (by simpa only [subtypeCoord_source, Set.mem_preimage] using hx) x.2

/-- On its target, the inverse of `subtypeCoord` is the ambient inverse evaluated on the
parametrized slice. -/
@[simp]
theorem coe_subtypeCoord_symm_apply (e : OpenPartialHomeomorph X Y) (s : Set X)
    (hs : Nonempty s) (ι : Z → Y) (π : Y → Z)
    (hι : ∀ {z}, ι z ∈ e.target → e.symm (ι z) ∈ s)
    (hslice : ∀ {x}, x ∈ e.source → x ∈ s → ι (π (e x)) = e x)
    (hπι : Set.LeftInvOn π ι (ι ⁻¹' e.target)) (hιc : Continuous ι)
    (hπc : ContinuousOn π (e.target ∩ Set.range ι)) {z : Z} (hz : ι z ∈ e.target) :
    ((e.subtypeCoord s hs ι π hι hslice hπι hιc hπc).symm z : X) = e.symm (ι z) := by
  classical
  simp [subtypeCoord, hz]

end OpenPartialHomeomorph

namespace ContinuousOn

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}
    (hf : ContinuousOn f U) (hg : ContinuousOn g V) (hU : IsOpen U) (hV : IsOpen V)
    (hgf : LeftInvOn g f (U ∩ f ⁻¹' V)) (hfg : RightInvOn g f (V ∩ g ⁻¹' U))

/-- Continuous maps on open sets define an open partial homeomorphism if they are inverse on
points whose images lie in the other set. The forward and inverse maps are the given maps,
and the source and target are exactly these mutual restrictions. -/
def toOpenPartialHomeomorph : OpenPartialHomeomorph X Y where
  toFun := f
  invFun := g
  source := U ∩ f ⁻¹' V
  target := V ∩ g ⁻¹' U
  map_source' x hx := ⟨hx.2, by simpa only [mem_preimage, hgf hx] using hx.1⟩
  map_target' y hy := ⟨hy.2, by simpa only [mem_preimage, hfg hy] using hy.1⟩
  left_inv' _ hx := hgf hx
  right_inv' _ hy := hfg hy
  open_source := hf.isOpen_inter_preimage hU hV
  open_target := hg.isOpen_inter_preimage hV hU
  continuousOn_toFun := hf.mono inter_subset_left
  continuousOn_invFun := hg.mono inter_subset_left

/-- The forward map of `toOpenPartialHomeomorph` is the given map. -/
@[simp]
theorem coe_toOpenPartialHomeomorph :
    ⇑(hf.toOpenPartialHomeomorph hg hU hV hgf hfg) = f := (rfl)

/-- The inverse map of `toOpenPartialHomeomorph` is the given inverse. -/
@[simp]
theorem coe_toOpenPartialHomeomorph_symm :
    ⇑(hf.toOpenPartialHomeomorph hg hU hV hgf hfg).symm = g := (rfl)

/-- The source of `toOpenPartialHomeomorph` consists of points of `U` mapped into `V`. -/
@[simp]
theorem toOpenPartialHomeomorph_source :
    (hf.toOpenPartialHomeomorph hg hU hV hgf hfg).source = U ∩ f ⁻¹' V := (rfl)

/-- The target of `toOpenPartialHomeomorph` consists of points of `V` mapped into `U`. -/
@[simp]
theorem toOpenPartialHomeomorph_target :
    (hf.toOpenPartialHomeomorph hg hU hV hgf hfg).target = V ∩ g ⁻¹' U := (rfl)

end ContinuousOn
