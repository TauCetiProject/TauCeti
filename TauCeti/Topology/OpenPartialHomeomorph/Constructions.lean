/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Constructions for open partial homeomorphisms

An open partial homeomorphism restricts to a chart on a subtype when membership in the subtype is
detected by a parametrized coordinate slice. In a topological group, an ambient chart can also be
transported by left translation. This file packages both topological constructions; zero-slice
subgroup charts translate the ambient chart first and then restrict it to the zero-slice subtype.

## Main definitions

* `OpenPartialHomeomorph.subtypeCoord` restricts an open partial homeomorphism to a subtype and
  reads its coordinates through a retraction onto the parametrized slice.
* `OpenPartialHomeomorph.translatedChart` translates an ambient group chart by a group element.
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

section Translation

variable {G P : Type*} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
  [TopologicalSpace P]

/-- Translate an ambient chart by a group element `g`. -/
def translatedChart (φ : OpenPartialHomeomorph G P) (g : G) : OpenPartialHomeomorph G P :=
  (Homeomorph.smul g).symm.transOpenPartialHomeomorph φ

/-- A translated chart is composition with inverse left translation. -/
theorem translatedChart_def (φ : OpenPartialHomeomorph G P) (g : G) :
    φ.translatedChart g = (Homeomorph.smul g).symm.transOpenPartialHomeomorph φ := by
  rfl

/-- The source of a translated chart consists of the points moved into the source of the original
chart by multiplication by `g⁻¹`. -/
@[simp]
theorem translatedChart_source (φ : OpenPartialHomeomorph G P) (g : G) :
    (φ.translatedChart g).source = (fun y : G => g⁻¹ * y) ⁻¹' φ.source := by
  ext y
  simp [translatedChart, Homeomorph.smul_symm_apply, smul_eq_mul]

/-- Translation does not change the coordinate target of an ambient chart. -/
@[simp]
theorem translatedChart_target (φ : OpenPartialHomeomorph G P) (g : G) :
    (φ.translatedChart g).target = φ.target := by
  simp [translatedChart]

/-- Evaluating a chart translated by `g` first translates the argument by `g⁻¹`, then applies
the original chart. -/
@[simp]
theorem translatedChart_apply (φ : OpenPartialHomeomorph G P) (g y : G) :
    φ.translatedChart g y = φ (g⁻¹ * y) := by
  simp [translatedChart, Homeomorph.smul_symm_apply, smul_eq_mul]

/-- The inverse of a translated chart applies the original inverse and then translates by `g`. -/
@[simp]
theorem translatedChart_symm_apply (φ : OpenPartialHomeomorph G P) (g : G) (p : P) :
    (φ.translatedChart g).symm p = g * φ.symm p := by
  simp [translatedChart, smul_eq_mul]

/-- A chart containing `1` in its source, translated by `g`, contains `g` in its source. -/
theorem mem_translatedChart_source (φ : OpenPartialHomeomorph G P)
    (h1 : (1 : G) ∈ φ.source) (g : G) : g ∈ (φ.translatedChart g).source := by
  rw [translatedChart_source]
  simpa using h1

end Translation

end OpenPartialHomeomorph
