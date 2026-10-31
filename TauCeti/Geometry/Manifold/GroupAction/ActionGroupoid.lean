/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.CategoryTheory.ActionGroupoid

/-!
# The smooth structure of an action groupoid

Let a discrete group `G` act on a manifold `X` by `C^n` maps. This file makes Mathlib's native
action category `CategoryTheory.ActionCategory G X` into an étale `C^n` groupoid: its objects and
its total arrows are `C^n` manifolds modelled on the model of `X`, the source and target maps are
`C^n` local diffeomorphisms, and units, inversion and composition are `C^n`. The charts, the
source, units and composition only need a discrete monoid; the target and inversion use the group
structure.

The object charts are those of `X`, transported along `ActionCategory.objEquiv`, so the objects are
diffeomorphic to `X` (`TauCeti.ActionGroupoid.objectDiffeomorph`) without being identified with `X`
definitionally. The arrow charts are pulled back from the objects along the source map, which is a
local homeomorphism because each fixed-label slice of arrows is open. With these charts the source
is a `C^n` local diffeomorphism by construction, and a map into the arrows is `C^n` exactly when it
is continuous and its source is `C^n` (`TauCeti.ActionGroupoid.contMDiff_arrows_iff`). Every label
is retained: arrows with distinct labels lie in distinct slices even when the labels act
identically on `X`, as for the ineffective isotropy of an orbifold chart `[U/G]`.

Composition is stated for smooth families of composable arrows: if `a` and `b` are `C^n` maps from
a manifold into the arrows with the target of `a z` equal to the source of `b z`, then the composite
arrows depend `C^n` on `z`. No manifold structure is put on the space of composable pairs here.

This is the smooth model of the finite quotient charts `[U/G]` of an orbifold. For a proper
action, `TauCeti.ActionGroupoid.isProperMap_source_target_iff` makes it a proper étale groupoid.

## Main definitions

* `TauCeti.ActionGroupoid.instChartedSpaceObjects`, `TauCeti.ActionGroupoid.instChartedSpaceArrows`:
  the object and arrow charts.
* `TauCeti.ActionGroupoid.objectDiffeomorph`: the objects are diffeomorphic to `X`.
* `TauCeti.ActionGroupoid.inverseDiffeomorph`: inversion of arrows is a diffeomorphism.

## Main results

* `TauCeti.ActionGroupoid.contMDiff_objects_iff`, `TauCeti.ActionGroupoid.contMDiff_arrows_iff`:
  the `C^n` maps into the objects and into the arrows.
* `TauCeti.ActionGroupoid.isLocalDiffeomorph_source` and
  `TauCeti.ActionGroupoid.isLocalDiffeomorph_target`: source and target are `C^n` local
  diffeomorphisms.
* `TauCeti.ActionGroupoid.contMDiff_sourceChart_symm`: each label gives a `C^n` section of the
  source map.
* `TauCeti.ActionGroupoid.contMDiff_unit`, `TauCeti.ActionGroupoid.contMDiff_inverse` and
  `TauCeti.ActionGroupoid.contMDiff_comp`: units, inversion and composition are `C^n`.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and stringy topology*, Chapter 1.
-/

public noncomputable section

open CategoryTheory Topology
open CategoryTheory.ActionCategory
open scoped Manifold ContDiff

namespace TauCeti.ActionGroupoid

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  (G X : Type*)

section Monoid

variable [Monoid G] [MulAction G X] [TopologicalSpace X] [ChartedSpace H X]

/-- The object charts of the native action category, transported from `X` along the object
homeomorphism. -/
instance instChartedSpaceObjects : ChartedSpace H (ActionCategory G X) :=
  (objectHomeomorph G X).pullbackChartedSpace

/-- The objects of the action category of a `C^n` manifold form a `C^n` manifold. -/
instance instIsManifoldObjects [IsManifold I n X] : IsManifold I n (ActionCategory G X) :=
  Homeomorph.pullback_isManifold I n (objectHomeomorph G X)

/-- The objects of the native action category are diffeomorphic to the acted-on manifold. -/
def objectDiffeomorph : ActionCategory G X ≃ₘ^n⟮I, I⟯ X :=
  (objectHomeomorph G X).pullbackDiffeomorph I n

/-- The object diffeomorphism reads the point underlying a native action-category object. -/
@[simp]
theorem objectDiffeomorph_apply (x : ActionCategory G X) :
    objectDiffeomorph I n G X x = x.back := by
  simp [objectDiffeomorph]

/-- The inverse object diffeomorphism is the native object equivalence. -/
@[simp]
theorem objectDiffeomorph_symm_apply (x : X) :
    (objectDiffeomorph I n G X).symm x = objEquiv G X x := by
  simp [objectDiffeomorph]

variable {G X} in
/-- A map into the objects of the action category is `C^n` exactly when the underlying points
depend `C^n` on the parameter. -/
theorem contMDiff_objects_iff {f : N → ActionCategory G X} :
    ContMDiff I' I n f ↔ ContMDiff I' I n fun z ↦ (f z).back := by
  simp [← (objectDiffeomorph I n G X).contMDiff_diffeomorph_comp_iff le_rfl, Function.comp_def]

variable [TopologicalSpace G] [DiscreteTopology G]

/-- The arrow charts of the native action category of a discrete monoid, pulled back from the
objects along the source map. -/
instance instChartedSpaceArrows : ChartedSpace H (Quiver.Total (ActionCategory G X)) :=
  (isLocalHomeomorph_source G X).chartedSpaceComap

/-- The arrows of the action category of a discrete monoid acting on a `C^n` manifold form a `C^n`
manifold. -/
instance instIsManifoldArrows [IsManifold I n X] :
    IsManifold I n (Quiver.Total (ActionCategory G X)) :=
  (isLocalHomeomorph_source G X).isManifold_chartedSpaceComap

/-- The source map of the action groupoid of a discrete monoid is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_source :
    IsLocalDiffeomorph I I n
      (Quiver.Total.left : Quiver.Total (ActionCategory G X) → ActionCategory G X) :=
  (isLocalHomeomorph_source G X).isLocalDiffeomorph_chartedSpaceComap

variable {G X} in
/-- A map into the arrows of the action category of a discrete monoid is `C^n` exactly when it is
continuous and the sources of its arrows depend `C^n` on the parameter. -/
theorem contMDiff_arrows_iff {f : N → Quiver.Total (ActionCategory G X)} :
    ContMDiff I' I n f ↔ Continuous f ∧ ContMDiff I' I n fun z ↦ (f z).left :=
  (isLocalHomeomorph_source G X).contMDiff_chartedSpaceComap_iff

/-- The inverse of the fixed-label source chart, sending an object to the arrow with that source
and the given label, is `C^n`. So every label gives a global `C^n` section of the source map. -/
theorem contMDiff_sourceChart_symm (g : G) : ContMDiff I I n (sourceChart G X g).symm := by
  refine (contMDiff_arrows_iff I n).2 ⟨?_, ?_⟩
  · exact continuousOn_univ.1 (sourceChart_target G X g ▸ (sourceChart G X g).continuousOn_symm)
  · exact contMDiff_id.congr fun x ↦ by
      simpa only [sourceChart_apply, id] using
        (sourceChart G X g).right_inv (sourceChart_target G X g ▸ Set.mem_univ x)

/-- The unit map of the action groupoid of a discrete monoid is `C^n`. -/
theorem contMDiff_unit :
    ContMDiff I I n fun x : ActionCategory G X ↦
      (⟨x, x, 𝟙 x⟩ : Quiver.Total (ActionCategory G X)) :=
  (contMDiff_arrows_iff I n).2 ⟨continuous_unit G X, contMDiff_id⟩

/-- The target map of the action groupoid of a discrete monoid acting by `C^n` maps is `C^n`. -/
theorem contMDiff_target [ContMDiffConstSMul I n G X] :
    ContMDiff I I n
      (Quiver.Total.right : Quiver.Total (ActionCategory G X) → ActionCategory G X) := by
  rw [contMDiff_objects_iff]
  intro f
  -- Near `f` every arrow has the label of `f`, so there the target is the translate of the source
  -- by that fixed label.
  have hlabel : ∀ᶠ a in 𝓝 f, a.hom.hom = f.hom.hom :=
    ((isOpen_discrete {f.hom.hom}).preimage (continuous_label G X)).mem_nhds rfl
  have hsmooth : ContMDiff I I n fun a : Quiver.Total (ActionCategory G X) ↦
      f.hom.hom • a.left.back := by
    simpa [Function.comp_def] using (contMDiff_const_smul f.hom.hom).comp
      ((objectDiffeomorph I n G X).contMDiff.comp (isLocalDiffeomorph_source I n G X).contMDiff)
  refine (hsmooth f).congr_of_eventuallyEq ?_
  filter_upwards [hlabel] with a ha
  rw [← ha]
  exact a.hom.map_val.symm

variable {G X} in
/-- Composition in the action groupoid of a discrete monoid is `C^n`: composing two `C^n` families
of composable arrows gives a `C^n` family. The first arrow is followed by the second. -/
theorem contMDiff_comp {a b : N → Quiver.Total (ActionCategory G X)} (ha : ContMDiff I' I n a)
    (hb : ContMDiff I' I n b) (h : ∀ z, (a z).right = (b z).left) :
    ContMDiff I' I n fun z ↦
      (⟨(a z).left, (b z).right, (a z).hom ≫ eqToHom (h z) ≫ (b z).hom⟩ :
        Quiver.Total (ActionCategory G X)) := by
  have hsource : ContMDiff I' I n fun z ↦ (a z).left :=
    (isLocalDiffeomorph_source I n G X).contMDiff.comp ha
  exact (contMDiff_arrows_iff I n).2 ⟨(continuous_comp G X).comp
    ((ha.continuous.prodMk hb.continuous).subtype_mk h), hsource⟩

end Monoid

section Group

variable [Group G] [MulAction G X] [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace G] [DiscreteTopology G] [ContMDiffConstSMul I n G X]

/-- Inversion in the action groupoid of a discrete group acting by `C^n` maps is `C^n`. -/
theorem contMDiff_inverse :
    ContMDiff I I n fun f : Quiver.Total (ActionCategory G X) ↦
      (⟨f.right, f.left, inv f.hom⟩ : Quiver.Total (ActionCategory G X)) := by
  -- A discrete group acting by continuous maps acts continuously.
  have := ContMDiffConstSMul.continuousConstSMul (I := I) n (Γ := G) (M := X)
  have : ContinuousSMul G X := ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩
  exact (contMDiff_arrows_iff I n).2 ⟨continuous_inverse G X, contMDiff_target I n G X⟩

/-- Inversion of arrows, as a `C^n` diffeomorphism of the arrow manifold of the action groupoid of
a discrete group acting by `C^n` maps. -/
def inverseDiffeomorph :
    Quiver.Total (ActionCategory G X) ≃ₘ^n⟮I, I⟯ Quiver.Total (ActionCategory G X) where
  toFun f := ⟨f.right, f.left, inv f.hom⟩
  invFun f := ⟨f.right, f.left, inv f.hom⟩
  left_inv f := by simp
  right_inv f := by simp
  contMDiff_toFun := contMDiff_inverse I n G X
  contMDiff_invFun := contMDiff_inverse I n G X

/-- The inversion diffeomorphism reverses an arrow. -/
@[simp]
theorem inverseDiffeomorph_apply (f : Quiver.Total (ActionCategory G X)) :
    inverseDiffeomorph I n G X f = ⟨f.right, f.left, inv f.hom⟩ := (rfl)

/-- The inversion diffeomorphism is its own inverse. -/
@[simp]
theorem inverseDiffeomorph_symm :
    (inverseDiffeomorph I n G X).symm = inverseDiffeomorph I n G X := (rfl)

/-- The target map of the action groupoid of a discrete group acting by `C^n` maps is a `C^n` local
diffeomorphism. -/
theorem isLocalDiffeomorph_target :
    IsLocalDiffeomorph I I n
      (Quiver.Total.right : Quiver.Total (ActionCategory G X) → ActionCategory G X) :=
  -- The target is the source of the inverse arrow.
  isLocalDiffeomorph_iff.2 fun f ↦
    (isLocalDiffeomorph_iff.1 (inverseDiffeomorph I n G X).isLocalDiffeomorph f).comp I
      (ActionCategory G X) (isLocalDiffeomorph_iff.1 (isLocalDiffeomorph_source I n G X) _)

end Group

end TauCeti.ActionGroupoid
