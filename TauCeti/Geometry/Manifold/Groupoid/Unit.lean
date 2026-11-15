/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples

/-!
# The smooth structure of the unit groupoid

For a `C^n` manifold `X`, the native discrete category `Discrete X` carries a `C^n` étale groupoid
structure whose objects and total arrows are both `C^n`-diffeomorphic to `X`. As in
`TauCeti.UnitGroupoid`, `Discrete X` means categorical discreteness (only identity arrows), while
retaining the manifold topology and smooth charts of `X`.

Object charts are pulled back along `TauCeti.UnitGroupoid.objectHomeomorph`, and arrow charts are
pulled back from objects along the source map via `IsLocalHomeomorph.chartedSpaceComap`, matching
`TauCeti.ActionGroupoid`. Consequently source and target are `C^n` local diffeomorphisms, and
units, inversion and smooth families of composable arrows are `C^n`.

## Main definitions

* `TauCeti.UnitGroupoid.instChartedSpaceObjects`, `TauCeti.UnitGroupoid.instChartedSpaceArrows`:
  the `C^n` charts on `Discrete X` and `Quiver.Total (Discrete X)`.
* `TauCeti.UnitGroupoid.objectDiffeomorph`, `TauCeti.UnitGroupoid.arrowDiffeomorph`: `C^n`
  diffeomorphisms of objects and total arrows with `X`.

## Main results

* `TauCeti.UnitGroupoid.contMDiff_objects_iff`, `TauCeti.UnitGroupoid.contMDiff_arrows_iff`:
  characterisations of `C^n` maps into objects and total arrows.
* `TauCeti.UnitGroupoid.isLocalDiffeomorph_source`,
  `TauCeti.UnitGroupoid.isLocalDiffeomorph_target`: source and target are `C^n` local
  diffeomorphisms.
* `TauCeti.UnitGroupoid.contMDiff_unit`, `TauCeti.UnitGroupoid.contMDiff_inverse`,
  `TauCeti.UnitGroupoid.contMDiff_comp`: units, inversion and composition are `C^n`.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
-/

public noncomputable section

open CategoryTheory Topology
open scoped Manifold ContDiff

namespace TauCeti.UnitGroupoid

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  (X : Type*) [TopologicalSpace X] [ChartedSpace H X]

/-- Object charts of the unit groupoid, pulled back from `X` along `objectHomeomorph`. -/
instance instChartedSpaceObjects : ChartedSpace H (Discrete X) :=
  (objectHomeomorph X).pullbackChartedSpace

/-- Objects of the unit groupoid on a `C^n` manifold form a `C^n` manifold. -/
instance instIsManifoldObjects [IsManifold I n X] : IsManifold I n (Discrete X) :=
  Homeomorph.pullback_isManifold I n (objectHomeomorph X)

/-- Forgetting the categorical wrapper is a `C^n` diffeomorphism on objects. -/
def objectDiffeomorph : Discrete X ≃ₘ^n⟮I, I⟯ X :=
  (objectHomeomorph X).pullbackDiffeomorph I n

@[simp]
theorem objectDiffeomorph_apply (x : Discrete X) :
    objectDiffeomorph I n X x = x.as := by
  simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_symm_apply (x : X) :
    (objectDiffeomorph I n X).symm x = Discrete.mk x := by
  simp [objectDiffeomorph]

variable {X} in
/-- A map into `Discrete X` is `C^n` if and only if its underlying map into `X` is `C^n`. -/
theorem contMDiff_objects_iff {f : N → Discrete X} :
    ContMDiff I' I n f ↔ ContMDiff I' I n fun z ↦ (f z).as := by
  simp [← (objectDiffeomorph I n X).contMDiff_diffeomorph_comp_iff le_rfl, Function.comp_def]

/-- Arrow charts of the unit groupoid, pulled back from objects along the source map. -/
instance instChartedSpaceArrows : ChartedSpace H (Quiver.Total (Discrete X)) :=
  (isLocalHomeomorph_source X).chartedSpaceComap

/-- Total arrows of the unit groupoid on a `C^n` manifold form a `C^n` manifold. -/
instance instIsManifoldArrows [IsManifold I n X] : IsManifold I n (Quiver.Total (Discrete X)) :=
  (isLocalHomeomorph_source X).isManifold_chartedSpaceComap

/-- The source map of the unit groupoid is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_source :
    IsLocalDiffeomorph I I n (Quiver.Total.left : Quiver.Total (Discrete X) → Discrete X) :=
  (isLocalHomeomorph_source X).isLocalDiffeomorph_chartedSpaceComap

variable {X} in
/-- A map into `Quiver.Total (Discrete X)` is `C^n` if and only if it is continuous and its
sources depend `C^n` on the parameter. -/
theorem contMDiff_arrows_iff {f : N → Quiver.Total (Discrete X)} :
    ContMDiff I' I n f ↔ Continuous f ∧ ContMDiff I' I n fun z ↦ (f z).left :=
  (isLocalHomeomorph_source X).contMDiff_chartedSpaceComap_iff

/-- The unit map of the unit groupoid is `C^n`. -/
theorem contMDiff_unit :
    ContMDiff I I n fun x : Discrete X ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total (Discrete X)) :=
  (contMDiff_arrows_iff I n).mpr ⟨IsTopologicalGroupoid.continuous_unit, contMDiff_id⟩

/-- Total arrows of the unit groupoid are `C^n`-diffeomorphic to `X`. -/
def arrowDiffeomorph : Quiver.Total (Discrete X) ≃ₘ^n⟮I, I⟯ X :=
  { (arrowHomeomorph X).toEquiv with
    contMDiff_toFun := by
      convert (objectDiffeomorph I n X).contMDiff.comp (isLocalDiffeomorph_source I n X).contMDiff
        using 1
      funext a
      simp
    contMDiff_invFun := by
      convert (contMDiff_unit I n X).comp (objectDiffeomorph I n X).symm.contMDiff using 1
      funext x
      exact (arrowHomeomorph_symm_apply X x).trans
        (congrArg (fun y : Discrete X ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total (Discrete X)))
          (objectDiffeomorph_symm_apply I n X x).symm) }

@[simp]
theorem arrowDiffeomorph_apply (a : Quiver.Total (Discrete X)) :
    arrowDiffeomorph I n X a = a.left.as :=
  arrowHomeomorph_apply X a

@[simp]
theorem arrowDiffeomorph_symm_apply (x : X) :
    (arrowDiffeomorph I n X).symm x = ⟨⟨x⟩, ⟨x⟩, 𝟙 _⟩ :=
  arrowHomeomorph_symm_apply X x

/-- The target map of the unit groupoid is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_target :
    IsLocalDiffeomorph I I n (Quiver.Total.right : Quiver.Total (Discrete X) → Discrete X) := by
  convert isLocalDiffeomorph_source I n X using 1
  funext a
  exact (Discrete.ext (Discrete.eq_of_hom a.hom)).symm

/-- Inversion of arrows in the unit groupoid is `C^n`. -/
theorem contMDiff_inverse :
    ContMDiff I I n fun a : Quiver.Total (Discrete X) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Discrete X)) := by
  refine (contMDiff_arrows_iff I n).mpr ⟨IsTopologicalGroupoid.continuous_inverse, ?_⟩
  exact (isLocalDiffeomorph_target I n X).contMDiff

variable {X} in
/-- Smooth families of composable arrows in the unit groupoid compose to a `C^n` family. -/
theorem contMDiff_comp {a b : N → Quiver.Total (Discrete X)} (ha : ContMDiff I' I n a)
    (hb : ContMDiff I' I n b) (h : ∀ z, (a z).right = (b z).left) :
    ContMDiff I' I n fun z ↦ (a z).comp (b z) (h z) := by
  have hsource : ContMDiff I' I n fun z ↦ ((a z).comp (b z) (h z)).left := by
    simpa only [Quiver.Total.comp_left, Function.comp_def] using
      (isLocalDiffeomorph_source I n X).contMDiff.comp ha
  exact (contMDiff_arrows_iff I n).mpr
    ⟨IsTopologicalGroupoid.continuous_comp.comp ((ha.continuous.prodMk hb.continuous).subtype_mk h),
      hsource⟩

end TauCeti.UnitGroupoid
