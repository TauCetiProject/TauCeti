/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.Geometrically.Reduced
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Scheme
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Translation
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.GroupAction.Orbit.BaseChange
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Descent
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus.Basic

/-!
# Smooth orbit schemes

For a geometrically reduced finite-type group scheme acting on a finite-type scheme over any
field `k` (in particular, for any smooth group over `k` or any reduced group over a perfect
field), every locally closed orbit has a smooth scheme model. The model is the locally closed
scheme image of the actual orbit morphism. The ambient scheme need not be reduced, irreducible or
separated, and the group need not be connected.

Over an algebraically closed field, reducedness descends from the group to the orbit image, and
the dense smooth locus of the orbit scheme spreads to the whole model by translations
(`AlgebraicGeometry.Scheme.Hom.smooth_of_transitive_on_closedPoints`, adapting the proof
underlying Mathlib's `AlgebraicGeometry.smooth_of_grpObj`, by Andrew Yang); for closed orbits the
entire scheme-theoretic image is smooth, and every orbit closure contains such a smooth closed
orbit. Over a general field `k`, extending scalars to `AlgebraicClosure k` identifies the orbit
scheme with the base change of `orbitScheme` (`isPullback_orbitToBase_baseChange`), and
smoothness descends along `Spec (AlgebraicClosure k) ⟶ Spec k`. The orbit morphism itself is not
asserted smooth: in positive characteristic its stabilizer can be nonreduced.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace TauCeti.SchemeAction

universe u

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [LocallyOfFiniteType X.hom]

/-- A reduced immersed scheme lying in one orbit is smooth when the ambient translations
lift to automorphisms of that scheme. -/
theorem smooth_of_equivariant_of_range_subset_orbit
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) {Y : Scheme.{u}} (i : Y ⟶ X.left)
    [IsImmersion i] [IsReduced Y] (hrange : Set.range i ⊆ orbit G x)
    (e : (𝟙_ (Over (Spec (.of k))) ⟶ G) → (Y ≅ Y))
    (he : ∀ g, (e g).hom ≫ i = i ≫ (translation X g).hom.left) :
    Smooth (i ≫ X.hom) := by
  apply Scheme.Hom.smooth_of_transitive_on_closedPoints
  intro y hy z hz
  obtain ⟨g, hg⟩ := exists_eq_of_equivariant_of_range_subset_orbit G x i hrange e he hy hz
  refine ⟨e g, ?_, hg⟩
  rw [← Category.assoc, he, Category.assoc, Over.w]

private theorem smooth_orbitToBase_of_isAlgClosed [CompactSpace G.left] [CompactSpace X.left]
    [IsReduced G.left] (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) : Smooth (orbitToBase G x) := by
  rw [orbitToBase_def]
  exact smooth_of_equivariant_of_range_subset_orbit G x (orbitι G x)
    (range_orbitι G x).le (orbitTranslation G x) (orbitTranslation_hom_ι G x)

/-- A closed orbit of a reduced finite-type group over an algebraically closed field
has a smooth scheme-theoretic image, even when the ambient scheme is nonreduced. -/
theorem smooth_orbitClosureToBase_of_isClosed [IsReduced G.left]
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) [QuasiCompact (orbitMap G x).left]
    (hc : IsClosed (orbit G x)) :
    Smooth (orbitClosureToBase G x) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsReduced (orbitClosureScheme G x) :=
    IsSchemeTheoreticallyDominant.isReduced (toOrbitClosure G x)
  rw [orbitClosureToBase_def]
  exact smooth_of_equivariant_of_range_subset_orbit G x (orbitClosureι G x)
    (range_orbitClosureι_of_isClosed G x hc).le (orbitClosureTranslation G x)
    (orbitClosureTranslation_hom_ι G x)

end AlgClosed

/-- Over any field, every orbit scheme of a geometrically reduced finite-type group is smooth. In
particular, this applies whenever the group is smooth over `k`, or reduced over a perfect field.
The stabilizer and orbit morphism need not be smooth. -/
instance smooth_orbitToBase {k : Type u} [Field k] (G : Over (Spec (.of k)))
    {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
    [LocallyOfFiniteType G.hom] [CompactSpace G.left]
    [LocallyOfFiniteType X.hom] [CompactSpace X.left] [GeometricallyReduced G.hom]
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) : Smooth (orbitToBase G x) := by
  let f := Spec.algebraMap k (AlgebraicClosure k)
  let := (Over.pullback f).modObjObj G X
  exact MorphismProperty.of_isPullback_of_surjective_of_flat_of_quasiCompact
    (isPullback_orbitToBase_baseChange f G x)
    (smooth_orbitToBase_of_isAlgClosed ((Over.pullback f).obj G) _)

/-- Every reduced finite-type homogeneous scheme for a geometrically reduced finite-type group
over a field is smooth. -/
theorem smooth_of_orbit_eq_univ {k : Type u} [Field k] (G : Over (Spec (.of k)))
    {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X] [LocallyOfFiniteType G.hom]
    [CompactSpace G.left] [LocallyOfFiniteType X.hom] (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    [GeometricallyReduced G.hom] [IsReduced X.left] (h : orbit G x = Set.univ) :
    Smooth X.hom := by
  have : CompactSpace X.left := compactSpace_of_orbit_eq_univ G x h
  have : IsIso (orbitι G x) := isIso_orbitι_of_orbit_eq_univ G x h
  have hcomp : inv (orbitι G x) ≫ orbitToBase G x = X.hom := by
    rw [orbitToBase_def, IsIso.inv_hom_id_assoc]
  rw [← hcomp]
  infer_instance

end TauCeti.SchemeAction
