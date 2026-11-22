/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Stabilizer
import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Smooth

/-!
# Homogeneous schemes and orbit-scheme identification

When a finite-type algebraic group scheme `G` over a field `k` acts on a locally finite-type
quasi-compact reduced `k`-scheme `X` such that the orbit of a rational point `x : Spec k ⟶ X`
covers all of `X`, the canonical equivariant orbit immersion
`orbitInclusion G x : orbitOver G x ⟶ X` is a surjective closed immersion into a reduced scheme,
hence an equivariant isomorphism `orbitInclusionIso G x h : orbitOver G x ≅ X`. Transporting the
orbit-scheme theory along this isomorphism shows that for a geometrically reduced finite-type group
`G`:

* `X` itself is smooth over `Spec k`;
* the orbit morphism `orbitMap G x` is faithfully flat and locally of finite presentation;
* the orbit morphism `orbitMap G x` is smooth if and only if the scheme-theoretic stabilizer
  `stabilizer G x` is smooth over `Spec k` (and unconditionally so when `G` is affine in
  characteristic zero).

## Main declarations

* `TauCeti.SchemeAction.smooth_of_orbit_eq_univ`,
  `TauCeti.SchemeAction.flat_orbitMap_of_orbit_eq_univ`,
  `TauCeti.SchemeAction.smooth_orbitMap_iff_of_orbit_eq_univ`,
  `TauCeti.SchemeAction.smooth_orbitMap_of_orbit_eq_univ_of_charZero`: smoothness and flatness
  consequences for homogeneous schemes and their orbit morphisms.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.e, Propositions 7.11 and 7.15.
-/

public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Topology

namespace TauCeti.SchemeAction

universe u

section Homogeneous

variable {k : Type u} [Field k]
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

/-- Every reduced finite-type homogeneous scheme for a geometrically reduced finite-type group
over a field is smooth. -/
theorem smooth_of_orbit_eq_univ [GeometricallyReduced G.hom] [IsReduced X.left]
    (h : orbit G x = Set.univ) :
    Smooth X.hom := by
  have : CompactSpace X.left := compactSpace_of_orbit_eq_univ G x h
  have hcomp : (orbitInclusionIso G x h).inv.left ≫ orbitToBase G x = X.hom :=
    Over.w (orbitInclusionIso G x h).inv
  rw [← hcomp]
  infer_instance

/-- The orbit morphism onto a reduced finite-type homogeneous scheme for a geometrically reduced
finite-type group over a field is flat. -/
theorem flat_orbitMap_of_orbit_eq_univ [GeometricallyReduced G.hom] [IsReduced X.left]
    (h : orbit G x = Set.univ) :
    Flat (orbitMap G x).left := by
  have : CompactSpace X.left := compactSpace_of_orbit_eq_univ G x h
  have : IsIso (orbitι G x) := isIso_orbitι_of_orbit_eq_univ G x h
  rw [← toOrbit_ι G x]
  infer_instance

/-- For a geometrically reduced finite-type group acting transitively on a reduced finite-type
scheme `X` over a field, the orbit morphism `G ⟶ X` is smooth if and only if the scheme-theoretic
stabilizer `stabilizer G x` is smooth over `Spec k`. -/
theorem smooth_orbitMap_iff_of_orbit_eq_univ [GeometricallyReduced G.hom] [IsReduced X.left]
    (h : orbit G x = Set.univ) :
    Smooth (orbitMap G x).left ↔ Smooth (stabilizer G x).hom := by
  have : CompactSpace X.left := compactSpace_of_orbit_eq_univ G x h
  have : IsIso (orbitι G x) := isIso_orbitι_of_orbit_eq_univ G x h
  let : MorphismProperty.RespectsIso @Smooth :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← toOrbit_ι G x, MorphismProperty.cancel_right_of_respectsIso @Smooth]
  exact smooth_toOrbit_iff G x

/-- In characteristic zero, the orbit morphism from an affine finite-type group onto a reduced
finite-type homogeneous scheme over a field is smooth. -/
theorem smooth_orbitMap_of_orbit_eq_univ_of_charZero [CharZero k] [IsAffine G.left]
    [IsReduced X.left] (h : orbit G x = Set.univ) :
    Smooth (orbitMap G x).left := by
  have : CompactSpace X.left := compactSpace_of_orbit_eq_univ G x h
  have : IsIso (orbitι G x) := isIso_orbitι_of_orbit_eq_univ G x h
  rw [← toOrbit_ι G x]
  infer_instance

end Homogeneous

end TauCeti.SchemeAction
