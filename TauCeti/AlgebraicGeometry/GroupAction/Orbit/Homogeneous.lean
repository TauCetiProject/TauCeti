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

* `TauCeti.SchemeAction.orbitInclusionIso`: for a reduced homogeneous scheme `X`, the equivariant
  isomorphism `orbitOver G x ≅ X`.
* `TauCeti.SchemeAction.smooth_of_orbit_eq_univ`,
  `TauCeti.SchemeAction.flat_orbitMap_of_orbit_eq_univ`,
  `TauCeti.SchemeAction.smooth_orbitMap_iff_of_orbit_eq_univ`: smoothness and flatness consequences
  for homogeneous schemes and their orbit morphisms.

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

section CompactTarget

variable [CompactSpace X.left]

/-- When a single orbit covers `X`, the orbit immersion is a closed immersion. -/
theorem isClosedImmersion_orbitι_of_orbit_eq_univ (h : orbit G x = Set.univ) :
    IsClosedImmersion (orbitι G x) :=
  (isClosedImmersion_orbitι_iff G x).mpr (h ▸ isClosed_univ)

/-- When a single orbit covers `X`, the orbit immersion is surjective. -/
theorem surjective_orbitι_of_orbit_eq_univ (h : orbit G x = Set.univ) :
    Surjective (orbitι G x) :=
  ⟨Set.range_eq_univ.mp ((range_orbitι G x).trans h)⟩

/-- When a single orbit covers a reduced finite-type scheme `X`, the orbit immersion is an
isomorphism of schemes. -/
theorem isIso_orbitι_of_orbit_eq_univ [IsReduced X.left] (h : orbit G x = Set.univ) :
    IsIso (orbitι G x) := by
  have : IsClosedImmersion (orbitι G x) := isClosedImmersion_orbitι_of_orbit_eq_univ G x h
  have : Surjective (orbitι G x) := surjective_orbitι_of_orbit_eq_univ G x h
  exact isIso_of_isClosedImmersion_of_surjective (orbitι G x)

/-- When a single orbit covers a reduced finite-type scheme `X`, the orbit inclusion over `Spec k`
is an isomorphism. -/
theorem isIso_orbitInclusion_of_orbit_eq_univ [IsReduced X.left] (h : orbit G x = Set.univ) :
    IsIso (orbitInclusion G x) := by
  have : IsIso ((Over.forget _).map (orbitInclusion G x)) := by
    rw [Over.forget_map, orbitInclusion_left]
    exact isIso_orbitι_of_orbit_eq_univ G x h
  exact isIso_of_reflects_iso (orbitInclusion G x) (Over.forget _)

/-- The canonical equivariant isomorphism between the orbit scheme `orbitOver G x` and a reduced
homogeneous scheme `X`. -/
def orbitInclusionIso [IsReduced X.left] (h : orbit G x = Set.univ) :
    orbitOver G x ≅ X :=
  have : IsIso (orbitInclusion G x) := isIso_orbitInclusion_of_orbit_eq_univ G x h
  asIso (orbitInclusion G x)

/-- The forward direction of `orbitInclusionIso` is the orbit inclusion. -/
@[simp]
theorem orbitInclusionIso_hom [IsReduced X.left] (h : orbit G x = Set.univ) :
    (orbitInclusionIso G x h).hom = orbitInclusion G x := (rfl)

/-- Composing the orbit morphism with the inverse of `orbitInclusionIso` recovers the orbit
projection. -/
@[reassoc (attr := simp)]
theorem orbitMap_comp_orbitInclusionIso_inv [IsReduced X.left] (h : orbit G x = Set.univ) :
    orbitMap G x ≫ (orbitInclusionIso G x h).inv = orbitProjection G x := by
  rw [← orbitProjection_inclusion G x, ← orbitInclusionIso_hom G x h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- `orbitInclusionIso` is equivariant. -/
instance [IsReduced X.left] (h : orbit G x = Set.univ) :
    IsModHom G (orbitInclusionIso G x h).hom := by
  rw [orbitInclusionIso_hom]
  infer_instance

end CompactTarget

/-- Every reduced finite-type homogeneous scheme for a geometrically reduced finite-type group
over a field is smooth. -/
theorem smooth_of_orbit_eq_univ [GeometricallyReduced G.hom] [IsReduced X.left]
    (h : orbit G x = Set.univ) :
    Smooth X.hom := by
  have : CompactSpace X.left := Function.Surjective.compactSpace (orbitMap G x).left.continuous
    ((surjective_iff _).mp ((surjective_orbitMap_iff_orbit_eq_univ G x).mpr h))
  have hcomp : (orbitInclusionIso G x h).inv.left ≫ orbitToBase G x = X.hom :=
    Over.w (orbitInclusionIso G x h).inv
  rw [← hcomp]
  infer_instance

/-- The orbit morphism onto a reduced finite-type homogeneous scheme for a geometrically reduced
finite-type group over a field is flat. -/
theorem flat_orbitMap_of_orbit_eq_univ [GeometricallyReduced G.hom] [IsReduced X.left]
    (h : orbit G x = Set.univ) :
    Flat (orbitMap G x).left := by
  have : CompactSpace X.left := Function.Surjective.compactSpace (orbitMap G x).left.continuous
    ((surjective_iff _).mp ((surjective_orbitMap_iff_orbit_eq_univ G x).mpr h))
  have : IsIso (orbitι G x) := isIso_orbitι_of_orbit_eq_univ G x h
  rw [← toOrbit_ι G x]
  infer_instance

/-- For a geometrically reduced finite-type group acting transitively on a reduced finite-type
scheme `X` over a field, the orbit morphism `G ⟶ X` is smooth if and only if the scheme-theoretic
stabilizer `stabilizer G x` is smooth over `Spec k`. -/
theorem smooth_orbitMap_iff_of_orbit_eq_univ [GeometricallyReduced G.hom] [IsReduced X.left]
    (h : orbit G x = Set.univ) :
    Smooth (orbitMap G x).left ↔ Smooth (stabilizer G x).hom := by
  have : CompactSpace X.left := Function.Surjective.compactSpace (orbitMap G x).left.continuous
    ((surjective_iff _).mp ((surjective_orbitMap_iff_orbit_eq_univ G x).mpr h))
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
  have : CompactSpace X.left := Function.Surjective.compactSpace (orbitMap G x).left.continuous
    ((surjective_iff _).mp ((surjective_orbitMap_iff_orbit_eq_univ G x).mpr h))
  have : IsIso (orbitι G x) := isIso_orbitι_of_orbit_eq_univ G x h
  rw [← toOrbit_ι G x]
  infer_instance

end Homogeneous

end TauCeti.SchemeAction
