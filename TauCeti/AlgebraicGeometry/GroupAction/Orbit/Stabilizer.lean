/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Action
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Flat
public import TauCeti.AlgebraicGeometry.GroupAction.Stabilizer
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Stabilizer.KernelPair
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Descent
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-!
# Smooth orbit maps and scheme-theoretic stabilizers

For a geometrically reduced finite-type group scheme over any field, the projection onto an orbit
scheme is smooth exactly when its scheme-theoretic stabilizer is smooth. Over any field of
characteristic zero, an affine acting group is smooth and has smooth stabilizers by Cartier's
theorem, so its orbit projections are smooth. The target here is the locally closed orbit scheme,
rather than the possibly larger ambient scheme.

The actual relation over the orbit is `G × Stab(x) ≅ G ×_O G`, with maps
`(g,h) ↦ g` and `(g,h) ↦ gh`. It is obtained from `stabilizer.isPullback_rightMul` by
cancelling the orbit immersion. The projection from this product is smooth when the
stabilizer is; smoothness descends along the faithfully flat orbit projection. Conversely,
the stabilizer is the fibre over the base point. All these squares are scheme-theoretic,
so the criterion retains infinitesimal stabilizers in positive characteristic.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

namespace TauCeti.SchemeAction

universe u

section GeneralBase

variable {S : Scheme.{u}} (G : Over S) {X : Over S} [GrpObj G] [ModObj G X]
  (x : 𝟙_ (Over S) ⟶ X)

/-- Smoothness of the orbit morphism implies smoothness of its scheme-theoretic stabilizer, over an
arbitrary base scheme and in every characteristic. -/
theorem smooth_stabilizer_of_smooth_orbitMap (h : Smooth (orbitMap G x).left) :
    Smooth (stabilizer G x).hom := by
  have hpb : IsPullback (stabilizer.incl G x).left (stabilizer G x).hom
      (orbitMap G x).left x.left := by
    simpa only [Over.forget_map, Over.toUnit_left] using
      (orbitFiber.isPullback G x x).map (Over.forget S)
  exact MorphismProperty.of_isPullback hpb h

/-- Over an arbitrary base scheme, a faithfully flat and quasi-compact orbit morphism is smooth if
and only if its scheme-theoretic stabilizer is smooth over the base scheme. -/
theorem smooth_orbitMap_iff [Flat (orbitMap G x).left] [Surjective (orbitMap G x).left]
    [QuasiCompact (orbitMap G x).left] :
    Smooth (orbitMap G x).left ↔ Smooth (stabilizer G x).hom := by
  refine ⟨smooth_stabilizer_of_smooth_orbitMap G x, fun hs ↦ ?_⟩
  let := hs
  have hp : Smooth (fst G (stabilizer G x)).left := by
    rw [Over.fst_left]
    infer_instance
  have hpb : IsPullback (fst G (stabilizer G x)).left (stabilizer.rightMul G x).left
      (orbitMap G x).left (orbitMap G x).left := by
    simpa only [Over.forget_map] using
      (stabilizer.isPullback_rightMul G x).map (Over.forget S)
  exact MorphismProperty.of_isPullback_of_surjective_of_flat_of_quasiCompact hpb hp

end GeneralBase

section Orbit

variable {k : Type u} [Field k]
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]
  (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

/-- The kernel pair of the orbit projection is right multiplication by the
scheme-theoretic stabilizer, on arbitrary test schemes. -/
theorem isPullback_toOrbit_rightMul :
    IsPullback (fst G (stabilizer G x)).left (stabilizer.rightMul G x).left
      (toOrbit G x) (toOrbit G x) := by
  have h := stabilizer.isPullback_rightMul G x
  have h' := PullbackCone.isLimitOfFactors _ _ (orbitInclusion G x)
    (orbitProjection G x) (orbitProjection G x)
    (orbitProjection_inclusion G x) (orbitProjection_inclusion G x) h.cone h.isLimit
  have hh : IsPullback (fst G (stabilizer G x)) (stabilizer.rightMul G x)
      (orbitProjection G x) (orbitProjection G x) :=
    IsPullback.of_isLimit' ⟨(cancel_mono (orbitInclusion G x)).mp (by
      simpa only [Category.assoc, orbitProjection_inclusion] using h.w)⟩ h'
  simpa only [Over.forget_map, orbitProjection_left] using hh.map (Over.forget _)

/-- The fibre of the orbit projection over its base point is the actual stabilizer. -/
theorem isPullback_toOrbit_stabilizer :
    IsPullback (stabilizer.incl G x).left (stabilizer G x).hom
      (toOrbit G x) (η[G] ≫ orbitProjection G x).left := by
  have h := orbitFiber.isPullback G x x
  have hx : (η[G] ≫ orbitProjection G x) ≫ orbitInclusion G x = x := by
    simp [orbitProjection_inclusion, MonObj.one_eq_one]
  have h' := PullbackCone.isLimitOfFactors _ _ (orbitInclusion G x)
    (orbitProjection G x) (η[G] ≫ orbitProjection G x)
    (orbitProjection_inclusion G x) hx h.cone h.isLimit
  have hh : IsPullback (stabilizer.incl G x) (toUnit (stabilizer G x))
      (orbitProjection G x) (η[G] ≫ orbitProjection G x) :=
    IsPullback.of_isLimit' ⟨(cancel_mono (orbitInclusion G x)).mp (by
      rw [Category.assoc, orbitProjection_inclusion, Category.assoc, hx]
      exact h.w)⟩ h'
  simpa only [Over.forget_map, Over.toUnit_left, orbitProjection_left] using
    hh.map (Over.forget _)

/-- Smoothness of the orbit projection implies smoothness of its scheme-theoretic stabilizer,
in every characteristic. -/
theorem smooth_stabilizer_of_smooth_toOrbit (h : Smooth (toOrbit G x)) :
    Smooth (stabilizer G x).hom :=
  MorphismProperty.of_isPullback (isPullback_toOrbit_stabilizer G x) h

/-- For a geometrically reduced group over any field, the orbit projection is smooth exactly when
its scheme-theoretic stabilizer is. The stabilizer need not be reduced a priori. -/
theorem smooth_toOrbit_iff [GeometricallyReduced G.hom] :
    Smooth (toOrbit G x) ↔ Smooth (stabilizer G x).hom := by
  refine ⟨smooth_stabilizer_of_smooth_toOrbit G x, fun hs ↦ ?_⟩
  let := hs
  have hp : Smooth (fst G (stabilizer G x)).left := by
    rw [Over.fst_left]
    infer_instance
  exact MorphismProperty.of_isPullback_of_surjective_of_flat_of_quasiCompact
    (isPullback_toOrbit_rightMul G x) hp

/-- Over any field of characteristic zero, orbit projections for affine finite-type groups are
smooth. No algebraic closedness, connectedness or reducedness hypothesis on the acting group is
needed. -/
instance smooth_toOrbit_of_charZero [CharZero k] [IsAffine G.left] :
    Smooth (toOrbit G x) := by
  have : Smooth G.hom := TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_charZero G
  exact (smooth_toOrbit_iff G x).mpr (smooth_stabilizer G x)

end Orbit

section Homogeneous

variable {k : Type u} [Field k]
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

/-- For a geometrically reduced finite-type group acting transitively on a reduced finite-type
scheme `X` over a field, the orbit morphism `G ⟶ X` is smooth if and only if the scheme-theoretic
stabilizer `stabilizer G x` is smooth over `Spec k`. -/
theorem smooth_orbitMap_iff_of_orbit_eq_univ [GeometricallyReduced G.hom] [IsReduced X.left]
    (h : orbit G x = Set.univ) :
    Smooth (orbitMap G x).left ↔ Smooth (stabilizer G x).hom := by
  have : Flat (orbitMap G x).left := flat_orbitMap_of_orbit_eq_univ G x h
  have : Surjective (orbitMap G x).left := (surjective_orbitMap_iff_orbit_eq_univ G x).mpr h
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  exact smooth_orbitMap_iff G x

/-- In characteristic zero, the orbit morphism from an affine finite-type group onto a reduced
finite-type homogeneous scheme over a field is smooth. -/
theorem smooth_orbitMap_of_orbit_eq_univ_of_charZero [CharZero k] [IsAffine G.left]
    [IsReduced X.left] (h : orbit G x = Set.univ) :
    Smooth (orbitMap G x).left := by
  have : Smooth G.hom := TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_charZero G
  exact (smooth_orbitMap_iff_of_orbit_eq_univ G x h).mpr (smooth_stabilizer G x)

end Homogeneous

end TauCeti.SchemeAction
