/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Stabilizer
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Stabilizer

/-!
# Orbit-map smoothness and stabilizer Hopf ideals

Let `G = Spec H` be an affine algebraic group scheme over a commutative ring `R` acting on a
scheme `X` over `Spec R`, and let `x : Spec R ⟶ X` be a section whose scheme-theoretic
stabilizer inclusion `stabilizer (Spec H) x ⟶ Spec H` is a closed immersion. Combining the
scheme-theoretic stabilizer smoothness criterion (`TauCeti.SchemeAction.smooth_orbitMap_iff`) with
the Hopf-ideal identification of `stabilizer (Spec H) x` shows that a faithfully flat and
quasi-compact orbit morphism `Spec H ⟶ X` is smooth over `Spec R` if and only if the quotient
Hopf algebra `H ⧸ stabilizerHopfIdeal H x` is smooth over `R`
(`TauCeti.SchemeAction.smooth_orbitMap_iff_smoothCommHopfAlgProperty_stabilizerHopfIdeal`).
In particular, this holds for homogeneous orbit morphisms of geometrically reduced finite-type
groups over a field
(`smooth_orbitMap_iff_smoothCommHopfAlgProperty_stabilizerHopfIdeal_of_orbit_eq_univ`).

## Main declarations

* `TauCeti.SchemeAction.smooth_orbitMap_iff_smoothCommHopfAlgProperty_stabilizerHopfIdeal`:
  smoothness of a faithfully flat, quasi-compact orbit morphism out of `Spec H` over `Spec R` in
  terms of `stabilizerHopfIdeal H x`.
* `smooth_orbitMap_iff_smoothCommHopfAlgProperty_stabilizerHopfIdeal_of_orbit_eq_univ`:
  specialization to homogeneous orbit morphisms over a field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §7.e, Proposition 7.15.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj

namespace TauCeti.SchemeAction

universe u

section CommRing

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)
  {X : Over (Spec (CommRingCat.of R))}
  [ModObj ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) X]
  (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ X)
  [IsClosedImmersion
    (stabilizer.incl ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x).left]

/-- Over an arbitrary commutative ring `R`, a faithfully flat, quasi-compact orbit morphism
`Spec H ⟶ X` is smooth if and only if the coordinate Hopf algebra
`H ⧸ stabilizerHopfIdeal H x` of its scheme-theoretic stabilizer is smooth over `R`. -/
theorem smooth_orbitMap_iff_smoothCommHopfAlgProperty_stabilizerHopfIdeal
    [Flat (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x).left]
    [Surjective (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x).left]
    [QuasiCompact (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x).left] :
    Smooth (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) x).left ↔
      smoothCommHopfAlgProperty R
        (_root_.CommHopfAlgCat.quotient H (stabilizerHopfIdeal H x)) :=
  (smooth_orbitMap_iff _ x).trans (smoothCommHopfAlgProperty_stabilizerHopfIdeal_iff H x).symm

end CommRing

section Homogeneous

variable {k : Type u} [Field k]
  (H : _root_.CommHopfAlgCat.{u} k) [Algebra.FiniteType k H]
  {X : Over (Spec (.of k))}
  [ModObj ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) X]
  [LocallyOfFiniteType X.hom] (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

local instance :
    LocallyOfFiniteType ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom :=
  (algebraFiniteType_iff_locallyOfFiniteType_hopfSpec k H).mp inferInstance

local instance :
    CompactSpace ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).left :=
  inferInstanceAs (CompactSpace (Spec (CommRingCat.of H)))

/-- For a geometrically reduced finite-type affine group acting transitively on a reduced
locally finite-type scheme `X` over a field, the orbit morphism `Spec H ⟶ X` is smooth if and only
if the coordinate Hopf algebra `H ⧸ stabilizerHopfIdeal H x` of the stabilizer is smooth over
`k`. -/
theorem smooth_orbitMap_iff_smoothCommHopfAlgProperty_stabilizerHopfIdeal_of_orbit_eq_univ
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]
    [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    Smooth (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left ↔
      smoothCommHopfAlgProperty k
        (_root_.CommHopfAlgCat.quotient H (stabilizerHopfIdeal H x)) :=
  (smooth_orbitMap_iff_of_orbit_eq_univ _ x h).trans
    (smoothCommHopfAlgProperty_stabilizerHopfIdeal_iff H x).symm

end Homogeneous

end TauCeti.SchemeAction
