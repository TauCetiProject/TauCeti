/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Stabilizer
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Homogeneous

/-!
# Orbit-map smoothness and stabilizer Hopf ideals

For a geometrically reduced finite-type affine algebraic group `G = Spec H` acting transitively on a
reduced locally finite-type scheme `X` over a field `k` with rational point `x : Spec k ⟶ X`,
combining the scheme-theoretic stabilizer smoothness criterion for homogeneous orbit maps with the
Hopf-ideal identification of `stabilizer (Spec H) x` shows that the orbit morphism `Spec H ⟶ X`
is smooth over `k` if and only if the quotient Hopf algebra `H ⧸ stabilizerHopfIdeal H x` is
smooth over `k`.

## Main declarations

* `TauCeti.SchemeAction.smooth_orbitMap_iff_smoothCommHopfAlgProperty_stabilizerHopfIdeal`:
  smoothness of a homogeneous orbit morphism out of `Spec H` in terms of
  `stabilizerHopfIdeal H x`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §7.e, Proposition 7.15.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj

namespace TauCeti.SchemeAction

universe u

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
theorem smooth_orbitMap_iff_smoothCommHopfAlgProperty_stabilizerHopfIdeal
    [GeometricallyReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom]
    [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    Smooth (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left ↔
      smoothCommHopfAlgProperty k
        (_root_.CommHopfAlgCat.quotient H (stabilizerHopfIdeal H x)) :=
  (smooth_orbitMap_iff_of_orbit_eq_univ _ x h).trans
    (smoothCommHopfAlgProperty_stabilizerHopfIdeal_iff H x).symm

end TauCeti.SchemeAction
