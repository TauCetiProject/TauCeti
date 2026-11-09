/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
public import TauCeti.LowDimTopology.DehnSurgery.Filling

/-!
# Orientations of Dehn fillings

A Dehn filling `Y` of the exterior of a knot in an oriented `3`-manifold `X` contains the open
exterior, the complement in `X` of the closed solid torus, as the open complement of the filling
solid torus (`TauCeti.DehnFilling.range_openExteriorEmbedding`). An orientation of `Y` is
*compatible* with an orientation of `X` when the two orientations agree on the open exterior:
this is how a surgery on a knot in an oriented manifold, such as `S³`, is itself oriented, and it
is the orientation that statements about orientation-preserving homeomorphisms between surgered
manifolds refer to (Kirby's problems 1.19 and 1.81).

Orientations are the homological orientations of `TauCeti.HomologicalOrientation`, since the
filled space of a `TauCeti.DehnFilling` is only a topological space: compatibility
(`TauCeti.DehnFilling.IsOrientationCompatible`) asks that the orientations of `X` and of `Y` pull
back to the same orientation of the open exterior, along its inclusion in `X` and along
`TauCeti.DehnFilling.openExteriorEmbedding`. On a connected filled space a compatible orientation is
unique when the open exterior is nonempty (`TauCeti.DehnFilling.IsOrientationCompatible.unique`), so
being orientation-preserving is a well-defined property of a homeomorphism between two fillings of
knot exteriors in the same oriented manifold.

## Main definitions

* `TauCeti.DehnFilling.IsOrientationCompatible F o oY`: the orientation `oY` of the filled space
  agrees with the orientation `o` of the ambient space on the open exterior.

## Main results

* `TauCeti.DehnFilling.IsOrientationCompatible.unique`: on a connected filled space there is at
  most one orientation compatible with a given orientation of the ambient space, provided the open
  exterior is nonempty.
* `TauCeti.DehnFilling.isOrientationCompatible_neg_iff`: reversing both orientations preserves
  compatibility.
* `TauCeti.DehnFilling.isOrientationCompatible_transHomeomorph_iff`: compatibility after transport
  along a homeomorphism of the filled space.
* `TauCeti.IsSolidTorusNeighborhood.isOrientationCompatible_meridianDehnFilling`: the trivial
  filling, the ambient space itself, carries the ambient orientation as a compatible orientation.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9 (Dehn surgery on knots in
  oriented `3`-manifolds).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.3 (orientations
  as locally consistent local orientations, restricted along open subsets).
-/

public section

open Set Topology

namespace TauCeti

namespace DehnFilling

variable {X : Type} [TopologicalSpace X] [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}
  {h : IsSolidTorusNeighborhood f Φ} {s : Slope h.framedBoundaryTorus.H}
  {Y : Type} [TopologicalSpace Y] [T2Space Y]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E X] [ChartedSpace E Y] {d : ℕ}

/-- The orientation `oY` of the filled space `Y` of a Dehn filling `F` is **compatible** with the
orientation `o` of the ambient space `X` of the knot when the two agree on the open exterior,
the complement of the closed solid torus: they pull back to the same orientation of the open
exterior, along `TauCeti.DehnFilling.openExteriorEmbedding` and along its inclusion in `X`. -/
def IsOrientationCompatible (F : DehnFilling h s Y) (o : HomologicalOrientation X E d)
    (oY : HomologicalOrientation Y E d) : Prop :=
  oY.comap F.isOpenEmbedding_openExteriorEmbedding = o.comap h.openExterior.isOpenEmbedding'

theorem isOrientationCompatible_iff (F : DehnFilling h s Y) (o : HomologicalOrientation X E d)
    (oY : HomologicalOrientation Y E d) :
    F.IsOrientationCompatible o oY ↔
      oY.comap F.isOpenEmbedding_openExteriorEmbedding = o.comap h.openExterior.isOpenEmbedding' :=
  Iff.rfl

/-- At a point of the open exterior, a compatible orientation of the filled space is the
orientation of the ambient space, carried across by the two identifications of local homology
with that of the open exterior. -/
theorem IsOrientationCompatible.apply_openExteriorEmbedding {F : DehnFilling h s Y}
    {o : HomologicalOrientation X E d} {oY : HomologicalOrientation Y E d}
    (hF : F.IsOrientationCompatible o oY) (x : h.openExterior) :
    oY (F.openExteriorEmbedding x) =
      F.isOpenEmbedding_openExteriorEmbedding.localOrientationEquiv x d
        ((h.openExterior.isOpenEmbedding'.localOrientationEquiv x d).symm (o x)) := by
  rw [← HomologicalOrientation.localOrientationEquiv_comap_apply oY
    F.isOpenEmbedding_openExteriorEmbedding x, hF, HomologicalOrientation.comap_apply]

/-- **Compatible orientations are unique**: on a connected filled space, two orientations
compatible with the same orientation of the ambient space are equal, provided the open exterior is
nonempty. -/
theorem IsOrientationCompatible.unique [ConnectedSpace Y] {F : DehnFilling h s Y}
    {o : HomologicalOrientation X E d} {oY oY' : HomologicalOrientation Y E d}
    (hF : F.IsOrientationCompatible o oY) (hF' : F.IsOrientationCompatible o oY')
    (x : h.openExterior) : oY = oY' :=
  HomologicalOrientation.eq_of_apply_eq (x := F.openExteriorEmbedding x)
    (by rw [hF.apply_openExteriorEmbedding, hF'.apply_openExteriorEmbedding])

/-- Reversing both orientations preserves compatibility. -/
@[simp]
theorem isOrientationCompatible_neg_iff (F : DehnFilling h s Y)
    (o : HomologicalOrientation X E d) (oY : HomologicalOrientation Y E d) :
    F.IsOrientationCompatible (-o) (-oY) ↔ F.IsOrientationCompatible o oY := by
  simp only [isOrientationCompatible_iff, HomologicalOrientation.comap_neg, neg_inj]

/-- A Dehn filling transported along a homeomorphism `e : Y ≃ₜ Y'` carries the orientation `oY'`
of `Y'` as a compatible orientation exactly when the original filling carries the pullback of
`oY'` along `e`. -/
theorem isOrientationCompatible_transHomeomorph_iff (F : DehnFilling h s Y) {Y' : Type}
    [TopologicalSpace Y'] [T2Space Y'] [ChartedSpace E Y'] (e : Y ≃ₜ Y')
    (o : HomologicalOrientation X E d) (oY' : HomologicalOrientation Y' E d) :
    (F.transHomeomorph e).IsOrientationCompatible o oY' ↔
      F.IsOrientationCompatible o (oY'.comap e.isOpenEmbedding) := by
  rw [isOrientationCompatible_iff, isOrientationCompatible_iff,
    HomologicalOrientation.comap_comap,
    oY'.comap_congr (F.transHomeomorph e).isOpenEmbedding_openExteriorEmbedding
      (e.isOpenEmbedding.comp F.isOpenEmbedding_openExteriorEmbedding)
      (F.transHomeomorph_openExteriorEmbedding e)]

end DehnFilling

namespace IsSolidTorusNeighborhood

variable {X : Type} [TopologicalSpace X] [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E X] {d : ℕ}

/-- The trivial filling along the meridian, the ambient space itself
(`TauCeti.IsSolidTorusNeighborhood.meridianDehnFilling`), carries every orientation of the ambient
space as a compatible orientation. -/
theorem isOrientationCompatible_meridianDehnFilling (h : IsSolidTorusNeighborhood f Φ)
    (o : HomologicalOrientation X E d) : h.meridianDehnFilling.IsOrientationCompatible o o :=
  o.comap_congr _ _ h.meridianDehnFilling_openExteriorEmbedding

end IsSolidTorusNeighborhood

end TauCeti
