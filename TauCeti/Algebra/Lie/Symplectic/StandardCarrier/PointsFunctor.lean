/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Presentation
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Scheme

/-!
# Presented points of the full-weight type-C carrier

`TauCeti.SpStd.pointsPresentation` presents the carrier's matrix points by its defining
integral Hopf ideal. The shared `GeneralLinear.IntegralPointsPresentation` API supplies maps
of value rings, their functoriality, and the representing equivalence with quotient-algebra
points. This file proves that those maps preserve the pinned root subgroups and weight torus.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  Sections 1.15 and 1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.SpStd

universe v v'

noncomputable section

variable (n : ℕ)

/-- The carrier's matrix points, presented by its defining integral Hopf ideal. -/
abbrev pointsPresentation (A : Type v) [CommRing A] :
    GeneralLinear.IntegralPointsPresentation ((n + 1) + (n + 1)) (definingIdeal n) A where
  val := points n A
  property := points_def n A

variable {A : Type v} {B : Type v'} [CommRing A] [CommRing B]

/-- The induced map carries a numbered root-subgroup parameter along the homomorphism of value
rings. -/
@[simp]
theorem map_rootSubgroupPoints (f : A →+* B)
    (i : Fin (n + 1) ⊕ Fin (n + 1)) (u : Multiplicative A) :
    (pointsPresentation n A).map (pointsPresentation n B) f (rootSubgroupPoints n i A u) =
      rootSubgroupPoints n i B (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  rw [GeneralLinear.IntegralPointsPresentation.coe_map,
    coe_rootSubgroupPoints, coe_rootSubgroupPoints,
    UniversalEnvelopingAlgebra.map_kostantRootSubgroupMatrix,
    AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply, RingHom.toIntAlgHom_apply]

/-- The induced map carries a point of the pinned split weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp]
theorem map_weightTorusPoints (f : A →+* B) (s : Fin (n + 1) → Aˣ) :
    (pointsPresentation n A).map (pointsPresentation n B) f (weightTorusPoints n A s) =
      weightTorusPoints n B fun i ↦ Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  rw [GeneralLinear.IntegralPointsPresentation.coe_map,
    coe_weightTorusPoints, coe_weightTorusPoints]
  exact UniversalEnvelopingAlgebra.map_kostantTorusMatrix
    (M := (lattice n).toAddSubgroup) (b := latticeBasis n) (wt := basisWeight n) f s

end

end TauCeti.SpStd
