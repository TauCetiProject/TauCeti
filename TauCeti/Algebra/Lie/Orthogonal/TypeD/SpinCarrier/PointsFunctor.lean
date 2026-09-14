/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Presentation
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Basic

/-!
# Presented points of the full-weight type-D spin carrier

`TauCeti.TypeDSpinCarrier.pointsPresentation` presents the carrier's matrix points by its defining
integral Hopf ideal. The shared `GeneralLinear.IntegralPointsPresentation` API supplies maps
of value rings, their functoriality, and the representing equivalence with quotient-algebra
points. This file proves that those maps preserve the pinned root subgroups and weight torus.
-/

public section

namespace TauCeti.TypeDSpinCarrier

universe v v'

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n)

/-- The carrier's matrix points, presented by its defining integral Hopf ideal. -/
abbrev pointsPresentation (A : Type v) [CommRing A] :
    GeneralLinear.IntegralPointsPresentation (dimension n) (definingIdeal n hn) A where
  subgroup := points n hn A
  subgroup_eq := points_def n hn A

variable {A : Type v} {B : Type v'} [CommRing A] [CommRing B]

/-- The induced map carries a numbered root-subgroup parameter along the homomorphism of value
rings. -/
@[simp]
theorem map_rootSubgroupPoints (f : A →+* B) (k : Fin n ⊕ Fin n)
    (u : Multiplicative A) :
    (pointsPresentation n hn A).map (pointsPresentation n hn B) f (rootSubgroupPoints n hn k A u) =
      rootSubgroupPoints n hn k B
        (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  rw [GeneralLinear.IntegralPointsPresentation.coe_map,
    coe_rootSubgroupPoints, coe_rootSubgroupPoints,
    UniversalEnvelopingAlgebra.map_kostantRootSubgroupMatrix,
    AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply, RingHom.toIntAlgHom_apply]

/-- The induced map carries a point of the split spin weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp]
theorem map_weightTorusPoints (f : A →+* B) (s : Fin n → Aˣ) :
    (pointsPresentation n hn A).map (pointsPresentation n hn B) f (weightTorusPoints n hn A s) =
      weightTorusPoints n hn B fun i ↦ Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  rw [GeneralLinear.IntegralPointsPresentation.coe_map,
    coe_weightTorusPoints, coe_weightTorusPoints]
  exact UniversalEnvelopingAlgebra.map_kostantTorusMatrix
    (M := (lattice n).toAddSubgroup) (b := latticeBasis n) (wt := basisWeight n) f s

end

end TauCeti.TypeDSpinCarrier
