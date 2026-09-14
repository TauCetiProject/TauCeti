/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Presentation
public import TauCeti.Algebra.Lie.E7.Minuscule.Carrier

/-!
# Presented points of the minuscule E₇ carrier

`TauCeti.E7Minuscule.pointsPresentation` presents the carrier's matrix points by its defining
integral Hopf ideal. The shared `GeneralLinear.IntegralPointsPresentation` API supplies maps
of value rings, their functoriality, and the representing equivalence with quotient-algebra
points. This file proves that those maps preserve the pinned root subgroups and weight torus.
-/

public section

namespace TauCeti.E7Minuscule

universe v v'

noncomputable section

/-- The carrier's matrix points, presented by its defining integral Hopf ideal. -/
abbrev pointsPresentation (A : Type v) [CommRing A] :
    GeneralLinear.IntegralPointsPresentation 56 definingIdeal A where
  subgroup := points A
  subgroup_eq := points_def A

variable {A : Type v} {B : Type v'} [CommRing A] [CommRing B]

/-- The induced map carries a numbered root-subgroup parameter along the homomorphism of value
rings. -/
@[simp]
theorem map_rootSubgroupPoints (f : A →+* B) (k : Fin 7 ⊕ Fin 7)
    (u : Multiplicative A) :
    (pointsPresentation A).map (pointsPresentation B) f (rootSubgroupPoints k A u) =
      rootSubgroupPoints k B (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  rw [GeneralLinear.IntegralPointsPresentation.coe_map,
    coe_rootSubgroupPoints, coe_rootSubgroupPoints,
    UniversalEnvelopingAlgebra.map_kostantRootSubgroupMatrix,
    AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply, RingHom.toIntAlgHom_apply]

/-- The induced map carries a point of the pinned split weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp]
theorem map_weightTorusPoints (f : A →+* B) (s : Fin 7 → Aˣ) :
    (pointsPresentation A).map (pointsPresentation B) f (weightTorusPoints A s) =
      weightTorusPoints B fun i ↦ Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  rw [GeneralLinear.IntegralPointsPresentation.coe_map,
    coe_weightTorusPoints, coe_weightTorusPoints]
  exact UniversalEnvelopingAlgebra.map_kostantTorusMatrix
    (M := lattice.toAddSubgroup) (b := latticeBasis)
      (wt := DynkinType.e7MinusculeWeight) f s

end

end TauCeti.E7Minuscule
