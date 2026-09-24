/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
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

open TauCeti.UniversalEnvelopingAlgebra

universe v v'

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n)

/-- The carrier's matrix points, presented by its defining integral Hopf ideal. -/
abbrev pointsPresentation (A : Type v) [CommRing A] :
    TauCeti.GeneralLinear.IntegralPointsPresentation (dimension n) (definingIdeal n hn) A where
  val := points n hn A
  property := points_def n hn A

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
  have h := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralRootSubgroupPoints
      (e := TauCeti.serreRootGenerator (CartanMatrix.D n))
      (h := TauCeti.serreH ℚ (CartanMatrix.D n)) (ρ := rep n hn)
      (M := (lattice n).toAddSubgroup) (hM := rep_kostantForm_mem_lattice n hn)
      (hnil := isNilpotent_rep_rootGenerator n hn) (b := latticeBasis n)
      (wt := basisWeight n) f k u)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map]
  simpa only [coe_rootSubgroupPoints, coe_kostantToralRootSubgroupPoints] using h

/-- The induced map carries a point of the split spin weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp]
theorem map_weightTorusPoints (f : A →+* B) (s : Fin n → Aˣ) :
    (pointsPresentation n hn A).map (pointsPresentation n hn B) f (weightTorusPoints n hn A s) =
      weightTorusPoints n hn B fun i ↦ Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralWeightTorusPoints
      (e := TauCeti.serreRootGenerator (CartanMatrix.D n))
      (h := TauCeti.serreH ℚ (CartanMatrix.D n)) (ρ := rep n hn)
      (M := (lattice n).toAddSubgroup) (hM := rep_kostantForm_mem_lattice n hn)
      (hnil := isNilpotent_rep_rootGenerator n hn) (b := latticeBasis n) (wt := basisWeight n) f s)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map]
  simpa only [coe_weightTorusPoints, coe_kostantToralWeightTorusPoints] using h

end

end TauCeti.TypeDSpinCarrier
