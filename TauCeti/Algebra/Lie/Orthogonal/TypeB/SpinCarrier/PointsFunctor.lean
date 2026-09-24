/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Basic

/-!
# Presented points of the full-weight type-B spin carrier

`TauCeti.TypeBSpinCarrier.pointsPresentation` presents the carrier's matrix points by its defining
integral Hopf ideal. The shared `GeneralLinear.IntegralPointsPresentation` API supplies maps
of value rings, their functoriality, and the representing equivalence with quotient-algebra
points. This file proves that those maps preserve the pinned root subgroups and weight torus.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  Sections 1.15 and 1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
-/

public section

namespace TauCeti.TypeBSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra

universe v v'

noncomputable section

variable (n : ℕ)

/-- The carrier's matrix points, presented by its defining integral Hopf ideal. -/
abbrev pointsPresentation (A : Type v) [CommRing A] :
    TauCeti.GeneralLinear.IntegralPointsPresentation (dimension n) (definingIdeal n) A where
  val := points n A
  property := points_def n A

variable {A : Type v} {B : Type v'} [CommRing A] [CommRing B]

/-- The induced map carries a numbered root-subgroup parameter along the homomorphism of value
rings. -/
@[simp]
theorem map_rootSubgroupPoints (f : A →+* B)
    (k : Fin (n + 1) ⊕ Fin (n + 1)) (u : Multiplicative A) :
    (pointsPresentation n A).map (pointsPresentation n B) f (rootSubgroupPoints n k A u) =
      rootSubgroupPoints n k B
        (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralRootSubgroupPoints
      (e := TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
      (h := TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (ρ := rep n)
      (M := (lattice n).toAddSubgroup) (hM := rep_kostantForm_mem_lattice n)
      (hnil := isNilpotent_rep_rootGenerator n) (b := latticeBasis n) (wt := basisWeight n) f k u)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map]
  simpa only [coe_rootSubgroupPoints, coe_kostantToralRootSubgroupPoints] using h

/-- The induced map carries a point of the split spin weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp]
theorem map_weightTorusPoints (f : A →+* B) (s : Fin (n + 1) → Aˣ) :
    (pointsPresentation n A).map (pointsPresentation n B) f (weightTorusPoints n A s) =
      weightTorusPoints n B fun i ↦ Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralWeightTorusPoints
      (e := TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
      (h := TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (ρ := rep n)
      (M := (lattice n).toAddSubgroup) (hM := rep_kostantForm_mem_lattice n)
      (hnil := isNilpotent_rep_rootGenerator n) (b := latticeBasis n) (wt := basisWeight n) f s)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map]
  simpa only [coe_weightTorusPoints, coe_kostantToralWeightTorusPoints] using h

end

end TauCeti.TypeBSpinCarrier
