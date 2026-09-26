/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Basic

/-!
# Presented points of the full-weight type-A carrier

`TauCeti.SlStd.pointsPresentation` presents the carrier's matrix points by its defining
integral Hopf ideal. The shared `GeneralLinear.IntegralPointsPresentation` API supplies maps
of value rings, their functoriality, and the representing equivalence with quotient-algebra
points. This file proves that those maps preserve the pinned root subgroups and weight torus.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.SlStd

universe v v'

noncomputable section

variable (r : ℕ)

/-- The carrier's matrix points, presented by its defining integral Hopf ideal. -/
abbrev pointsPresentation (A : Type v) [CommRing A] :
    TauCeti.GeneralLinear.IntegralPointsPresentation (r + 1) (definingIdeal r) A where
  val := points r A
  property := points_def r A

variable {A : Type v} {B : Type v'} [CommRing A] [CommRing B]

/-- The induced map carries a numbered root-subgroup parameter along the homomorphism of value
rings. -/
@[simp]
theorem map_rootSubgroupPoints (f : A →+* B) (k : Fin r ⊕ Fin r) (u : Multiplicative A) :
    (pointsPresentation r A).map (pointsPresentation r B) f (rootSubgroupPoints r k A u) =
      rootSubgroupPoints r k B (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralRootSubgroupPoints
      (e := rootGenerator r) (h := cartanGenerator r) (ρ := rep r)
      (M := (lattice r).toAddSubgroup)
      (hM := fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (hnil := isNilpotent_rep_rootGenerator r) (b := latticeBasis r)
      (wt := weight r) f k u)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map]
  simpa only [coe_rootSubgroupPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints] using h

/-- The induced map carries a point of the pinned split weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp]
theorem map_weightTorusPoints (f : A →+* B) (s : Fin r → Aˣ) :
    (pointsPresentation r A).map (pointsPresentation r B) f (weightTorusPoints r A s) =
      weightTorusPoints r B fun i => Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralWeightTorusPoints
      (e := rootGenerator r) (h := cartanGenerator r) (ρ := rep r)
      (M := (lattice r).toAddSubgroup)
      (hM := fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (hnil := isNilpotent_rep_rootGenerator r) (b := latticeBasis r)
      (wt := weight r) f s)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map]
  simpa only [coe_weightTorusPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralWeightTorusPoints] using h

end

end TauCeti.SlStd
