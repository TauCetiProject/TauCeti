/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.KnotTheory.Grid.Differential.Square.Annulus
public import TauCeti.KnotTheory.Grid.Differential.Square.DoubleTransposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing
public import TauCeti.KnotTheory.Grid.SimplyBlocked

/-!
# The grid differentials square to zero

The square of the unblocked grid differential `∂⁻` of `Unblocked.lean` is a sum over pairs of
composable rectangles which are empty and cover no `X`-marking. This file completes the
juxtaposition argument that the sum vanishes in characteristic two, so that `GC⁻` is a chain
complex.

The two side-column pairs of such a two-step term are equal, disjoint, or meet in exactly one
column. Equal pairs mean the second rectangle returns to the source of the first; those terms
cover a full toroidal annulus, hence an `X`-marking, and vanish over every coefficient ring. The
other two cases pair the terms off two by two, by a weight-preserving involution without fixed
points: rectangles with disjoint side columns are applied in the opposite order, and rectangles
sharing one side column bound an L-shaped hexagon which is cut the other way. Each pairing changes
the intermediate grid state and preserves the covered-square domain, hence the monomial weight, so
in characteristic two the two terms of a pair cancel.

Specializing carries the theorem to the two blocked theories, so their complexes are chain
complexes too. Setting one `V_i` to zero gives the simply blocked map, and specialization
intertwines the two differentials. Setting every `V_i` to zero — that is, taking constant terms —
gives the fully blocked differential of `Complex.lean`, whose rectangles must avoid the
`O`-markings as well: `GridDiagram.fullyBlockedRectangleCount_eq_constantCoeff` identifies its
matrix coefficients with the constant terms of `∂⁻` over `ZMod 2`.

## Main results

* `TauCeti.GridDiagram.sum_unblockedCoefficient_mul_unblockedCoefficient_eq_zero`: every matrix
  entry of the square of `∂⁻` vanishes.
* `TauCeti.GridDiagram.unblockedDifferential_comp_self_eq_zero`: `∂⁻ ∘ ∂⁻ = 0`.
* `TauCeti.GridDiagram.simplyBlockedDifferential_comp_self_eq_zero`: the same for the
  specialization at `V_i = 0`.
* `TauCeti.GridDiagram.fullyBlockedDecompositionCount_eq_zero`,
  `TauCeti.GridDiagram.fullyBlockedDifferential_comp_self_eq_zero`: the same for the fully blocked
  differential, the specialization at every `V_i = 0`.

## References

The juxtaposition proof follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Chapter 4.6.
-/
public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R] [CharP R 2]

/-- In characteristic two every matrix entry of the square of the unblocked grid differential
vanishes. -/
theorem sum_unblockedCoefficient_mul_unblockedCoefficient_eq_zero (x z : GridState n) :
    ∑ y : GridState n, G.unblockedCoefficient R x y * G.unblockedCoefficient R y z = 0 := by
  classical
  rcases eq_or_ne z x with rfl | hzx
  · exact Finset.sum_eq_zero fun y _ =>
      G.unblockedCoefficient_mul_unblockedCoefficient_eq_zero R z y
  rw [G.sum_unblockedCoefficient_mul_unblockedCoefficient R x z,
    ← Finset.sum_filter_add_sum_filter_not (G.unblockedDecompositions x z)
      (fun D => D.HasDisjointSides) (G.unblockedDecompositionWeight R)]
  have hdisjoint : ∑ D ∈ (G.unblockedDecompositions x z).filter
      (fun D => D.HasDisjointSides), G.unblockedDecompositionWeight R D = 0 := by
    refine Finset.sum_involution
      (fun D hD => D.commute (Finset.mem_filter.mp hD).2) (fun D hD => ?_) (fun D hD _ => ?_)
      (fun D hD => ?_) (fun D hD => ?_)
    · rw [G.unblockedDecompositionWeight_commute R D]
      exact CharTwo.add_self_eq_zero _
    · exact D.commute_ne _
    · exact Finset.mem_filter.mpr ⟨(G.commute_mem_unblockedDecompositions_iff D _).mpr
        (Finset.mem_filter.mp hD).1, D.hasDisjointSides_commute _⟩
    · exact D.commute_commute _
  have hone : ∀ D ∈ (G.unblockedDecompositions x z).filter
      (fun D => ¬D.HasDisjointSides), D.HasOneCommonSide := fun D hD =>
    (D.hasDisjointSides_or_hasOneCommonSide_of_ne hzx).resolve_left (Finset.mem_filter.mp hD).2
  have hfirst : ∀ D ∈ (G.unblockedDecompositions x z).filter
      (fun D => ¬D.HasDisjointSides), D.first ∈ G.unblockedRectangles x D.middle := fun D hD =>
    ((G.mem_unblockedDecompositions x z D).mp (Finset.mem_filter.mp hD).1).1
  have hsecond : ∀ D ∈ (G.unblockedDecompositions x z).filter
      (fun D => ¬D.HasDisjointSides), D.second ∈ G.unblockedRectangles D.middle z := fun D hD =>
    ((G.mem_unblockedDecompositions x z D).mp (Finset.mem_filter.mp hD).1).2
  have hcommon : ∑ D ∈ (G.unblockedDecompositions x z).filter
      (fun D => ¬D.HasDisjointSides), G.unblockedDecompositionWeight R D = 0 := by
    refine Finset.sum_involution
      (fun D hD => D.recut G (hone D hD) (hfirst D hD) (hsecond D hD)) (fun D hD => ?_)
      (fun D hD _ => ?_) (fun D hD => ?_) (fun D hD => ?_)
    · have hweight : G.unblockedDecompositionWeight R
          (D.recut G (hone D hD) (hfirst D hD) (hsecond D hD)) =
            G.unblockedDecompositionWeight R D := by
        rw [G.unblockedDecompositionWeight_def R, G.unblockedDecompositionWeight_def R]
        exact (D.isRecut_recut G (hone D hD) (hfirst D hD)
          (hsecond D hD)).isRepartition.OMonomial_mul_OMonomial G R
      rw [hweight]
      exact CharTwo.add_self_eq_zero _
    · exact D.recut_ne G _ _ _
    · refine Finset.mem_filter.mpr ⟨(G.mem_unblockedDecompositions x z _).mpr ⟨?_, ?_⟩, ?_⟩
      · exact (D.isRecut_recut G _ _ _).mem_unblockedRectangles_first
      · exact (D.isRecut_recut G _ _ _).mem_unblockedRectangles_second
      · exact GridRectangleDecomposition.not_hasDisjointSides_of_hasOneCommonSide _
          (D.hasOneCommonSide_recut G _ _ _)
    · exact D.recut_recut G _ _ _
  rw [hdisjoint, hcommon, add_zero]

/-- In characteristic two the square of the unblocked grid differential vanishes on a
generator. -/
theorem unblockedDifferential_sq_single_apply_eq_zero (x z : GridState n) :
    G.unblockedDifferential R (G.unblockedDifferential R (Finsupp.single x 1)) z = 0 := by
  rw [G.unblockedDifferential_sq_single_apply R x z]
  exact G.sum_unblockedCoefficient_mul_unblockedCoefficient_eq_zero R x z

/-- In characteristic two the square of the unblocked grid differential kills every
generator. -/
theorem unblockedDifferential_sq_single_eq_zero (x : GridState n) :
    G.unblockedDifferential R (G.unblockedDifferential R (Finsupp.single x 1)) = 0 := by
  refine Finsupp.ext fun z => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply]
  exact G.unblockedDifferential_sq_single_apply_eq_zero R x z

/-- The unblocked grid differential squares to zero in characteristic two. -/
theorem unblockedDifferential_comp_self_eq_zero :
    G.unblockedDifferential R ∘ₗ G.unblockedDifferential R =
      (0 : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n) := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_comp,
    LinearMap.zero_apply]
  exact G.unblockedDifferential_sq_single_eq_zero R x

/-- The simply blocked grid map squares to zero in characteristic two: it is the specialization
of `∂⁻` at `V_i = 0`, and specialization intertwines the two maps. -/
theorem simplyBlockedDifferential_comp_self_eq_zero (i : Fin n) :
    G.simplyBlockedDifferential R i ∘ₗ G.simplyBlockedDifferential R i =
      (0 : GridChainHat R n i →ₗ[MvPolynomial {c : Fin n // c ≠ i} R] GridChainHat R n i) := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_comp,
    LinearMap.zero_apply]
  have hsingle : (Finsupp.single x 1 : GridChainHat R n i) =
      simplyBlockedSpecialization R i (Finsupp.single x 1) := by
    rw [simplyBlockedSpecialization_single, map_one]
  rw [hsingle, ← G.simplyBlockedSpecialization_unblockedDifferential R i,
    ← G.simplyBlockedSpecialization_unblockedDifferential R i]
  rw [G.unblockedDifferential_sq_single_eq_zero R x, map_zero]

/-- Every fully blocked two-step decomposition count is even.

The fully blocked matrix coefficients are the constant terms of the unblocked ones over `ZMod 2`,
and taking constant terms is a ring homomorphism, so this entry of the fully blocked square is the
constant term of the corresponding entry of `∂⁻ ∘ ∂⁻`. -/
theorem fullyBlockedDecompositionCount_eq_zero (x z : GridState n) :
    G.fullyBlockedDecompositionCount x z = 0 := by
  have hterm : ∀ y : GridState n,
      G.fullyBlockedRectangleCount x y * G.fullyBlockedRectangleCount y z =
        MvPolynomial.constantCoeff
          (G.unblockedCoefficient (ZMod 2) x y * G.unblockedCoefficient (ZMod 2) y z) :=
    fun y => by
      rw [map_mul, G.fullyBlockedRectangleCount_eq_constantCoeff x y,
        G.fullyBlockedRectangleCount_eq_constantCoeff y z]
  rw [G.fullyBlockedDecompositionCount_eq_sum x z, Finset.sum_congr rfl fun y _ => hterm y,
    ← map_sum, G.sum_unblockedCoefficient_mul_unblockedCoefficient_eq_zero (ZMod 2) x z, map_zero]

/-- The fully blocked grid differential squares to zero, so the fully blocked grid complex of
`Complex.lean` is a chain complex. -/
theorem fullyBlockedDifferential_comp_self_eq_zero :
    G.fullyBlockedDifferential.comp G.fullyBlockedDifferential = 0 :=
  G.fullyBlockedDifferential_comp_self_eq_zero_iff_decompositionCount.mpr
    G.fullyBlockedDecompositionCount_eq_zero

end GridDiagram

end TauCeti
