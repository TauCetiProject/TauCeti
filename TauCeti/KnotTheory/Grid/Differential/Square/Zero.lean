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
juxtaposition argument that the sum vanishes in characteristic two. That is the square-zero
condition a chain complex structure on `GC⁻` needs; the structure itself is not built here.

The two side-column pairs of such a two-step term are equal, disjoint, or meet in exactly one
column. Equal pairs mean the second rectangle returns to the source of the first; those terms
cover a full toroidal annulus, hence an `X`-marking, and vanish over every coefficient ring. The
other two cases pair the terms off two by two, by a weight-preserving involution without fixed
points: rectangles with disjoint side columns are applied in the opposite order, and rectangles
sharing one side column bound an L-shaped hexagon which is cut the other way. Each pairing changes
the intermediate grid state and preserves the covered-square domain, hence the monomial weight, so
in characteristic two the two terms of a pair cancel. The pairing is stated separately, for any
function on decompositions whose paired terms cancel, so that a sign assignment can reuse it over
coefficient rings of other characteristics.

Specializing carries the square-zero identity to the two blocked theories as well. Setting one
`V_i` to zero gives the simply blocked map, and specialization intertwines the two differentials.
Setting every `V_i` to zero — that is, taking constant terms — gives the fully blocked
differential `TauCeti.GridDiagram.fullyBlockedDifferential`, whose rectangles must avoid the
`O`-markings as well:
`GridDiagram.fullyBlockedRectangleCount_eq_constantCoeff` identifies its matrix coefficients with
the constant terms of `∂⁻` over `ZMod 2`.

## Main results

* `TauCeti.GridRectangleDecomposition.sum_eq_zero_of_pairing`: the pairing itself, for any
  family of decompositions into empty rectangles closed under both pairings and any function on
  decompositions whose paired terms cancel, over any coefficients.
* `TauCeti.GridDiagram.sum_unblockedDecompositions_eq_zero`: the pairing for the decompositions
  counted by the square of `∂⁻`.
* `TauCeti.GridDiagram.unblockedDecompositionWeight_recut`: recutting a decomposition preserves
  its weight.
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

namespace GridRectangleDecomposition

variable {n : ℕ}

/-- **The juxtaposition pairing.** Let `S` be a finite family of two-step decompositions from `x`
to a different state `z` into two empty rectangles, closed under reordering two rectangles with
disjoint side columns and under recutting two rectangles that share one side column. A function on
decompositions sums to zero over `S` when each term cancels its partner under both pairings.

Over `𝔽₂` the partners carry equal weights; over a general coefficient ring a sign assignment makes
them carry opposite signs. -/
theorem sum_eq_zero_of_pairing {M : Type*} [AddCommMonoid M] {x z : GridState n} (hzx : z ≠ x)
    {S : Finset (GridRectangleDecomposition x z)}
    (hempty : ∀ D ∈ S, D.first.IsEmpty ∧ D.second.IsEmpty)
    (hcommute_mem : ∀ D ∈ S, ∀ h : D.HasDisjointSides, D.commute h ∈ S)
    (hrecut_mem : ∀ D ∈ S, ∀ (hone : D.HasOneCommonSide) (hfirst : D.first.IsEmpty)
      (hsecond : D.second.IsEmpty), D.recut hone hfirst hsecond ∈ S)
    (f : GridRectangleDecomposition x z → M)
    (hcommute : ∀ D ∈ S, ∀ h : D.HasDisjointSides, f D + f (D.commute h) = 0)
    (hrecut : ∀ D ∈ S, ∀ (hone : D.HasOneCommonSide) (hfirst : D.first.IsEmpty)
      (hsecond : D.second.IsEmpty), f D + f (D.recut hone hfirst hsecond) = 0) :
    ∑ D ∈ S, f D = 0 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not S (fun D => D.HasDisjointSides) f]
  have hdisjoint : ∑ D ∈ S.filter (fun D => D.HasDisjointSides), f D = 0 :=
    Finset.sum_involution (fun D hD => D.commute (Finset.mem_filter.mp hD).2)
      (fun D hD => hcommute D (Finset.mem_filter.mp hD).1 _) (fun D _ _ => D.commute_ne _)
      (fun D hD => Finset.mem_filter.mpr
        ⟨hcommute_mem D (Finset.mem_filter.mp hD).1 _, D.hasDisjointSides_commute _⟩)
      (fun D _ => D.commute_commute _)
  have hone : ∀ D ∈ S.filter (fun D => ¬D.HasDisjointSides), D.HasOneCommonSide := fun D hD =>
    (D.hasDisjointSides_or_hasOneCommonSide_of_ne hzx).resolve_left (Finset.mem_filter.mp hD).2
  have hempty' : ∀ D ∈ S.filter (fun D => ¬D.HasDisjointSides),
      D.first.IsEmpty ∧ D.second.IsEmpty := fun D hD => hempty D (Finset.mem_filter.mp hD).1
  have hcommon : ∑ D ∈ S.filter (fun D => ¬D.HasDisjointSides), f D = 0 :=
    Finset.sum_involution
      (fun D hD => D.recut (hone D hD) (hempty' D hD).1 (hempty' D hD).2)
      (fun D hD => hrecut D (Finset.mem_filter.mp hD).1 _ _ _) (fun D _ _ => D.recut_ne _ _ _)
      (fun D hD => Finset.mem_filter.mpr ⟨hrecut_mem D (Finset.mem_filter.mp hD).1 _ _ _,
        not_hasDisjointSides_of_hasOneCommonSide _ (D.hasOneCommonSide_recut _ _ _)⟩)
      (fun D _ => D.recut_recut _ _ _)
  rw [hdisjoint, hcommon, add_zero]

end GridRectangleDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The juxtaposition pairing for the square of `∂⁻`: a function on the two-step decompositions
counted by the square of `∂⁻` sums to zero over the decompositions from `x` to a different state
`z`, provided each term cancels its partner under both pairings, reordering two rectangles with
disjoint side columns and recutting two rectangles that share one side column. -/
theorem sum_unblockedDecompositions_eq_zero {M : Type*} [AddCommMonoid M] {x z : GridState n}
    (hzx : z ≠ x) (f : GridRectangleDecomposition x z → M)
    (hcommute : ∀ D ∈ G.unblockedDecompositions x z, ∀ h : D.HasDisjointSides,
      f D + f (D.commute h) = 0)
    (hrecut : ∀ D ∈ G.unblockedDecompositions x z, ∀ (hone : D.HasOneCommonSide)
      (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty),
      f D + f (D.recut hone hfirst hsecond) = 0) :
    ∑ D ∈ G.unblockedDecompositions x z, f D = 0 := by
  refine GridRectangleDecomposition.sum_eq_zero_of_pairing hzx (fun D hD => ?_)
    (fun D hD h => (G.commute_mem_unblockedDecompositions_iff D h).mpr hD)
    (fun D hD hone hfirst hsecond => ?_) f hcommute hrecut
  · obtain ⟨h₁, h₂⟩ := (G.mem_unblockedDecompositions x z D).mp hD
    exact ⟨G.isEmpty_of_mem_unblockedRectangles h₁, G.isEmpty_of_mem_unblockedRectangles h₂⟩
  · -- The recut covers the same squares, so it again avoids the `X`-markings.
    obtain ⟨h₁, h₂⟩ := (G.mem_unblockedDecompositions x z D).mp hD
    have hrecut := D.isRecut_recut hone hfirst hsecond
    have hX₁ := G.disjoint_XSet_of_mem_unblockedRectangles h₁
    have hX₂ := G.disjoint_XSet_of_mem_unblockedRectangles h₂
    refine (G.mem_unblockedDecompositions x z _).mpr ⟨?_, ?_⟩
    · exact (G.mem_unblockedRectangles _).mpr
        ⟨hrecut.isEmpty_first, hrecut.isRepartition.disjoint_coveredSquares_first hX₁ hX₂⟩
    · exact (G.mem_unblockedRectangles _).mpr
        ⟨hrecut.isEmpty_second, hrecut.isRepartition.disjoint_coveredSquares_second hX₁ hX₂⟩

/-- Recutting a two-step decomposition by two empty rectangles sharing one side column preserves
its weight: the two decompositions cover the same squares. -/
theorem unblockedDecompositionWeight_recut (R : Type*) [CommSemiring R] {x z : GridState n}
    (D : GridRectangleDecomposition x z) (hone : D.HasOneCommonSide) (hfirst : D.first.IsEmpty)
    (hsecond : D.second.IsEmpty) :
    G.unblockedDecompositionWeight R (D.recut hone hfirst hsecond) =
      G.unblockedDecompositionWeight R D := by
  rw [G.unblockedDecompositionWeight_def R, G.unblockedDecompositionWeight_def R]
  exact (D.isRecut_recut hone hfirst hsecond).isRepartition.OMonomial_mul_OMonomial G R

variable (R : Type*) [CommSemiring R] [CharP R 2]

/-- In characteristic two every matrix entry of the square of the unblocked grid differential
vanishes. -/
theorem sum_unblockedCoefficient_mul_unblockedCoefficient_eq_zero (x z : GridState n) :
    ∑ y : GridState n, G.unblockedCoefficient R x y * G.unblockedCoefficient R y z = 0 := by
  rcases eq_or_ne z x with rfl | hzx
  · exact Finset.sum_eq_zero fun y _ =>
      G.unblockedCoefficient_mul_unblockedCoefficient_eq_zero R z y
  rw [G.sum_unblockedCoefficient_mul_unblockedCoefficient R x z]
  refine G.sum_unblockedDecompositions_eq_zero hzx _ (fun D _ h => ?_)
    (fun D _ hone hfirst hsecond => ?_)
  · rw [G.unblockedDecompositionWeight_commute R D]
    exact CharTwo.add_self_eq_zero _
  · rw [G.unblockedDecompositionWeight_recut R D]
    exact CharTwo.add_self_eq_zero _

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

/-- The fully blocked grid differential `TauCeti.GridDiagram.fullyBlockedDifferential` squares to
zero. -/
theorem fullyBlockedDifferential_comp_self_eq_zero :
    G.fullyBlockedDifferential.comp G.fullyBlockedDifferential = 0 :=
  G.fullyBlockedDifferential_comp_self_eq_zero_iff_decompositionCount.mpr
    G.fullyBlockedDecompositionCount_eq_zero

end GridDiagram

end TauCeti
