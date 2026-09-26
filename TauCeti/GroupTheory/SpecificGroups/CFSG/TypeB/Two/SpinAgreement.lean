/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.RankTwo
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Two.Agreement

/-!
# The spin carrier of `B₂(q)` in the pinned symplectic model

The untwisted family `Bₙ(q)` is built, at every rank including two, on the full-weight type-`B`
spin carrier: the ambient group of a validated type-`B` index is
`TauCeti.TypeBLieIndex.AmbientGroup`, the algebraic-closure-valued points of
`TauCeti.TypeBSpinCarrier.groupScheme` at the index's carrier rank, and its Steinberg endomorphism
is the `q`-power Frobenius `TauCeti.TypeBLieIndex.steinberg`. The reference group of the rank-two
diagram is the group of algebraic-closure-valued points of the symplectic group scheme `Sp₄` over
`ℤ`, the simply connected group of type `B₂ = C₂`.

This file identifies the two for an untwisted rank-two index `B₂(q)`, a
`TauCeti.TypeB2LieIndex`. The identification is the composite of two existing ones:

* `TauCeti.TypeBSpinCarrier.pointsMulEquivSymplecticPoints`, which identifies the rank-two spin
  carrier with the rank-two standard symplectic carrier by a signed permutation of the lattice
  bases (the spin representation of `Spin₅` being the standard representation of `Sp₄`), after
  reading the spin carrier of the index at rank parameter one;
* `TauCeti.RankTwoBLieIndex.carrierEquivPinned`, which identifies the rank-two standard symplectic
  carrier with the pinned `Sp₄/ℤ` scheme points.

The spin carrier numbers its generators by the Bourbaki numbering of `B₂`, node for node, while
the symplectic carrier numbers them by that of `C₂`; the first identification exchanges the two
nodes, and `TauCeti.RankTwoBLieIndex.carrierNode` records the same exchange on the symplectic
side, so the composite matches the Bourbaki-numbered simple root subgroups of the two sides with
no further adapter. Both identifications are integral, so the composite intertwines the carrier's
Steinberg endomorphism with the entrywise `q`-power Frobenius of the pinned points, which
`TauCeti.RankTwoBLieIndex.pinnedFrobenius` defines through the matrix realization of the pinned
points and independently of either carrier.

Since `TauCeti.TypeB2LieIndex.spinEquivPinned` intertwines the two endomorphisms,
`TauCeti.FixedPointCandidate.congr` transports the candidate group of `B₂(q)` along it to the
candidate group of the pinned Frobenius, so the candidate needs no restatement on the pinned side.
Nothing here asserts that any of these groups is finite, perfect, or simple, and nothing identifies
the spin carrier of rank at least three with a pinned group scheme.

## Main definitions

* `TauCeti.TypeB2LieIndex.spinEquivCarrier`: the ambient group of `B₂(q)` on the spin carrier is
  the ambient group on the rank-two symplectic carrier.
* `TauCeti.TypeB2LieIndex.spinEquivPinned`: the ambient group of `B₂(q)` is the group of points of
  the pinned `Sp₄/ℤ` group scheme.

## Main results

* `TauCeti.TypeB2LieIndex.spinEquivCarrier_simpleRootSubgroup`,
  `TauCeti.TypeB2LieIndex.spinEquivCarrier_frobenius` and
  `TauCeti.TypeB2LieIndex.spinEquivCarrier_primeFrobenius`: the carrier identification matches the
  numbered simple root subgroups and both Frobenius maps.
* `TauCeti.TypeB2LieIndex.spinEquivPinned_simpleRootSubgroup` and
  `TauCeti.TypeB2LieIndex.spinEquivPinned_steinberg`: the identification with the pinned points
  matches the numbered simple root subgroups and intertwines the Steinberg endomorphism of `B₂(q)`
  with the pinned `q`-power Frobenius.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* R. W. Carter, *Simple Groups of Lie Type*, §§11.3 and 14.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates II and III.

The organization follows the rank-two symplectic comparison in
`TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Two.Agreement`.
-/

public section

open scoped CategoryTheory.MonObj

namespace TauCeti.TypeB2LieIndex

variable (d : TypeB2LieIndex)

/-- The spin carrier serving an untwisted rank-two type-`B` index is the one at rank parameter
one, the carrier of type `B (1 + 1)`. -/
@[simp]
theorem carrierRank_toTypeBLieIndex : d.toTypeBLieIndex.carrierRank = 1 := by
  have h := d.toTypeBLieIndex.carrierRank_add_one
  rw [RankTwoBLieIndex.rank_eq_two] at h
  omega

/-! ## Reading the spin carrier at rank parameter one -/

-- The carrier rank of the index is not definitionally `1`, so the spin carrier of the index is
-- read at rank parameter one along `MulEquiv.cast`. The two transport statements below are
-- proved for a free rank parameter, where the equation can be substituted.

/-- Reading the spin carrier at another rank parameter along `MulEquiv.cast` preserves the
numbered root subgroups. -/
private theorem cast_rootSubgroupPoints {K : Type} [CommRing K] {n : ℕ} (h : n = 1)
    (k : Fin (n + 1) ⊕ Fin (n + 1)) (u : Multiplicative K) :
    MulEquiv.cast (M := fun n => TypeBSpinCarrier.points n K) h
        (TypeBSpinCarrier.rootSubgroupPoints n k K u) =
      TypeBSpinCarrier.rootSubgroupPoints 1
        (Sum.map (Fin.cast (congrArg (· + 1) h)) (Fin.cast (congrArg (· + 1) h)) k) K u := by
  subst h
  rcases k with k | k <;> rfl

/-- Reading the spin carrier at another rank parameter along `MulEquiv.cast` commutes with its
Frobenius maps. -/
private theorem cast_frobenius {K : Type} [CommRing K] {p e n : ℕ} [ExpChar K p] (h : n = 1)
    (g : TypeBSpinCarrier.points n K) :
    MulEquiv.cast (M := fun n => TypeBSpinCarrier.points n K) h
        (TypeBSpinCarrier.frobenius n p e K g) =
      TypeBSpinCarrier.frobenius 1 p e K
        (MulEquiv.cast (M := fun n => TypeBSpinCarrier.points n K) h g) := by
  subst h
  rfl

/-! ## The spin carrier and the rank-two symplectic carrier -/

/-- **The spin carrier of `B₂(q)` is the rank-two symplectic carrier.** The ambient group of the
index on the full-weight spin carrier, read at rank parameter one, is identified with the ambient
group on the rank-two standard symplectic carrier by
`TauCeti.TypeBSpinCarrier.pointsMulEquivSymplecticPoints`, which reindexes the four spin
coordinates and conjugates by a signed permutation matrix. -/
noncomputable def spinEquivCarrier : d.toTypeBLieIndex.AmbientGroup ≃* d.1.AmbientGroup :=
  (MulEquiv.cast (M := fun n => TypeBSpinCarrier.points n d.1.1.Closure)
    d.carrierRank_toTypeBLieIndex).trans
    (TypeBSpinCarrier.pointsMulEquivSymplecticPoints d.1.1.Closure)

/-- The carrier identification is the rank-two spin-to-symplectic identification, after reading
the spin carrier of the index at rank parameter one. -/
theorem spinEquivCarrier_apply (g : d.toTypeBLieIndex.AmbientGroup) :
    d.spinEquivCarrier g =
      TypeBSpinCarrier.pointsMulEquivSymplecticPoints d.1.1.Closure
        (MulEquiv.cast (M := fun n => TypeBSpinCarrier.points n d.1.1.Closure)
          d.carrierRank_toTypeBLieIndex g) :=
  (rfl)

-- This lemma and `spinEquivPinned_simpleRootSubgroup` state their left-hand sides through
-- `dsimp% only` (#8315): the types of the left-hand side are indexed unreduced, with projections
-- of `Subtype.mk` and `CommRingCat.of` literals, while `simp` reduces those projections before
-- it looks a term up, so the plain form is never found.
/-- **The carrier identification matches the Bourbaki-numbered simple root subgroups.** The spin
carrier's raising subgroup at node `i` of `B₂` goes to the symplectic carrier's raising subgroup
at the exchanged `C₂` node, which is the node `TauCeti.RankTwoBLieIndex.carrierNode` assigns to
`i`. -/
@[simp]
theorem spinEquivCarrier_simpleRootSubgroup (i : Fin d.1.1.rank)
    (u : Multiplicative d.1.1.Closure) :
    (dsimp% only (d.spinEquivCarrier (d.toTypeBLieIndex.simpleRootSubgroup i u))) =
      d.1.simpleRootSubgroup i u := by
  rw [spinEquivCarrier_apply, TypeBLieIndex.simpleRootSubgroup_def, cast_rootSubgroupPoints,
    RankTwoBLieIndex.simpleRootSubgroup_def]
  -- Both carrier nodes are the value of `i` read in `Fin 2`, to which the spin-to-symplectic
  -- identification and `RankTwoBLieIndex.carrierNode` apply the same swap of the two nodes.
  have hnode : Fin.cast (congrArg (· + 1) d.carrierRank_toTypeBLieIndex)
      (d.toTypeBLieIndex.carrierNode i) = finCongr d.1.rank_eq_two i :=
    Fin.ext (by simp)
  simp only [Sum.map_inl, hnode, TypeBSpinCarrier.pointsMulEquivSymplecticPoints_rootSubgroupPoints,
    TypeBSpinCarrier.symplecticRootIndex_inl, RankTwoBLieIndex.carrierNode_apply]
  generalize finCongr d.1.rank_eq_two i = j
  fin_cases j <;> simp

/-- **The carrier identification intertwines the two `q`-power Frobenius maps.** -/
@[simp]
theorem spinEquivCarrier_frobenius (g : d.toTypeBLieIndex.AmbientGroup) :
    d.spinEquivCarrier (d.toTypeBLieIndex.frobenius g) = d.1.frobenius (d.spinEquivCarrier g) := by
  rw [spinEquivCarrier_apply, spinEquivCarrier_apply, TypeBLieIndex.frobenius_def,
    RankTwoBLieIndex.frobenius_def, cast_frobenius,
    TypeBSpinCarrier.pointsMulEquivSymplecticPoints_frobenius]

/-- **The carrier identification intertwines the two prime-field Frobenius maps.** -/
@[simp]
theorem spinEquivCarrier_primeFrobenius (g : d.toTypeBLieIndex.AmbientGroup) :
    d.spinEquivCarrier (d.toTypeBLieIndex.primeFrobenius g) =
      d.1.primeFrobenius (d.spinEquivCarrier g) := by
  rw [spinEquivCarrier_apply, spinEquivCarrier_apply, TypeBLieIndex.primeFrobenius_def,
    RankTwoBLieIndex.primeFrobenius_def, cast_frobenius,
    TypeBSpinCarrier.pointsMulEquivSymplecticPoints_frobenius]

/-! ## The comparison with the pinned scheme points -/

/-- **The ambient group of `B₂(q)` is the group of points of the pinned `Sp₄/ℤ` group scheme.** It
is the carrier identification `spinEquivCarrier` followed by the identification
`TauCeti.RankTwoBLieIndex.carrierEquivPinned` of the rank-two symplectic carrier with the pinned
scheme points. -/
noncomputable def spinEquivPinned : d.toTypeBLieIndex.AmbientGroup ≃* d.1.PinnedGroup :=
  d.spinEquivCarrier.trans d.1.carrierEquivPinned

/-- The identification with the pinned points passes through the rank-two symplectic carrier. -/
theorem spinEquivPinned_apply (g : d.toTypeBLieIndex.AmbientGroup) :
    d.spinEquivPinned g = d.1.carrierEquivPinned (d.spinEquivCarrier g) :=
  (rfl)

/-- **The identification with the pinned points matches the Bourbaki-numbered simple root
subgroups**: `e (x_i(u)) = x'_i(u)` for the pinned simple root subgroups `x'_i` of `Sp₄/ℤ`. -/
@[simp]
theorem spinEquivPinned_simpleRootSubgroup (i : Fin d.1.1.rank)
    (u : Multiplicative d.1.1.Closure) :
    (dsimp% only (d.spinEquivPinned (d.toTypeBLieIndex.simpleRootSubgroup i u))) =
      d.1.pinnedSimpleRootSubgroup i u := by
  rw [spinEquivPinned_apply, spinEquivCarrier_simpleRootSubgroup,
    RankTwoBLieIndex.carrierEquivPinned_simpleRootSubgroup]

/-- The identification with the pinned points intertwines the carrier's `q`-power Frobenius with
the pinned one. -/
@[simp]
theorem spinEquivPinned_frobenius (g : d.toTypeBLieIndex.AmbientGroup) :
    d.spinEquivPinned (d.toTypeBLieIndex.frobenius g) =
      d.1.pinnedFrobenius (d.spinEquivPinned g) := by
  rw [spinEquivPinned_apply, spinEquivCarrier_frobenius,
    RankTwoBLieIndex.carrierEquivPinned_frobenius, spinEquivPinned_apply]

/-- The identification with the pinned points intertwines the two prime-field Frobenius maps. -/
@[simp]
theorem spinEquivPinned_primeFrobenius (g : d.toTypeBLieIndex.AmbientGroup) :
    d.spinEquivPinned (d.toTypeBLieIndex.primeFrobenius g) =
      d.1.pinnedPrimeFrobenius (d.spinEquivPinned g) := by
  rw [spinEquivPinned_apply, spinEquivCarrier_primeFrobenius,
    RankTwoBLieIndex.carrierEquivPinned_primeFrobenius, spinEquivPinned_apply]

/-- **The identification with the pinned points intertwines the Steinberg endomorphism of
`B₂(q)` with the pinned `q`-power Frobenius**: `e (F g) = F' (e g)`, where `F'` is defined on the
pinned points through their matrix realization, independently of the spin carrier. -/
@[simp]
theorem spinEquivPinned_steinberg (g : d.toTypeBLieIndex.AmbientGroup) :
    d.spinEquivPinned (d.toTypeBLieIndex.steinberg g) =
      d.1.pinnedFrobenius (d.spinEquivPinned g) := by
  rw [TypeBLieIndex.steinberg_def, spinEquivPinned_frobenius]

end TauCeti.TypeB2LieIndex
