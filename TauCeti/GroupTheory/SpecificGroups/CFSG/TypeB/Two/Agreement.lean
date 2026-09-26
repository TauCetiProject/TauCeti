/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Generation
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Two.Basic

/-!
# The rank-two `B₂` carrier in the pinned symplectic model

`TauCeti.RankTwoBLieIndex` collects the two classification-list families on the `B₂` diagram.
Both use an explicit full-weight rank-two type-`C` Chevalley carrier, while the reference group of
the diagram is the group of algebraic-closure-valued points of the symplectic group scheme
`Sp₄` over `ℤ`. This file identifies those two groups and matches their numbered simple-root
subgroups and Frobenius maps.

The comparison goes through the standard symplectic matrix group `Sp₄(K)`, which both sides
realize with the same underlying matrix: the carrier through
`TauCeti.SpStd.pointsMulEquivGLSymplecticFin`, and the scheme points through
`TauCeti.Symplectic.schemePointsMulEquiv`. Numbering is the one point where the sides differ:
the carrier is numbered as `C₂`, whose Bourbaki node `0` is short, while the `B₂` diagram has
node `0` long. The adapter `TauCeti.RankTwoBLieIndex.carrierNode` accounts for that swap.

Nothing here asserts that either family-specific fixed-point group is finite, perfect, or simple.

## Main definitions

* `TauCeti.RankTwoBLieIndex.StandardGroup`: the standard symplectic matrix group `Sp₄`.
* `TauCeti.RankTwoBLieIndex.PinnedGroup` and
  `TauCeti.RankTwoBLieIndex.pinnedEquivSymplectic`: the pinned scheme points and their matrix
  realization.
* `TauCeti.RankTwoBLieIndex.carrierEquivSymplectic` and
  `TauCeti.RankTwoBLieIndex.carrierEquivPinned`: the equivalences from the explicit carrier.
* `TauCeti.RankTwoBLieIndex.symplecticRootIndex` and
  `TauCeti.RankTwoBLieIndex.symplecticSimpleRootSubgroup`: the symplectic root and subgroup at a
  Bourbaki-numbered simple root of `B₂`.
* `TauCeti.RankTwoBLieIndex.pinnedSimpleRootSubgroup`,
  `TauCeti.RankTwoBLieIndex.pinnedFrobenius`, and
  `TauCeti.RankTwoBLieIndex.pinnedPrimeFrobenius`: the pinning and Frobenius data on the pinned
  scheme points.

## Main results

* `TauCeti.RankTwoBLieIndex.carrierEquivPinned_simpleRootSubgroup`: the equivalence matches the
  numbered simple-root subgroups.
* `TauCeti.RankTwoBLieIndex.carrierEquivPinned_frobenius` and
  `TauCeti.RankTwoBLieIndex.carrierEquivPinned_primeFrobenius`: the equivalence intertwines the
  corresponding Frobenius maps.
* `TauCeti.RankTwoBLieIndex.symplecticRootIndex_of_isLongSimpleRoot` and
  `TauCeti.RankTwoBLieIndex.symplecticRootIndex_of_not_isLongSimpleRoot`: the two numbered roots
  have the expected lengths.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates II and III.

The organization follows the type-`A` comparison in
`TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Agreement`.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.RankTwoBLieIndex

variable (d : RankTwoBLieIndex)

/-! ## The two realizations of the rank-two symplectic group -/

/-- The standard symplectic matrix group `Sp₄` over the algebraic closure of the index's prime
field. -/
abbrev StandardGroup : Type := GLSymplecticFin 2 d.1.Closure

/-- The algebraic-closure-valued points of the pinned symplectic group scheme `Sp₄` over `ℤ`. -/
noncomputable abbrev PinnedGroup : Type :=
  ((Spec (CommRingCat.of d.1.Closure)).asOver (Spec (CommRingCat.of ℤ)) ⟶
    (Symplectic.groupScheme ℤ 2).X)

/-- The canonical matrix realization of the pinned symplectic scheme points. -/
noncomputable def pinnedEquivSymplectic : d.PinnedGroup ≃* d.StandardGroup :=
  Symplectic.schemePointsMulEquiv (R := ℤ) 2 d.1.Closure

/-- **The explicit rank-two type-`C` carrier is the standard symplectic matrix group.** The
equivalence preserves the underlying matrix. -/
noncomputable def carrierEquivSymplectic : d.AmbientGroup ≃* d.StandardGroup :=
  SpStd.pointsMulEquivGLSymplecticFin 1 d.1.Closure

/-- The carrier equivalence acts through the canonical identification with symplectic matrices. -/
theorem carrierEquivSymplectic_apply (g : d.AmbientGroup) :
    d.carrierEquivSymplectic g = SpStd.pointsMulEquivGLSymplecticFin 1 d.1.Closure g :=
  (rfl)

/-- **The explicit rank-two type-`C` carrier is equivalent to the points of the pinned `Sp₄/ℤ`
group scheme.** -/
noncomputable def carrierEquivPinned : d.AmbientGroup ≃* d.PinnedGroup :=
  d.carrierEquivSymplectic.trans d.pinnedEquivSymplectic.symm

/-! ## The numbered simple root subgroups on the symplectic side -/

/-- **The symplectic root at the Bourbaki-numbered simple root `i` of `B₂`**: the positive long
root `2e₁` at the long node, which is the final carrier node, and the difference short root
`e₀ - e₁` at the short one. -/
noncomputable def symplecticRootIndex (i : Fin d.1.rank) : GLSymplecticFin.RootSubgroupIndex 2 :=
  ![.difference 0 1 (by decide), .positiveLong 1] (d.carrierNode i)

/-- The symplectic root at the final carrier node is the positive long root `2e₁`. -/
theorem symplecticRootIndex_of_carrierNode_eq_one {i : Fin d.1.rank}
    (h : d.carrierNode i = 1) : d.symplecticRootIndex i = .positiveLong 1 := by
  rw [symplecticRootIndex, h]
  rfl

/-- The symplectic root at the initial carrier node is the difference short root `e₀ - e₁`. -/
theorem symplecticRootIndex_of_carrierNode_eq_zero {i : Fin d.1.rank}
    (h : d.carrierNode i = 0) : d.symplecticRootIndex i = .difference 0 1 (by decide) := by
  rw [symplecticRootIndex, h]
  rfl

/-- Every Bourbaki-numbered simple root of `B₂` sits at one of the two carrier nodes. -/
private theorem carrierNode_eq_zero_or_eq_one (i : Fin d.1.rank) :
    d.carrierNode i = 0 ∨ d.carrierNode i = 1 := by
  generalize d.carrierNode i = c
  revert c
  decide

/-- **At a long simple root the symplectic root is the positive long root `2e₁`.** -/
theorem symplecticRootIndex_of_isLongSimpleRoot (i : Fin d.1.rank)
    (hi : d.1.dynkinType.IsLongSimpleRoot i) : d.symplecticRootIndex i = .positiveLong 1 :=
  d.symplecticRootIndex_of_carrierNode_eq_one ((d.carrierNode_eq_one_iff i).mpr hi)

/-- **At a short simple root the symplectic root is the difference short root `e₀ - e₁`.** -/
theorem symplecticRootIndex_of_not_isLongSimpleRoot (i : Fin d.1.rank)
    (hi : ¬d.1.dynkinType.IsLongSimpleRoot i) :
    d.symplecticRootIndex i = .difference 0 1 (by decide) :=
  d.symplecticRootIndex_of_carrierNode_eq_zero
    ((d.carrierNode_eq_zero_or_eq_one i).resolve_right
      fun h => hi ((d.carrierNode_eq_one_iff i).mp h))

/-- The positive simple-root subgroup of the standard symplectic matrix group at the
Bourbaki-numbered node `i` of `B₂`. -/
noncomputable def symplecticSimpleRootSubgroup (i : Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.StandardGroup :=
  (d.symplecticRootIndex i).hom

/-- The positive simple-root subgroup of the pinned symplectic group scheme at the
Bourbaki-numbered node `i` of `B₂`. -/
noncomputable def pinnedSimpleRootSubgroup (i : Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.PinnedGroup where
  toFun u :=
    (AdditiveGroup.schemePointsMulEquiv d.1.Closure).symm u ≫
      (Symplectic.rootSubgroup (R := ℤ) (d.symplecticRootIndex i)).hom.hom
  map_one' := by simp
  map_mul' u v := by
    rw [map_mul]
    apply MonObj.mul_comp

/-! ## The Frobenius maps on the symplectic side -/

/-- Entrywise `q`-power Frobenius on the standard symplectic matrix group, for `q` the field order
the index records. -/
noncomputable def symplecticFrobenius : d.StandardGroup →* d.StandardGroup :=
  GLSymplecticFin.map 2 d.1.Closure
    (iterateFrobenius d.1.Closure d.1.characteristic d.1.fieldExponent)

/-- Entrywise prime-field Frobenius on the standard symplectic matrix group. -/
noncomputable def symplecticPrimeFrobenius : d.StandardGroup →* d.StandardGroup :=
  GLSymplecticFin.map 2 d.1.Closure (iterateFrobenius d.1.Closure d.1.characteristic 1)

/-- The `q`-power Frobenius on the pinned symplectic scheme points, defined through their canonical
matrix realization and independently of the explicit carrier. -/
noncomputable def pinnedFrobenius : d.PinnedGroup →* d.PinnedGroup :=
  d.pinnedEquivSymplectic.symm.toMonoidHom.comp
    (d.symplecticFrobenius.comp d.pinnedEquivSymplectic.toMonoidHom)

/-- The prime-field Frobenius on the pinned symplectic scheme points. -/
noncomputable def pinnedPrimeFrobenius : d.PinnedGroup →* d.PinnedGroup :=
  d.pinnedEquivSymplectic.symm.toMonoidHom.comp
    (d.symplecticPrimeFrobenius.comp d.pinnedEquivSymplectic.toMonoidHom)

/-! ## The pinned data in the standard matrix realization -/

/-- Under the canonical matrix realization, a pinned simple-root element is its standard symplectic
root matrix. -/
@[simp]
theorem pinnedEquivSymplectic_pinnedSimpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.pinnedEquivSymplectic (d.pinnedSimpleRootSubgroup i u) =
      d.symplecticSimpleRootSubgroup i u := by
  -- Expose the `toFun` of the bundled `pinnedSimpleRootSubgroup` homomorphism so that the
  -- scheme-point root-subgroup equation can recognize the displayed composition.
  change Symplectic.schemePointsMulEquiv (R := ℤ) 2 d.1.Closure
      ((AdditiveGroup.schemePointsMulEquiv d.1.Closure).symm u ≫
        (Symplectic.rootSubgroup (R := ℤ) (d.symplecticRootIndex i)).hom.hom) = _
  rw [Symplectic.schemePointsMulEquiv_rootSubgroup, MulEquiv.apply_symm_apply,
    symplecticSimpleRootSubgroup]

/-- The canonical matrix realization intertwines pinned and matrix Frobenius. -/
@[simp]
theorem pinnedEquivSymplectic_pinnedFrobenius (g : d.PinnedGroup) :
    d.pinnedEquivSymplectic (d.pinnedFrobenius g) =
      d.symplecticFrobenius (d.pinnedEquivSymplectic g) := by
  rw [pinnedFrobenius, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rfl

/-- The canonical matrix realization intertwines the pinned and matrix prime-field Frobenius. -/
@[simp]
theorem pinnedEquivSymplectic_pinnedPrimeFrobenius (g : d.PinnedGroup) :
    d.pinnedEquivSymplectic (d.pinnedPrimeFrobenius g) =
      d.symplecticPrimeFrobenius (d.pinnedEquivSymplectic g) := by
  rw [pinnedPrimeFrobenius, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rfl

/-! ## The carrier in the standard matrix realization -/

private theorem one_eq_last : (1 : Fin 2) = Fin.last 1 := rfl

private theorem zero_ne_last : (0 : Fin 2) ≠ Fin.last 1 := by decide

private theorem next_zero : SpStd.next 1 0 zero_ne_last = 1 :=
  Fin.ext (by rw [SpStd.val_next]; rfl)

/-- **The carrier equivalence identifies each numbered simple-root subgroup with its standard
symplectic root one-parameter subgroup.** -/
@[simp]
theorem carrierEquivSymplectic_simpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.carrierEquivSymplectic (d.simpleRootSubgroup i u) =
      d.symplecticSimpleRootSubgroup i u := by
  rw [carrierEquivSymplectic, simpleRootSubgroup_def, symplecticSimpleRootSubgroup]
  rcases d.carrierNode_eq_zero_or_eq_one i with h | h
  · rw [h, d.symplecticRootIndex_of_carrierNode_eq_zero h,
      SpStd.pointsMulEquivGLSymplecticFin_rootSubgroupPoints_inl_of_ne_last 1 0 zero_ne_last,
      GLSymplecticFin.RootSubgroupIndex.hom_difference,
      GLSymplecticFin.differenceShortRootHom_apply]
    exact GLSymplecticFin.differenceShortRootUnit_congr _ _ rfl next_zero _
  · rw [h, d.symplecticRootIndex_of_carrierNode_eq_one h, one_eq_last,
      SpStd.pointsMulEquivGLSymplecticFin_rootSubgroupPoints_inl_last,
      GLSymplecticFin.RootSubgroupIndex.hom_positiveLong,
      GLSymplecticFin.positiveLongRootTransvectionHom_apply]

/-- **The carrier equivalence intertwines the two entrywise `q`-power Frobenius maps.** -/
@[simp]
theorem carrierEquivSymplectic_frobenius (g : d.AmbientGroup) :
    d.carrierEquivSymplectic (d.frobenius g) =
      d.symplecticFrobenius (d.carrierEquivSymplectic g) := by
  apply Subtype.ext
  rw [carrierEquivSymplectic, SpStd.coe_pointsMulEquivGLSymplecticFin_apply, frobenius_def,
    SpStd.coe_frobenius, symplecticFrobenius, GLSymplecticFin.coe_map,
    SpStd.coe_pointsMulEquivGLSymplecticFin_apply]

/-- **The carrier equivalence intertwines the two prime-field Frobenius maps.** -/
@[simp]
theorem carrierEquivSymplectic_primeFrobenius (g : d.AmbientGroup) :
    d.carrierEquivSymplectic (d.primeFrobenius g) =
      d.symplecticPrimeFrobenius (d.carrierEquivSymplectic g) := by
  apply Subtype.ext
  rw [carrierEquivSymplectic, SpStd.coe_pointsMulEquivGLSymplecticFin_apply, primeFrobenius_def,
    SpStd.coe_frobenius, symplecticPrimeFrobenius, GLSymplecticFin.coe_map,
    SpStd.coe_pointsMulEquivGLSymplecticFin_apply]

/-! ## The comparison with the pinned scheme points -/

/-- The pinned comparison, read in the standard matrix realization, is the carrier's own. -/
@[simp]
theorem pinnedEquivSymplectic_carrierEquivPinned (g : d.AmbientGroup) :
    d.pinnedEquivSymplectic (d.carrierEquivPinned g) = d.carrierEquivSymplectic g := by
  rw [carrierEquivPinned, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

/-- **The carrier-to-pinned equivalence matches the numbered simple root subgroups.** -/
@[simp]
theorem carrierEquivPinned_simpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.carrierEquivPinned (d.simpleRootSubgroup i u) = d.pinnedSimpleRootSubgroup i u := by
  apply d.pinnedEquivSymplectic.injective
  rw [pinnedEquivSymplectic_carrierEquivPinned, carrierEquivSymplectic_simpleRootSubgroup,
    pinnedEquivSymplectic_pinnedSimpleRootSubgroup]

/-- The carrier-to-pinned equivalence intertwines the two `q`-power Frobenius maps. -/
@[simp]
theorem carrierEquivPinned_frobenius (g : d.AmbientGroup) :
    d.carrierEquivPinned (d.frobenius g) = d.pinnedFrobenius (d.carrierEquivPinned g) := by
  apply d.pinnedEquivSymplectic.injective
  rw [pinnedEquivSymplectic_carrierEquivPinned, carrierEquivSymplectic_frobenius,
    pinnedEquivSymplectic_pinnedFrobenius, pinnedEquivSymplectic_carrierEquivPinned]

/-- The carrier-to-pinned equivalence intertwines the two prime-field Frobenius maps. -/
@[simp]
theorem carrierEquivPinned_primeFrobenius (g : d.AmbientGroup) :
    d.carrierEquivPinned (d.primeFrobenius g) =
      d.pinnedPrimeFrobenius (d.carrierEquivPinned g) := by
  apply d.pinnedEquivSymplectic.injective
  rw [pinnedEquivSymplectic_carrierEquivPinned, carrierEquivSymplectic_primeFrobenius,
    pinnedEquivSymplectic_pinnedPrimeFrobenius, pinnedEquivSymplectic_carrierEquivPinned]

end TauCeti.RankTwoBLieIndex
