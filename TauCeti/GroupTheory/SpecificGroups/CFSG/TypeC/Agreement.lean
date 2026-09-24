/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Generation
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Basic
public import TauCeti.LinearAlgebra.RootSystem.RootLength

/-!
# The type-`C` carrier in the pinned symplectic model

A validated type-`C` index of rank `r` is built on the explicit full-weight standard symplectic
carrier `TauCeti.SpStd.groupScheme` at `TauCeti.TypeCLieIndex.carrierRank`, which is `r - 1`,
while the reference group of the diagram is the group of algebraic-closure-valued points of the
symplectic group scheme `Sp_{2r}` over `ℤ`. This file identifies those two groups, matches their
Bourbaki-numbered simple-root subgroups, and shows that the identification intertwines the
carrier's Steinberg endomorphism with entrywise `q`-power Frobenius on the pinned points, defined
independently of the carrier.

The comparison goes through the standard symplectic matrix group, which both sides realize with the
same underlying matrix: the carrier through `TauCeti.SpStd.pointsMulEquivGLSymplecticFin`, and the
scheme points through `TauCeti.Symplectic.schemePointsMulEquiv`. Both groups are formed at
`carrierRank + 1`, which is `r` by `TauCeti.TypeCLieIndex.carrierRank_add_one`, so that the carrier
comparison is the identity on matrices. The numbering needs no adapter: the carrier numbers its
generators node for node by the Bourbaki numbering of `Cᵣ`, the final node `r - 1` carrying the
long simple root `2eᵣ₋₁` and every other node `i` the adjacent difference root `eᵢ - eᵢ₊₁`.

Nothing here asserts that the fixed-point group of either Steinberg map is finite, perfect, or
simple.

## Main definitions

* `TauCeti.TypeCLieIndex.StandardGroup`: the standard symplectic matrix group.
* `TauCeti.TypeCLieIndex.PinnedGroup` and `TauCeti.TypeCLieIndex.pinnedEquivSymplectic`: the
  pinned scheme points and their matrix realization.
* `TauCeti.TypeCLieIndex.carrierEquivSymplectic` and `TauCeti.TypeCLieIndex.carrierEquivPinned`:
  the equivalences from the explicit carrier.
* `TauCeti.TypeCLieIndex.symplecticRootIndex`,
  `TauCeti.TypeCLieIndex.symplecticSimpleRootSubgroup` and
  `TauCeti.TypeCLieIndex.pinnedSimpleRootSubgroup`: the symplectic root and the root subgroups at
  a Bourbaki-numbered simple root of `Cᵣ`.
* `TauCeti.TypeCLieIndex.symplecticFrobenius` and `TauCeti.TypeCLieIndex.pinnedFrobenius`: the
  entrywise `q`-power Frobenius on the matrix group and on the pinned scheme points.

## Main results

* `TauCeti.TypeCLieIndex.carrierNode_eq_last_iff` and
  `TauCeti.TypeCLieIndex.symplecticRootIndex_of_isLongSimpleRoot`: the long simple root sits at the
  final carrier node, where the symplectic root is the long root `2eᵣ₋₁`; every other node carries
  a difference root, by `TauCeti.TypeCLieIndex.symplecticRootIndex_of_carrierNode_ne_last`.
* `TauCeti.TypeCLieIndex.carrierEquivPinned_simpleRootSubgroup`: the equivalence matches the
  numbered simple-root subgroups.
* `TauCeti.TypeCLieIndex.carrierEquivPinned_frobenius` and
  `TauCeti.TypeCLieIndex.carrierEquivPinned_steinberg`: the equivalence intertwines the carrier
  Frobenius and Steinberg map with the pinned Frobenius.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 11.3.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III.

The organization follows the rank-two comparison in
`TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Two.Agreement`.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.TypeCLieIndex

variable (d : TypeCLieIndex)

/-! ## The two realizations of the symplectic group -/

/-- The standard symplectic matrix group `Sp_{2r}` over the algebraic closure of the index's prime
field, formed at `carrierRank + 1 = r`. -/
abbrev StandardGroup : Type := GLSymplecticFin (d.carrierRank + 1) d.1.Closure

/-- The algebraic-closure-valued points of the pinned symplectic group scheme `Sp_{2r}` over `ℤ`,
formed at `carrierRank + 1 = r`. -/
noncomputable abbrev PinnedGroup : Type :=
  ((Spec (CommRingCat.of d.1.Closure)).asOver (Spec (CommRingCat.of ℤ)) ⟶
    (Symplectic.groupScheme ℤ (d.carrierRank + 1)).X)

/-- The canonical matrix realization of the pinned symplectic scheme points. -/
noncomputable def pinnedEquivSymplectic : d.PinnedGroup ≃* d.StandardGroup :=
  Symplectic.schemePointsMulEquiv (R := ℤ) (d.carrierRank + 1) d.1.Closure

/-- **The explicit type-`C` carrier is the standard symplectic matrix group.** The equivalence
preserves the underlying matrix. -/
noncomputable def carrierEquivSymplectic : d.AmbientGroup ≃* d.StandardGroup :=
  SpStd.pointsMulEquivGLSymplecticFin d.carrierRank d.1.Closure

/-- The carrier equivalence acts through the canonical identification with symplectic matrices. -/
theorem carrierEquivSymplectic_apply (g : d.AmbientGroup) :
    d.carrierEquivSymplectic g = SpStd.pointsMulEquivGLSymplecticFin d.carrierRank d.1.Closure g :=
  (rfl)

/-- **The explicit type-`C` carrier is equivalent to the points of the pinned `Sp_{2r}/ℤ` group
scheme.** -/
noncomputable def carrierEquivPinned : d.AmbientGroup ≃* d.PinnedGroup :=
  d.carrierEquivSymplectic.trans d.pinnedEquivSymplectic.symm

/-! ## The numbered simple root subgroups on the symplectic side -/

/-- **The long simple root sits at the final carrier node.** In the Bourbaki numbering of `Cᵣ` the
long simple root is the last node `r - 1`, and `carrierNode` moves no node value. -/
theorem carrierNode_eq_last_iff (i : Fin d.1.rank) :
    d.carrierNode i = Fin.last d.carrierRank ↔ d.1.dynkinType.IsLongSimpleRoot i := by
  have hcarrier : d.carrierNode i = Fin.last d.carrierRank ↔ (i : ℕ) + 1 = d.1.rank := by
    have := d.carrierRank_add_one
    rw [Fin.ext_iff, Fin.val_cast, Fin.val_last]
    omega
  obtain ⟨rank, q, hvalid, rfl⟩ := d.exists_eq_ofC
  rw [hcarrier, DynkinType.isLongSimpleRoot_congr (LieTypeIndex.dynkinType_C rank q)]
  simp only [DynkinType.isLongSimpleRoot_C, finCongr_apply, Fin.val_cast]
  simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType, LieTypeIndex.dynkinType_C,
    DynkinType.rank_C]

/-- **The symplectic root at the Bourbaki-numbered simple root `i` of `Cᵣ`**: the positive long
root `2eᵣ₋₁` at the final node, and the adjacent difference root `eᵢ - eᵢ₊₁` at every other node. -/
noncomputable def symplecticRootIndex (i : Fin d.1.rank) :
    GLSymplecticFin.RootSubgroupIndex (d.carrierRank + 1) :=
  if hi : d.carrierNode i = Fin.last d.carrierRank then .positiveLong (Fin.last d.carrierRank)
  else .difference (d.carrierNode i) (SpStd.next d.carrierRank (d.carrierNode i) hi)
    (SpStd.lt_next d.carrierRank (d.carrierNode i) hi).ne

/-- The symplectic root at the final carrier node is the positive long root `2eᵣ₋₁`. -/
theorem symplecticRootIndex_of_carrierNode_eq_last {i : Fin d.1.rank}
    (hi : d.carrierNode i = Fin.last d.carrierRank) :
    d.symplecticRootIndex i = .positiveLong (Fin.last d.carrierRank) := by
  simp only [symplecticRootIndex, hi, ↓reduceDIte]

/-- The symplectic root at a nonfinal carrier node is the adjacent difference root. -/
theorem symplecticRootIndex_of_carrierNode_ne_last {i : Fin d.1.rank}
    (hi : d.carrierNode i ≠ Fin.last d.carrierRank) :
    d.symplecticRootIndex i =
      .difference (d.carrierNode i) (SpStd.next d.carrierRank (d.carrierNode i) hi)
        (SpStd.lt_next d.carrierRank (d.carrierNode i) hi).ne := by
  simp only [symplecticRootIndex, hi, ↓reduceDIte]

/-- **At a long simple root the symplectic root is the positive long root `2eᵣ₋₁`.** -/
theorem symplecticRootIndex_of_isLongSimpleRoot {i : Fin d.1.rank}
    (hi : d.1.dynkinType.IsLongSimpleRoot i) :
    d.symplecticRootIndex i = .positiveLong (Fin.last d.carrierRank) :=
  d.symplecticRootIndex_of_carrierNode_eq_last ((d.carrierNode_eq_last_iff i).mpr hi)

/-- The positive simple-root subgroup of the standard symplectic matrix group at the
Bourbaki-numbered node `i` of `Cᵣ`. -/
noncomputable def symplecticSimpleRootSubgroup (i : Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.StandardGroup :=
  (d.symplecticRootIndex i).hom

/-- The positive simple-root subgroup of the pinned symplectic group scheme at the
Bourbaki-numbered node `i` of `Cᵣ`. -/
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
  GLSymplecticFin.map (d.carrierRank + 1) d.1.Closure
    (iterateFrobenius d.1.Closure d.1.characteristic d.1.fieldExponent)

/-- **The `q`-power Frobenius on the pinned symplectic scheme points**, defined through their
canonical matrix realization and independently of the explicit carrier. The type-`C` family is
untwisted, so this is also the pinned Steinberg map, matched with the carrier's by
`TauCeti.TypeCLieIndex.carrierEquivPinned_steinberg`. -/
noncomputable def pinnedFrobenius : d.PinnedGroup →* d.PinnedGroup :=
  d.pinnedEquivSymplectic.symm.toMonoidHom.comp
    (d.symplecticFrobenius.comp d.pinnedEquivSymplectic.toMonoidHom)

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
  change Symplectic.schemePointsMulEquiv (R := ℤ) (d.carrierRank + 1) d.1.Closure
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

/-! ## The carrier in the standard matrix realization -/

/-- **The carrier equivalence identifies each numbered simple-root subgroup with its standard
symplectic root one-parameter subgroup.** -/
@[simp]
theorem carrierEquivSymplectic_simpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.carrierEquivSymplectic (d.simpleRootSubgroup i u) =
      d.symplecticSimpleRootSubgroup i u := by
  rw [carrierEquivSymplectic, simpleRootSubgroup_def, symplecticSimpleRootSubgroup]
  by_cases hi : d.carrierNode i = Fin.last d.carrierRank
  · rw [d.symplecticRootIndex_of_carrierNode_eq_last hi, hi,
      SpStd.pointsMulEquivGLSymplecticFin_rootSubgroupPoints_inl_last,
      GLSymplecticFin.RootSubgroupIndex.hom_positiveLong,
      GLSymplecticFin.positiveLongRootTransvectionHom_apply]
  · rw [d.symplecticRootIndex_of_carrierNode_ne_last hi,
      SpStd.pointsMulEquivGLSymplecticFin_rootSubgroupPoints_inl_of_ne_last _ _ hi,
      GLSymplecticFin.RootSubgroupIndex.hom_difference,
      GLSymplecticFin.differenceShortRootHom_apply]

/-- **The carrier equivalence intertwines the two entrywise `q`-power Frobenius maps.** -/
@[simp]
theorem carrierEquivSymplectic_frobenius (g : d.AmbientGroup) :
    d.carrierEquivSymplectic (d.frobenius g) =
      d.symplecticFrobenius (d.carrierEquivSymplectic g) := by
  apply Subtype.ext
  rw [carrierEquivSymplectic, SpStd.coe_pointsMulEquivGLSymplecticFin_apply, frobenius_def,
    SpStd.coe_frobenius, symplecticFrobenius, GLSymplecticFin.coe_map,
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

/-- **The carrier Steinberg map agrees with the independently defined pinned `q`-power Frobenius**,
the Steinberg map of the untwisted type-`C` family on the pinned scheme points. -/
@[simp]
theorem carrierEquivPinned_steinberg (g : d.AmbientGroup) :
    d.carrierEquivPinned (d.steinberg g) = d.pinnedFrobenius (d.carrierEquivPinned g) := by
  rw [steinberg_def, carrierEquivPinned_frobenius]

end TauCeti.TypeCLieIndex
