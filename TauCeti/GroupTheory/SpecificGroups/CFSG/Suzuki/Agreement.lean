/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.SpecialIsogeny
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Basic

/-!
# The rank-two `B₂` carrier in the pinned symplectic model

`TauCeti.RankTwoBLieIndex` attaches to an index on the `B₂` diagram the explicit full-weight
rank-two type-`C` Chevalley carrier, whose points over an algebraic closure of the prime field
carry the numbered simple root subgroups of `B₂` and, in characteristic two, the special isogeny
`τ` whose odd power is the Suzuki family's Steinberg endomorphism. The reference group of that
diagram is the group of algebraic-closure-valued points of the symplectic group scheme `Sp₄` over
`ℤ`, its simply connected Chevalley group. This file identifies the two, together with all of the
pinned data the identification has to match.

The comparison goes through the standard symplectic matrix group `Sp₄(K)`, which both sides realize
with the same underlying matrix: the carrier by `TauCeti.SpStd.pointsMulEquivGLSymplecticFin` and
the scheme points by `TauCeti.Symplectic.schemePointsMulEquiv`. On that common realization the
pinned simple root subgroups are the standard symplectic root one-parameter subgroups, the pinned
Frobenius is entrywise Frobenius, and the pinned half-Frobenius is the matrix special isogeny
`TauCeti.specialIsogeny`, each built from the symplectic side alone rather than transported from
the carrier. The pinned Steinberg map of a Suzuki index is then the same odd power of the pinned
half-Frobenius that the carrier's is of the carrier's, and `carrierEquivPinned_simpleRootSubgroup`
and `carrierEquivPinned_steinberg` say that the equivalence matches the numbered pinning and
intertwines the two Steinberg maps.

Numbering is the one point where the two sides genuinely differ. The carrier is numbered as `C₂`,
whose Bourbaki node `0` is short, while the `B₂` diagram the index names has node `0` long;
`TauCeti.RankTwoBLieIndex.carrierNode` is the adapter between them, and
`TauCeti.RankTwoBLieIndex.symplecticRootIndex` reads off, for a Bourbaki-numbered simple root of
`B₂`, the symplectic root it is: the positive long root `2e₁` at the long node and the difference
short root `e₀ - e₁` at the short one.

Nothing here asserts that any group is finite, perfect or simple, and no order is computed.

## Main definitions

* `TauCeti.RankTwoBLieIndex.StandardGroup`: the standard symplectic matrix group `Sp₄` over the
  algebraic closure of the index's prime field.
* `TauCeti.RankTwoBLieIndex.PinnedGroup` and
  `TauCeti.RankTwoBLieIndex.pinnedEquivSymplectic`: the algebraic-closure-valued points of the
  pinned `Sp₄/ℤ` group scheme and their canonical matrix realization.
* `TauCeti.RankTwoBLieIndex.carrierEquivSymplectic` and
  `TauCeti.RankTwoBLieIndex.carrierEquivPinned`: the equivalences from the explicit carrier.
* `TauCeti.RankTwoBLieIndex.symplecticRootIndex` and
  `TauCeti.RankTwoBLieIndex.symplecticSimpleRootSubgroup`: the symplectic root, and its
  one-parameter subgroup, at a Bourbaki-numbered simple root of `B₂`.
* `TauCeti.RankTwoBLieIndex.symplecticFrobenius` and
  `TauCeti.RankTwoBLieIndex.symplecticPrimeFrobenius`: the standard matrix Frobenius maps, with
  `TauCeti.SuzukiLieIndex.symplecticHalfFrobenius` and
  `TauCeti.SuzukiLieIndex.symplecticSteinberg` the special isogeny and its odd power.
* `TauCeti.RankTwoBLieIndex.pinnedSimpleRootSubgroup`,
  `TauCeti.RankTwoBLieIndex.pinnedFrobenius`, `TauCeti.RankTwoBLieIndex.pinnedPrimeFrobenius`,
  `TauCeti.SuzukiLieIndex.pinnedHalfFrobenius` and `TauCeti.SuzukiLieIndex.pinnedSteinberg`: the
  pinning and Steinberg data on the pinned scheme points.

## Main results

* `TauCeti.RankTwoBLieIndex.carrierEquivPinned_simpleRootSubgroup`: the equivalence matches the
  numbered simple root subgroups.
* `TauCeti.SuzukiLieIndex.carrierEquivPinned_steinberg`: the equivalence intertwines the carrier
  Steinberg map of a Suzuki index with the independently defined pinned one;
  `TauCeti.RankTwoBLieIndex.carrierEquivPinned_frobenius` and
  `TauCeti.SuzukiLieIndex.carrierEquivPinned_halfFrobenius` do the same for the two maps it is
  assembled from.
* `TauCeti.RankTwoBLieIndex.symplecticRootIndex_of_isLongSimpleRoot` and
  `TauCeti.RankTwoBLieIndex.symplecticRootIndex_of_not_isLongSimpleRoot`: the long simple root of
  `B₂` is the long root of the symplectic group and the short one its short root.
* `TauCeti.SuzukiLieIndex.pinnedHalfFrobenius_pinnedHalfFrobenius` and
  `TauCeti.SuzukiLieIndex.pinnedHalfFrobenius_pinnedSimpleRootSubgroup`: the pinned special isogeny
  squares to the pinned prime-field Frobenius and exchanges the two numbered simple root subgroups
  with the exponents the length convention fixes.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates II and III, for the numbering
  of the two rank-two diagrams the node adapter moves between.

The organization of the comparison follows the type-`A` one in
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

namespace TauCeti.SuzukiLieIndex

variable (d : SuzukiLieIndex)

/-! ## The special isogeny and the Steinberg map on the symplectic side -/

/-- **The special isogeny of `Sp₄` in characteristic two**, read on the standard symplectic matrix
group. It is the matrix of `2 × 2` minors on the four form-free index pairs, and is built from the
symplectic group alone. -/
noncomputable def symplecticHalfFrobenius :
    d.toRankTwoBLieIndex.StandardGroup →* d.toRankTwoBLieIndex.StandardGroup :=
  TauCeti.specialIsogeny

/-- **The Steinberg map of a Suzuki index on the standard symplectic matrix group**: the odd power
`τ ^ (2m+1)` of the special isogeny, for `2m+1` the field exponent the index records. -/
noncomputable def symplecticSteinberg :
    d.toRankTwoBLieIndex.StandardGroup →* d.toRankTwoBLieIndex.StandardGroup :=
  HPow.hPow (α := Monoid.End d.toRankTwoBLieIndex.StandardGroup) d.symplecticHalfFrobenius
    d.1.fieldExponent

/-- The special isogeny on the pinned symplectic scheme points. -/
noncomputable def pinnedHalfFrobenius :
    d.toRankTwoBLieIndex.PinnedGroup →* d.toRankTwoBLieIndex.PinnedGroup :=
  d.toRankTwoBLieIndex.pinnedEquivSymplectic.symm.toMonoidHom.comp
    (d.symplecticHalfFrobenius.comp d.toRankTwoBLieIndex.pinnedEquivSymplectic.toMonoidHom)

/-- **The independently defined Steinberg map on the pinned symplectic scheme points**: the odd
power `τ ^ (2m+1)` of the pinned special isogeny. -/
noncomputable def pinnedSteinberg :
    d.toRankTwoBLieIndex.PinnedGroup →* d.toRankTwoBLieIndex.PinnedGroup :=
  HPow.hPow (α := Monoid.End d.toRankTwoBLieIndex.PinnedGroup) d.pinnedHalfFrobenius
    d.1.fieldExponent

/-- The canonical matrix realization intertwines the pinned and matrix special isogenies. -/
@[simp]
theorem pinnedEquivSymplectic_pinnedHalfFrobenius (g : d.toRankTwoBLieIndex.PinnedGroup) :
    d.toRankTwoBLieIndex.pinnedEquivSymplectic (d.pinnedHalfFrobenius g) =
      d.symplecticHalfFrobenius (d.toRankTwoBLieIndex.pinnedEquivSymplectic g) := by
  rw [pinnedHalfFrobenius, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rfl

/-- The canonical matrix realization intertwines the pinned and matrix Steinberg maps. -/
@[simp]
theorem pinnedEquivSymplectic_pinnedSteinberg (g : d.toRankTwoBLieIndex.PinnedGroup) :
    d.toRankTwoBLieIndex.pinnedEquivSymplectic (d.pinnedSteinberg g) =
      d.symplecticSteinberg (d.toRankTwoBLieIndex.pinnedEquivSymplectic g) := by
  have hpinned : ⇑d.pinnedSteinberg = (⇑d.pinnedHalfFrobenius)^[d.1.fieldExponent] :=
    Monoid.End.coe_pow (M := d.toRankTwoBLieIndex.PinnedGroup) d.pinnedHalfFrobenius
      d.1.fieldExponent
  have hstandard : ⇑d.symplecticSteinberg = (⇑d.symplecticHalfFrobenius)^[d.1.fieldExponent] :=
    Monoid.End.coe_pow (M := d.toRankTwoBLieIndex.StandardGroup) d.symplecticHalfFrobenius
      d.1.fieldExponent
  have hsemi : Function.Semiconj d.toRankTwoBLieIndex.pinnedEquivSymplectic d.pinnedHalfFrobenius
      d.symplecticHalfFrobenius := d.pinnedEquivSymplectic_pinnedHalfFrobenius
  have hiter := hsemi.iterate_right d.1.fieldExponent g
  rwa [← hpinned, ← hstandard] at hiter

/-! ## The comparison on a Suzuki index -/

/-- **The carrier equivalence intertwines the two special isogenies.** -/
@[simp]
theorem carrierEquivSymplectic_halfFrobenius (g : d.toRankTwoBLieIndex.AmbientGroup) :
    d.toRankTwoBLieIndex.carrierEquivSymplectic (d.halfFrobenius g) =
      d.symplecticHalfFrobenius (d.toRankTwoBLieIndex.carrierEquivSymplectic g) := by
  rw [RankTwoBLieIndex.carrierEquivSymplectic, halfFrobenius_def, symplecticHalfFrobenius,
    SpStd.pointsMulEquivGLSymplecticFin_specialIsogeny]

/-- **The carrier equivalence intertwines the two Steinberg maps.** Both sides are the same odd
power of their own special isogeny. -/
@[simp]
theorem carrierEquivSymplectic_steinberg (g : d.toRankTwoBLieIndex.AmbientGroup) :
    d.toRankTwoBLieIndex.carrierEquivSymplectic (d.steinberg g) =
      d.symplecticSteinberg (d.toRankTwoBLieIndex.carrierEquivSymplectic g) := by
  have hcarrier : ⇑d.steinberg = (⇑d.halfFrobenius)^[d.1.fieldExponent] := by
    rw [steinberg_def]
    exact Monoid.End.coe_pow (M := d.toRankTwoBLieIndex.AmbientGroup) d.halfFrobenius
      d.1.fieldExponent
  have hstandard : ⇑d.symplecticSteinberg = (⇑d.symplecticHalfFrobenius)^[d.1.fieldExponent] :=
    Monoid.End.coe_pow (M := d.toRankTwoBLieIndex.StandardGroup) d.symplecticHalfFrobenius
      d.1.fieldExponent
  have hsemi : Function.Semiconj d.toRankTwoBLieIndex.carrierEquivSymplectic d.halfFrobenius
      d.symplecticHalfFrobenius := d.carrierEquivSymplectic_halfFrobenius
  have hiter := hsemi.iterate_right d.1.fieldExponent g
  rwa [← hcarrier, ← hstandard] at hiter

/-- The carrier-to-pinned equivalence intertwines the two special isogenies. -/
@[simp]
theorem carrierEquivPinned_halfFrobenius (g : d.toRankTwoBLieIndex.AmbientGroup) :
    d.toRankTwoBLieIndex.carrierEquivPinned (d.halfFrobenius g) =
      d.pinnedHalfFrobenius (d.toRankTwoBLieIndex.carrierEquivPinned g) := by
  apply d.toRankTwoBLieIndex.pinnedEquivSymplectic.injective
  rw [RankTwoBLieIndex.pinnedEquivSymplectic_carrierEquivPinned,
    carrierEquivSymplectic_halfFrobenius, pinnedEquivSymplectic_pinnedHalfFrobenius,
    RankTwoBLieIndex.pinnedEquivSymplectic_carrierEquivPinned]

/-- **The explicit carrier's Steinberg map agrees with the independently defined Steinberg map on
the pinned symplectic scheme points.** -/
@[simp]
theorem carrierEquivPinned_steinberg (g : d.toRankTwoBLieIndex.AmbientGroup) :
    d.toRankTwoBLieIndex.carrierEquivPinned (d.steinberg g) =
      d.pinnedSteinberg (d.toRankTwoBLieIndex.carrierEquivPinned g) := by
  apply d.toRankTwoBLieIndex.pinnedEquivSymplectic.injective
  rw [RankTwoBLieIndex.pinnedEquivSymplectic_carrierEquivPinned, carrierEquivSymplectic_steinberg,
    pinnedEquivSymplectic_pinnedSteinberg,
    RankTwoBLieIndex.pinnedEquivSymplectic_carrierEquivPinned]

/-! ## The pinned half-Frobenius is a half-Frobenius -/

/-- **The square of the special isogeny on the standard symplectic matrix group is the prime-field
Frobenius**, that is `τ ^ 2 = Frob_p` at the defining characteristic `p = 2`. -/
@[simp]
theorem symplecticHalfFrobenius_symplecticHalfFrobenius (g : d.toRankTwoBLieIndex.StandardGroup) :
    d.symplecticHalfFrobenius (d.symplecticHalfFrobenius g) =
      d.toRankTwoBLieIndex.symplecticPrimeFrobenius g := by
  -- The matrix square relation is stated at the literal `2` and this one at the index's
  -- characteristic; identifying the two is the step that descends to matrix entries, the
  -- characteristic not being rewritable at the exponent of `iterateFrobenius`, whose instances
  -- depend on it.
  have hchar : d.1.characteristic = 2 := d.characteristic_eq_two
  rw [symplecticHalfFrobenius, TauCeti.specialIsogeny_specialIsogeny,
    RankTwoBLieIndex.symplecticPrimeFrobenius]
  apply Subtype.ext
  apply Units.ext
  rw [GLSymplecticFin.coe_map, GLSymplecticFin.coe_map]
  ext a b
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply,
    iterateFrobenius_def, frobenius_def]
  congr 1
  rw [pow_one, hchar]

/-- **The square of the special isogeny on the pinned symplectic scheme points is the prime-field
Frobenius.** Together with the simple-root equation below this is what makes the pinned map a
half-Frobenius in the sense the Suzuki family's Steinberg map is built from. -/
@[simp]
theorem pinnedHalfFrobenius_pinnedHalfFrobenius (g : d.toRankTwoBLieIndex.PinnedGroup) :
    d.pinnedHalfFrobenius (d.pinnedHalfFrobenius g) =
      d.toRankTwoBLieIndex.pinnedPrimeFrobenius g := by
  apply d.toRankTwoBLieIndex.pinnedEquivSymplectic.injective
  rw [pinnedEquivSymplectic_pinnedHalfFrobenius, pinnedEquivSymplectic_pinnedHalfFrobenius,
    RankTwoBLieIndex.pinnedEquivSymplectic_pinnedPrimeFrobenius,
    symplecticHalfFrobenius_symplecticHalfFrobenius]

/-- **The special isogeny exchanges the two numbered simple root subgroups of the standard
symplectic matrix group**, raising the parameter to the index's exponent at that root, which is one
at the long simple root and the defining characteristic at the short one. -/
@[simp]
theorem symplecticHalfFrobenius_symplecticSimpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.symplecticHalfFrobenius (d.toRankTwoBLieIndex.symplecticSimpleRootSubgroup i u) =
      d.toRankTwoBLieIndex.symplecticSimpleRootSubgroup
          (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i)
        (Multiplicative.ofAdd
          (Multiplicative.toAdd u ^ SuzukiReeIndex.exponent d.toSuzukiReeIndex i)) := by
  rw [← RankTwoBLieIndex.carrierEquivSymplectic_simpleRootSubgroup,
    ← carrierEquivSymplectic_halfFrobenius, halfFrobenius_simpleRootSubgroup,
    RankTwoBLieIndex.carrierEquivSymplectic_simpleRootSubgroup]

/-- **The special isogeny exchanges the two numbered simple root subgroups of the pinned symplectic
scheme points**, with the same exponents. -/
@[simp]
theorem pinnedHalfFrobenius_pinnedSimpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.pinnedHalfFrobenius (d.toRankTwoBLieIndex.pinnedSimpleRootSubgroup i u) =
      d.toRankTwoBLieIndex.pinnedSimpleRootSubgroup
          (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i)
        (Multiplicative.ofAdd
          (Multiplicative.toAdd u ^ SuzukiReeIndex.exponent d.toSuzukiReeIndex i)) := by
  apply d.toRankTwoBLieIndex.pinnedEquivSymplectic.injective
  rw [pinnedEquivSymplectic_pinnedHalfFrobenius,
    RankTwoBLieIndex.pinnedEquivSymplectic_pinnedSimpleRootSubgroup,
    RankTwoBLieIndex.pinnedEquivSymplectic_pinnedSimpleRootSubgroup,
    symplecticHalfFrobenius_symplecticSimpleRootSubgroup]

end TauCeti.SuzukiLieIndex
