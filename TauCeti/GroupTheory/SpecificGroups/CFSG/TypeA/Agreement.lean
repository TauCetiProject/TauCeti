/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Equivalence
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Basic

/-!
# The type-A carrier in the standard special linear model

The type-A families are constructed on the explicit full-weight carrier. Their pinned reference
group is the group of algebraic-closure-valued points of the special linear group scheme over
`ℤ`. This file records the comparison together with all of the pinned data used in the
construction.

For both `A_r(q)` and `²A_r(q)`, `carrierEquivSpecialLinear` is the identity on underlying
matrices. It sends each positive simple-root subgroup to its elementary transvection and
intertwines the carrier Frobenius with entrywise Frobenius. On the twisted family it also
intertwines the carrier graph automorphism with signed reverse inverse transpose. Thus the
carrier Steinberg map agrees with the independently defined pinned scheme-point composite.

## Main declarations

* `TauCeti.TypeALieIndex.StandardGroup`: the standard `SL_{r+1}` matrix group over the index's
  algebraic closure.
* `TauCeti.TypeALieIndex.PinnedGroup` and
  `TauCeti.TypeALieIndex.pinnedEquivSpecialLinear`: the algebraic-closure-valued points of the
  pinned `SL_{r+1}/ℤ` group scheme and their canonical matrix realization.
* `TauCeti.TypeALieIndex.carrierEquivSpecialLinear`: the equivalence from the explicit carrier.
* `TauCeti.TypeALieIndex.specialLinearFrobenius`,
  `TauCeti.TypeALieIndex.specialLinearGraphAut`, and
  `TauCeti.TypeALieIndex.specialLinearSteinberg`: the standard matrix maps.
* `TauCeti.TypeALieIndex.specialLinearGraphAut_ofA` and
  `TauCeti.TypeALieIndex.specialLinearGraphAut_ofTwistedA`: the graph-factor branch equations.
* `TauCeti.TypeALieIndex.pinnedSimpleRootSubgroup`, `TauCeti.TypeALieIndex.pinnedFrobenius`,
  `TauCeti.TypeALieIndex.pinnedGraphAut`, and `TauCeti.TypeALieIndex.pinnedSteinberg`: the pinning
  and Steinberg data on the pinned scheme points.
* `TauCeti.TypeALieIndex.carrierEquivSpecialLinear_simpleRootSubgroup`: agreement of the pinning.
* `TauCeti.TypeALieIndex.carrierEquivSpecialLinear_steinberg`: agreement of the Steinberg maps.
* `TauCeti.TypeALieIndex.carrierEquivPinned`,
  `TauCeti.TypeALieIndex.carrierEquivPinned_simpleRootSubgroup`, and
  `TauCeti.TypeALieIndex.carrierEquivPinned_steinberg`: the corresponding comparison with the
  pinned scheme points.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Chapters 2 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.TypeALieIndex

/-- The standard special linear matrix group corresponding to a validated type-A index. -/
noncomputable abbrev StandardGroup (d : TypeALieIndex) :=
  Matrix.SpecialLinearGroup (Fin (d.1.rank + 1)) d.1.Closure

/-- The algebraic-closure-valued points of the pinned special linear group scheme over `ℤ`. -/
noncomputable abbrev PinnedGroup (d : TypeALieIndex) :=
  ((Spec (CommRingCat.of d.1.Closure)).asOver (Spec (CommRingCat.of ℤ)) ⟶
    (SpecialLinear.groupScheme ℤ (d.1.rank + 1)).X)

/-- The canonical matrix realization of the pinned special linear scheme points. -/
noncomputable def pinnedEquivSpecialLinear (d : TypeALieIndex) :
    d.PinnedGroup ≃* d.StandardGroup :=
  SpecialLinear.schemePointsMulEquiv (R := ℤ) (d.1.rank + 1) d.1.Closure

/-- **The explicit type-A carrier is equivalent to the standard special linear matrix group.**
The equivalence preserves the underlying matrix. -/
noncomputable def carrierEquivSpecialLinear (d : TypeALieIndex) :
    d.AmbientGroup ≃* d.StandardGroup :=
  SlStd.specialLinearMulEquiv d.1.rank

/-- **The explicit type-A carrier is equivalent to the points of the pinned `SL_{r+1}/ℤ`
group scheme.** -/
noncomputable def carrierEquivPinned (d : TypeALieIndex) :
    d.AmbientGroup ≃* d.PinnedGroup :=
  d.carrierEquivSpecialLinear.trans d.pinnedEquivSpecialLinear.symm

/-- Entrywise `q`-power Frobenius on the standard special linear matrix group. -/
noncomputable def specialLinearFrobenius (d : TypeALieIndex) :
    d.StandardGroup →* d.StandardGroup :=
  Matrix.SpecialLinearGroup.map
    (iterateFrobenius d.1.Closure d.1.characteristic d.1.fieldExponent)

/-- The graph factor on the standard special linear matrix group: the identity for `A_r(q)` and
signed reverse inverse transpose for `²A_r(q)`. -/
noncomputable def specialLinearGraphAut (d : TypeALieIndex) : MulAut d.StandardGroup :=
  match h : d.1.1 with
  | .A _ _ => 1
  | .twistedA _ _ =>
      Matrix.SpecialLinearGroup.typeAGraphAutomorphism d.1.rank d.1.Closure
  | .B _ _ | .C _ _ | .D _ _ | .twistedD _ _ | .E6 _ | .E7 _ | .E8 _ | .F4 _ | .G2 _
  | .twistedE6 _ | .trialityD4 _ | .suzuki _ | .reeG2 _ | .reeF4 _ | .tits =>
      absurd d.2 (by rw [LieTypeIndex.isTypeA_iff, h]; exact not_false)

/-- On `A_r(q)`, the standard special-linear graph factor is trivial. -/
theorem specialLinearGraphAut_ofA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.A rank q).Valid) :
    (ofA rank q hvalid).specialLinearGraphAut = 1 := by
  simp only [specialLinearGraphAut]

/-- On `²A_r(q)`, the standard special-linear graph factor is signed reverse inverse
transpose. -/
theorem specialLinearGraphAut_ofTwistedA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.twistedA rank q).Valid) :
    (ofTwistedA rank q hvalid).specialLinearGraphAut =
      Matrix.SpecialLinearGroup.typeAGraphAutomorphism
        (ofTwistedA rank q hvalid).1.rank (ofTwistedA rank q hvalid).1.Closure := by
  simp only [specialLinearGraphAut]

/-- **The standard matrix Steinberg map**: the graph factor composed with entrywise `q`-power
Frobenius. -/
noncomputable def specialLinearSteinberg (d : TypeALieIndex) :
    d.StandardGroup →* d.StandardGroup :=
  d.specialLinearGraphAut.toMonoidHom.comp d.specialLinearFrobenius

/-- The positive simple-root subgroup of the pinned special linear group scheme. -/
noncomputable def pinnedSimpleRootSubgroup (d : TypeALieIndex) (i : Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.PinnedGroup :=
  { toFun := fun u =>
      (AdditiveGroup.schemePointsMulEquiv d.1.Closure).symm u ≫
        (SpecialLinear.rootSubgroup
          (R := ℤ) (SlStd.rootTarget_ne_rootSource d.1.rank (.inl i))).hom.hom
    map_one' := by simp
    map_mul' := by
      intro u v
      rw [map_mul]
      apply MonObj.mul_comp }

/-- Entrywise `q`-power Frobenius on the pinned special linear scheme points. This is defined from
the canonical matrix realization, independently of the explicit carrier. -/
noncomputable def pinnedFrobenius (d : TypeALieIndex) :
    d.PinnedGroup →* d.PinnedGroup :=
  d.pinnedEquivSpecialLinear.symm.toMonoidHom.comp
    (d.specialLinearFrobenius.comp d.pinnedEquivSpecialLinear.toMonoidHom)

/-- The graph factor on the pinned special linear scheme points, defined through their canonical
matrix realization. -/
noncomputable def pinnedGraphAut (d : TypeALieIndex) : MulAut d.PinnedGroup :=
  (d.pinnedEquivSpecialLinear.trans d.specialLinearGraphAut).trans
    d.pinnedEquivSpecialLinear.symm

/-- **The independently defined Steinberg map on the pinned special linear scheme points.** It is
the pinned graph factor composed with entrywise Frobenius. -/
noncomputable def pinnedSteinberg (d : TypeALieIndex) :
    d.PinnedGroup →* d.PinnedGroup :=
  d.pinnedGraphAut.toMonoidHom.comp d.pinnedFrobenius

/-- Under the canonical matrix realization, a pinned simple-root element is its elementary
transvection. -/
@[simp]
theorem pinnedEquivSpecialLinear_pinnedSimpleRootSubgroup (d : TypeALieIndex)
    (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.pinnedEquivSpecialLinear (d.pinnedSimpleRootSubgroup i u) =
      Matrix.SpecialLinearGroup.transvection
        (SlStd.rootTarget_ne_rootSource d.1.rank (.inl i))
        (Multiplicative.toAdd u) := by
  -- Expose the `toFun` of the bundled `pinnedSimpleRootSubgroup` homomorphism so that the
  -- scheme-point root-subgroup equation can recognize the displayed composition.
  change SpecialLinear.schemePointsMulEquiv (d.1.rank + 1) d.1.Closure
      ((AdditiveGroup.schemePointsMulEquiv d.1.Closure).symm u ≫
        (SpecialLinear.rootSubgroup
          (R := ℤ) (SlStd.rootTarget_ne_rootSource d.1.rank (.inl i))).hom.hom) = _
  rw [SpecialLinear.schemePointsMulEquiv_rootSubgroup, MulEquiv.apply_symm_apply]

/-- The canonical matrix realization intertwines pinned and matrix Frobenius. -/
@[simp]
theorem pinnedEquivSpecialLinear_pinnedFrobenius (d : TypeALieIndex) (g : d.PinnedGroup) :
    d.pinnedEquivSpecialLinear (d.pinnedFrobenius g) =
      d.specialLinearFrobenius (d.pinnedEquivSpecialLinear g) := by
  rw [pinnedFrobenius, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rfl

/-- The canonical matrix realization intertwines the pinned and matrix graph factors. -/
@[simp]
theorem pinnedEquivSpecialLinear_pinnedGraphAut (d : TypeALieIndex) (g : d.PinnedGroup) :
    d.pinnedEquivSpecialLinear (d.pinnedGraphAut g) =
      d.specialLinearGraphAut (d.pinnedEquivSpecialLinear g) := by
  rw [pinnedGraphAut, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]

/-- The canonical matrix realization intertwines the pinned and matrix Steinberg maps. -/
@[simp]
theorem pinnedEquivSpecialLinear_pinnedSteinberg (d : TypeALieIndex) (g : d.PinnedGroup) :
    d.pinnedEquivSpecialLinear (d.pinnedSteinberg g) =
      d.specialLinearSteinberg (d.pinnedEquivSpecialLinear g) := by
  rw [pinnedSteinberg, MonoidHom.comp_apply,
    specialLinearSteinberg, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, pinnedEquivSpecialLinear_pinnedGraphAut,
    pinnedEquivSpecialLinear_pinnedFrobenius]
  rfl

/-- **The carrier equivalence identifies each positive simple-root subgroup with its elementary
transvection in the standard special linear group.** -/
@[simp]
theorem carrierEquivSpecialLinear_simpleRootSubgroup (d : TypeALieIndex)
    (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.carrierEquivSpecialLinear (d.simpleRootSubgroup i u) =
      Matrix.SpecialLinearGroup.transvection
        (SlStd.rootTarget_ne_rootSource d.1.rank (.inl i))
        (Multiplicative.toAdd u) := by
  rw [carrierEquivSpecialLinear, simpleRootSubgroup_def,
    SlStd.specialLinearMulEquiv_rootSubgroupPoints]

/-- **The carrier-to-pinned equivalence matches the positive simple-root subgroups.** -/
@[simp]
theorem carrierEquivPinned_simpleRootSubgroup (d : TypeALieIndex)
    (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.carrierEquivPinned (d.simpleRootSubgroup i u) =
      d.pinnedSimpleRootSubgroup i u := by
  apply d.pinnedEquivSpecialLinear.injective
  rw [carrierEquivPinned, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    carrierEquivSpecialLinear_simpleRootSubgroup,
    pinnedEquivSpecialLinear_pinnedSimpleRootSubgroup]

/-- **The carrier equivalence intertwines the two entrywise Frobenius maps.** -/
@[simp]
theorem carrierEquivSpecialLinear_frobenius (d : TypeALieIndex)
    (g : d.AmbientGroup) :
    d.carrierEquivSpecialLinear (d.frobenius g) =
      d.specialLinearFrobenius (d.carrierEquivSpecialLinear g) := by
  rw [frobenius_def, carrierEquivSpecialLinear, specialLinearFrobenius,
    SlStd.specialLinearMulEquiv_frobenius]

/-- The carrier-to-pinned equivalence intertwines the Frobenius factors. -/
@[simp]
theorem carrierEquivPinned_frobenius (d : TypeALieIndex) (g : d.AmbientGroup) :
    d.carrierEquivPinned (d.frobenius g) =
      d.pinnedFrobenius (d.carrierEquivPinned g) := by
  apply d.pinnedEquivSpecialLinear.injective
  rw [carrierEquivPinned, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    pinnedFrobenius, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    carrierEquivSpecialLinear_frobenius]
  rw [MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

/-- **The carrier equivalence intertwines the two graph factors.** This is trivial on `A_r(q)`
and compares the two signed reverse-inverse-transpose maps on `²A_r(q)`. -/
@[simp]
theorem carrierEquivSpecialLinear_graphAut (d : TypeALieIndex)
    (g : d.AmbientGroup) :
    d.carrierEquivSpecialLinear (d.graphAut g) =
      d.specialLinearGraphAut (d.carrierEquivSpecialLinear g) := by
  rcases d.exists_eq_ofA_or_exists_eq_ofTwistedA with
    ⟨rank, q, hvalid, rfl⟩ | ⟨rank, q, hvalid, rfl⟩
  · rw [graphAut_ofA, carrierEquivSpecialLinear, specialLinearGraphAut_ofA,
      MulAut.one_apply, MulAut.one_apply]
  · rw [graphAut_ofTwistedA, carrierEquivSpecialLinear, specialLinearGraphAut_ofTwistedA,
      SlStd.specialLinearMulEquiv_graphAutomorphismPoints]

/-- The carrier-to-pinned equivalence intertwines the graph factors. -/
@[simp]
theorem carrierEquivPinned_graphAut (d : TypeALieIndex) (g : d.AmbientGroup) :
    d.carrierEquivPinned (d.graphAut g) =
      d.pinnedGraphAut (d.carrierEquivPinned g) := by
  apply d.pinnedEquivSpecialLinear.injective
  rw [carrierEquivPinned, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    pinnedGraphAut, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, carrierEquivSpecialLinear_graphAut]
  rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

/-- **The carrier Steinberg map agrees with the standard matrix Steinberg map.** This covers
entrywise Frobenius on `A_r(q)` and signed reverse inverse transpose after Frobenius on
`²A_r(q)`. -/
@[simp]
theorem carrierEquivSpecialLinear_steinberg (d : TypeALieIndex)
    (g : d.AmbientGroup) :
    d.carrierEquivSpecialLinear (d.steinberg g) =
      d.specialLinearSteinberg (d.carrierEquivSpecialLinear g) := by
  rw [steinberg_eq_graphAut_comp_frobenius, MonoidHom.comp_apply,
    specialLinearSteinberg, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom,
    carrierEquivSpecialLinear_graphAut, carrierEquivSpecialLinear_frobenius]
  rfl

/-- **The explicit carrier Steinberg map agrees with the independently defined Steinberg map on
the pinned special linear scheme points.** -/
@[simp]
theorem carrierEquivPinned_steinberg (d : TypeALieIndex) (g : d.AmbientGroup) :
    d.carrierEquivPinned (d.steinberg g) =
      d.pinnedSteinberg (d.carrierEquivPinned g) := by
  rw [steinberg_eq_graphAut_comp_frobenius, MonoidHom.comp_apply,
    pinnedSteinberg, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, carrierEquivPinned_graphAut,
    carrierEquivPinned_frobenius]
  rfl

end TauCeti.TypeALieIndex
