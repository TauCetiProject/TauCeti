/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Equivalence
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Basic

/-!
# The type-C carrier in the standard symplectic model

The type-`C` finite-group candidates are constructed on the explicit full-weight standard carrier.
Their pinned reference group is the group of algebraic-closure-valued points of the symplectic
group scheme over `ℤ`. This file identifies the two point groups and records that the
identification respects all data used by the finite-group construction.

The comparison is the identity on underlying matrices. It carries each positive simple-root
subgroup to the corresponding root subgroup of the symplectic group scheme and intertwines the
carrier's entrywise Frobenius with the independently defined entrywise Frobenius on pinned scheme
points. Since type `C` is untwisted, this also intertwines the two Steinberg endomorphisms.

The interface and proof organization follow the type-`A` carrier comparison developed in
[TauCetiProject/TauCeti#7837](https://github.com/TauCetiProject/TauCeti/pull/7837), specialized to
the symplectic group and its type-`C` simple roots.

## Main declarations

* `TauCeti.TypeCLieIndex.StandardGroup`: the standard symplectic matrix group.
* `TauCeti.TypeCLieIndex.PinnedGroup` and
  `TauCeti.TypeCLieIndex.pinnedEquivSymplectic`: the points of the pinned symplectic group scheme
  and their canonical matrix realization.
* `TauCeti.TypeCLieIndex.carrierEquivPinned`: the equivalence from the explicit carrier to the
  pinned scheme points.
* `TauCeti.TypeCLieIndex.pinnedSimpleRootSubgroup` and
  `TauCeti.TypeCLieIndex.pinnedSteinberg`: the pinning and Steinberg data on the pinned points.
* `TauCeti.TypeCLieIndex.carrierEquivPinned_simpleRootSubgroup` and
  `TauCeti.TypeCLieIndex.carrierEquivPinned_steinberg`: compatibility of the comparison with the
  pinning and Steinberg map.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Chapters 2 and 11.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.TypeCLieIndex

/-- The standard symplectic matrix group corresponding to a validated type-`C` index. -/
noncomputable abbrev StandardGroup (d : TypeCLieIndex) :=
  GLSymplecticFin (d.carrierRank + 1) d.1.Closure

/-- The algebraic-closure-valued points of the pinned symplectic group scheme over `ℤ`. -/
noncomputable abbrev PinnedGroup (d : TypeCLieIndex) :=
  ((Spec (CommRingCat.of d.1.Closure)).asOver (Spec (CommRingCat.of ℤ)) ⟶
    (Symplectic.groupScheme ℤ (d.carrierRank + 1)).X)

/-- The canonical matrix realization of the pinned symplectic scheme points. -/
noncomputable def pinnedEquivSymplectic (d : TypeCLieIndex) :
    d.PinnedGroup ≃* d.StandardGroup :=
  Symplectic.schemePointsMulEquiv (R := ℤ) (d.carrierRank + 1) d.1.Closure

/-- **The explicit type-`C` carrier is equivalent to the standard symplectic matrix group.**
Both directions preserve the underlying matrix. -/
noncomputable def carrierEquivSymplectic (d : TypeCLieIndex) :
    d.AmbientGroup ≃* d.StandardGroup :=
  SpStd.pointsMulEquivGLSymplecticFin d.carrierRank d.1.Closure

/-- **The explicit type-`C` carrier is equivalent to the points of the pinned symplectic group
scheme.** -/
noncomputable def carrierEquivPinned (d : TypeCLieIndex) :
    d.AmbientGroup ≃* d.PinnedGroup :=
  d.carrierEquivSymplectic.trans d.pinnedEquivSymplectic.symm

/-- The root of the standard symplectic group corresponding to a Bourbaki-numbered simple root of
the validated type-`C` index. -/
def symplecticSimpleRootIndex (d : TypeCLieIndex) (i : Fin d.1.rank) :
    GLSymplecticFin.RootSubgroupIndex (d.carrierRank + 1) :=
  Symplectic.diagonalSimpleRootIndex (d.carrierRank + 1) (d.carrierNode i)

/-- The positive simple-root subgroup of the pinned symplectic group scheme. -/
noncomputable def pinnedSimpleRootSubgroup (d : TypeCLieIndex) (i : Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.PinnedGroup :=
  { toFun := fun u ↦
      (AdditiveGroup.schemePointsMulEquiv d.1.Closure).symm u ≫
        (Symplectic.rootSubgroup (R := ℤ) (d.symplecticSimpleRootIndex i)).hom.hom
    map_one' := by simp
    map_mul' := by
      intro u v
      rw [map_mul]
      apply MonObj.mul_comp }

/-- Entrywise `q`-power Frobenius on the standard symplectic matrix group. -/
noncomputable def symplecticFrobenius (d : TypeCLieIndex) :
    d.StandardGroup →* d.StandardGroup :=
  GLSymplecticFin.map (d.carrierRank + 1) d.1.Closure
    (iterateFrobenius d.1.Closure d.1.characteristic d.1.fieldExponent)

/-- Entrywise `q`-power Frobenius on pinned symplectic scheme points, defined through their
canonical matrix realization and independently of the explicit carrier. -/
noncomputable def pinnedFrobenius (d : TypeCLieIndex) :
    d.PinnedGroup →* d.PinnedGroup :=
  d.pinnedEquivSymplectic.symm.toMonoidHom.comp
    (d.symplecticFrobenius.comp d.pinnedEquivSymplectic.toMonoidHom)

/-- **The Steinberg endomorphism on the pinned symplectic scheme points.** Type `C` is untwisted,
so this is the pinned Frobenius. -/
noncomputable def pinnedSteinberg (d : TypeCLieIndex) :
    d.PinnedGroup →* d.PinnedGroup :=
  d.pinnedFrobenius

/-- The pinned Steinberg endomorphism of type `C` is its `q`-power Frobenius. -/
theorem pinnedSteinberg_eq_frobenius (d : TypeCLieIndex) :
    d.pinnedSteinberg = d.pinnedFrobenius := by
  rw [pinnedSteinberg]

/-- Under the canonical matrix realization, a pinned simple-root element is the corresponding
standard symplectic root element. -/
@[simp]
theorem pinnedEquivSymplectic_pinnedSimpleRootSubgroup (d : TypeCLieIndex)
    (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.pinnedEquivSymplectic (d.pinnedSimpleRootSubgroup i u) =
      (d.symplecticSimpleRootIndex i).hom u := by
  -- Expose the `toFun` of the bundled homomorphism so the scheme-point root-subgroup equation
  -- recognizes the displayed composition.
  change Symplectic.schemePointsMulEquiv (d.carrierRank + 1) d.1.Closure
      ((AdditiveGroup.schemePointsMulEquiv d.1.Closure).symm u ≫
        (Symplectic.rootSubgroup (R := ℤ) (d.symplecticSimpleRootIndex i)).hom.hom) = _
  rw [Symplectic.schemePointsMulEquiv_rootSubgroup, MulEquiv.apply_symm_apply]

/-- The canonical matrix realization intertwines pinned and matrix Frobenius. -/
@[simp]
theorem pinnedEquivSymplectic_pinnedFrobenius (d : TypeCLieIndex) (g : d.PinnedGroup) :
    d.pinnedEquivSymplectic (d.pinnedFrobenius g) =
      d.symplecticFrobenius (d.pinnedEquivSymplectic g) := by
  rw [pinnedFrobenius, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rfl

/-- The canonical matrix realization intertwines the pinned and matrix Steinberg maps. -/
@[simp]
theorem pinnedEquivSymplectic_pinnedSteinberg (d : TypeCLieIndex) (g : d.PinnedGroup) :
    d.pinnedEquivSymplectic (d.pinnedSteinberg g) =
      d.symplecticFrobenius (d.pinnedEquivSymplectic g) := by
  rw [pinnedSteinberg_eq_frobenius, pinnedEquivSymplectic_pinnedFrobenius]

/-- **The carrier equivalence identifies each positive simple-root subgroup with the corresponding
standard symplectic root subgroup.** -/
@[simp]
theorem carrierEquivSymplectic_simpleRootSubgroup (d : TypeCLieIndex)
    (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.carrierEquivSymplectic (d.simpleRootSubgroup i u) =
      (d.symplecticSimpleRootIndex i).hom u := by
  rw [carrierEquivSymplectic, simpleRootSubgroup_def,
    symplecticSimpleRootIndex,
    SpStd.pointsMulEquivGLSymplecticFin_simpleRootSubgroup]

/-- **The carrier-to-pinned equivalence matches every positive simple-root subgroup.** -/
@[simp]
theorem carrierEquivPinned_simpleRootSubgroup (d : TypeCLieIndex)
    (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.carrierEquivPinned (d.simpleRootSubgroup i u) =
      d.pinnedSimpleRootSubgroup i u := by
  apply d.pinnedEquivSymplectic.injective
  rw [carrierEquivPinned, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    carrierEquivSymplectic_simpleRootSubgroup,
    pinnedEquivSymplectic_pinnedSimpleRootSubgroup]

/-- **The carrier equivalence intertwines the two entrywise Frobenius maps.** -/
@[simp]
theorem carrierEquivSymplectic_frobenius (d : TypeCLieIndex) (g : d.AmbientGroup) :
    d.carrierEquivSymplectic (d.frobenius g) =
      d.symplecticFrobenius (d.carrierEquivSymplectic g) := by
  rw [carrierEquivSymplectic, frobenius_def, symplecticFrobenius,
    SpStd.pointsMulEquivGLSymplecticFin_frobenius]

/-- The carrier-to-pinned equivalence intertwines the Frobenius endomorphisms. -/
@[simp]
theorem carrierEquivPinned_frobenius (d : TypeCLieIndex) (g : d.AmbientGroup) :
    d.carrierEquivPinned (d.frobenius g) =
      d.pinnedFrobenius (d.carrierEquivPinned g) := by
  apply d.pinnedEquivSymplectic.injective
  rw [carrierEquivPinned, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    carrierEquivSymplectic_frobenius, pinnedEquivSymplectic_pinnedFrobenius,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

/-- The carrier equivalence intertwines the carrier Steinberg map with standard symplectic
Frobenius. -/
@[simp]
theorem carrierEquivSymplectic_steinberg (d : TypeCLieIndex) (g : d.AmbientGroup) :
    d.carrierEquivSymplectic (d.steinberg g) =
      d.symplecticFrobenius (d.carrierEquivSymplectic g) := by
  rw [steinberg_def, carrierEquivSymplectic_frobenius]

/-- **The explicit carrier Steinberg map agrees with the independently defined Steinberg map on
the pinned symplectic scheme points.** -/
@[simp]
theorem carrierEquivPinned_steinberg (d : TypeCLieIndex) (g : d.AmbientGroup) :
    d.carrierEquivPinned (d.steinberg g) =
      d.pinnedSteinberg (d.carrierEquivPinned g) := by
  rw [steinberg_def, pinnedSteinberg_eq_frobenius, carrierEquivPinned_frobenius]

end TauCeti.TypeCLieIndex
