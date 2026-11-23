/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.AbelianLayer
public import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.Existence

import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormLimitation

/-!
# The global class-field correspondence

For a number field `K`, global existence and uniqueness identify the open finite-index subgroups
of the idele class group `C_K` with the finite abelian layers of its absolute Galois group.
`globalClassFieldCorrespondence` is this order isomorphism. Applying `classField` to its values
puts the corresponding extensions inside the separable closure and reverses inclusions.

The quotient isomorphism `globalClassFieldGaloisEquiv` is the existing reciprocity isomorphism
of the attached abelian layer, not a separately chosen isomorphism. Its value on an idele class
is the Artin symbol, and the index of the prescribed subgroup is the degree of the extension.

The construction follows the local counterpart in
`TauCeti/NumberTheory/ClassFieldTheory/LocalExistence/Correspondence.lean`, using global
existence and the idele-class norm subgroups in place of local existence and field-unit norms.

## Main definitions

* `TauCeti.ClassFieldTheory.GlobalNormSubgroups`: open finite-index subgroups of `C_K`.
* `TauCeti.ClassFieldTheory.globalClassField`: the unique abelian layer with a prescribed norm
  subgroup.
* `TauCeti.ClassFieldTheory.globalClassFieldCorrespondence`: the subgroup order isomorphism.
* `TauCeti.ClassFieldTheory.globalClassFieldGaloisEquiv`: reciprocity for the attached class field.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Theorem 9.5.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §6.
-/

public noncomputable section

open NumberField

namespace TauCeti.ClassFieldTheory

open NormalLayer

variable {K : Type} [Field K] [NumberField K]

/-- The source of the global class-field correspondence: open finite-index subgroups of the
idele class group of a number field. -/
abbrev GlobalNormSubgroups (K : Type) [Field K] [NumberField K] : Type :=
  {N : OpenSubgroup (IdeleClassGroup (𝓞 K) K) // N.toSubgroup.FiniteIndex}

/-- The norm subgroup of a finite global layer, bundled as an open finite-index subgroup. -/
def globalNormOpenSubgroup (K : Type) [Field K] [NumberField K]
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) : GlobalNormSubgroups K :=
  ⟨⟨globalNormSubgroup K V, isOpen_globalNormSubgroup K V⟩,
    finiteIndex_globalNormSubgroup K V⟩

/-- The subgroup underlying `globalNormOpenSubgroup` is the norm subgroup of the layer. -/
@[simp]
theorem globalNormOpenSubgroup_toSubgroup
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    (globalNormOpenSubgroup K V).val.toSubgroup = globalNormSubgroup K V :=
  (rfl)

/-- **The global class field attached to `N`.** This is the unique finite abelian layer with
norm subgroup `N`; its fixed field in the separable closure is
`classField K (globalClassField N).1`. -/
def globalClassField (N : GlobalNormSubgroups K) : AbelianLayer (AbsoluteGaloisGroup K) :=
  let _ := N.property
  let h := globalAbelianExistence N.val.isOpen
  ⟨h.choose, h.choose_spec.1⟩

/-- The attached global class field has the prescribed norm subgroup. -/
@[simp]
theorem globalClassField_normSubgroup (N : GlobalNormSubgroups K) :
    globalNormSubgroup K (globalClassField N).val = N.val.toSubgroup := by
  let _ := N.property
  exact (globalAbelianExistence N.val.isOpen).choose_spec.2

/-- The attached layer is characterized by its norm subgroup among finite abelian layers. -/
@[simp]
theorem globalClassField_eq_iff (N : GlobalNormSubgroups K)
    (V : AbelianLayer (AbsoluteGaloisGroup K)) :
    globalClassField N = V ↔ globalNormSubgroup K V.val = N.val.toSubgroup := by
  constructor
  · rintro rfl
    exact globalClassField_normSubgroup N
  · intro h
    apply Subtype.ext
    exact globalClassField_unique (globalClassField N).property V.property
      ((globalClassField_normSubgroup N).trans h.symm)

/-- Subgroup inclusions in the global class-field correspondence are preserved. -/
theorem globalClassField_le_iff (N₁ N₂ : GlobalNormSubgroups K) :
    N₁ ≤ N₂ ↔ (globalClassField N₁).val ≤ (globalClassField N₂).val := by
  rw [← globalNormSubgroup_le_iff_of_isAbelian (globalClassField N₂).property,
    globalClassField_normSubgroup, globalClassField_normSubgroup]
  -- Both the subtype order and the open-subgroup order are inherited from subgroup inclusion.
  rfl

/-- On fixed fields inside the separable closure, the global correspondence reverses inclusions.
-/
theorem globalClassField_orderReversing (N₁ N₂ : GlobalNormSubgroups K) :
    N₁ ≤ N₂ ↔
      classField K (globalClassField N₂).val ≤ classField K (globalClassField N₁).val :=
  (globalClassField_le_iff N₁ N₂).trans
    (classField_le_classField_iff K (globalClassField N₁).val (globalClassField N₂).val).symm

/-- **The global class-field correspondence.** Open finite-index subgroups of `C_K` correspond
order preservingly to finite abelian layers of `G_K`, and hence order reversingly to their fixed
fields. -/
def globalClassFieldCorrespondence :
    GlobalNormSubgroups K ≃o AbelianLayer (AbsoluteGaloisGroup K) where
  toFun := globalClassField
  invFun V := globalNormOpenSubgroup K V.val
  left_inv N := by
    apply Subtype.ext
    exact OpenSubgroup.toSubgroup_injective (globalClassField_normSubgroup N)
  right_inv V := by
    apply (globalClassField_eq_iff _ V).2
    exact (globalNormOpenSubgroup_toSubgroup V.val).symm
  map_rel_iff' := fun {N₁ N₂} ↦ (globalClassField_le_iff N₁ N₂).symm

/-- The global correspondence sends a subgroup to its attached class field. -/
@[simp]
theorem globalClassFieldCorrespondence_apply (N : GlobalNormSubgroups K) :
    globalClassFieldCorrespondence N = globalClassField N :=
  (rfl)

/-- The inverse global correspondence sends an abelian layer to its norm subgroup. -/
@[simp]
theorem globalClassFieldCorrespondence_symm_apply
    (V : AbelianLayer (AbsoluteGaloisGroup K)) :
    globalClassFieldCorrespondence.symm V = globalNormOpenSubgroup K V.val :=
  (rfl)

/-- The quotient `C_K / N` is canonically the Galois group of the attached abelian layer. -/
def globalClassFieldGaloisEquiv (N : GlobalNormSubgroups K) :
    IdeleClassGroup (𝓞 K) K ⧸ N.val.toSubgroup ≃* (ofOpenNormal (globalClassField N).val).Gal :=
  (QuotientGroup.quotientMulEquivOfEq (globalClassField_normSubgroup N).symm).trans
    (globalAbelianGaloisEquiv K (globalClassField N).property)

/-- The quotient isomorphism sends the class of an idele class to its Artin symbol. -/
@[simp]
theorem globalClassFieldGaloisEquiv_mk (N : GlobalNormSubgroups K)
    (c : IdeleClassGroup (𝓞 K) K) :
    globalClassFieldGaloisEquiv N (QuotientGroup.mk c) =
      globalAbelianArtinHom K (globalClassField N).property c := by
  rw [globalClassFieldGaloisEquiv, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk, globalAbelianGaloisEquiv_mk]

/-- The index of `N` is the degree of its global class field. -/
theorem globalClassField_index (N : GlobalNormSubgroups K) :
    N.val.toSubgroup.index = (ofOpenNormal (globalClassField N).val).degree := by
  rw [← index_globalNormSubgroup (globalClassField N).property, globalClassField_normSubgroup]

end TauCeti.ClassFieldTheory
