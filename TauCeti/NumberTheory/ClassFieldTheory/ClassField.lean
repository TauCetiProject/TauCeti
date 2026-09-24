/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.Galois.Infinite
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.AbelianLayer

/-!
# The field cut out by an open normal subgroup of the absolute Galois group

Class field theory states its correspondences on the Galois side, as bijections between norm
subgroups and open normal subgroups `V` of the absolute Galois group
`G_F = Gal(Fˢ/F)`. This file records, once, the dictionary that turns such a subgroup back into a
field: the **class field** `classField F V` is the fixed field of `V` inside the separable closure
`Fˢ`. Because `G_F` is taken at the separable closure, the fixed field of all of `G_F` is `F`
itself, so no transport between closures intervenes.

By the infinite Galois correspondence the dictionary is faithful: the fixing subgroup of
`classField F V` is `V` again, `classField F V` is a finite Galois extension of `F` whose Galois
group is the finite quotient `G_F ⧸ V`, and every finite Galois subextension of `Fˢ` arises this
way. Subgroup inclusion becomes reverse inclusion of fields, which is how an order-preserving
correspondence on subgroups becomes the classical order-reversing correspondence on fields.
Finally `V` is an abelian layer exactly when its class field is an abelian extension.

## Main definitions

* `TauCeti.ClassFieldTheory.classField F V`: the fixed field of `V` in `Fˢ`.
* `TauCeti.ClassFieldTheory.galClassFieldEquiv`: the Galois group of `classField F V` over `F` is
  the Galois group of the finite normal layer `V ◁ G_F`.

## Main results

* `TauCeti.ClassFieldTheory.fixingSubgroup_classField`: the fixing subgroup of the class field of
  `V` is `V`.
* `TauCeti.ClassFieldTheory.classField_le_classField_iff`: `classField F W ≤ classField F V` if
  and only if `V ≤ W`.
* `TauCeti.ClassFieldTheory.exists_classField_eq_iff`: the class fields are exactly the finite
  Galois subextensions of `Fˢ`.
* `TauCeti.ClassFieldTheory.finrank_classField`: the degree of the class field of `V` is the index
  of `V`.
* `TauCeti.ClassFieldTheory.isAbelianGalois_classField_iff`: the class field of `V` is abelian
  over `F` if and only if `V` is an abelian layer.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter IV, §1.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I, §1.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open IntermediateField

section Basic

variable (F : Type*) [Field F]

/-- **The class field of an open normal subgroup** `V` of the absolute Galois group `G_F`: the
fixed field of `V` inside the separable closure of `F`. It is the finite Galois extension of `F`
with Galois group `G_F ⧸ V`. -/
def classField (V : OpenNormalSubgroup (AbsoluteGaloisGroup F)) :
    IntermediateField F (SeparableClosure F) :=
  fixedField V.toSubgroup

variable {F}

/-- An element of `Fˢ` lies in the class field of `V` exactly when every element of `V` fixes
it. -/
@[simp]
theorem mem_classField {V : OpenNormalSubgroup (AbsoluteGaloisGroup F)} {x : SeparableClosure F} :
    x ∈ classField F V ↔ ∀ σ ∈ V, σ x = x :=
  ⟨fun hx σ hσ ↦ hx ⟨σ, hσ⟩, fun hx σ ↦ hx σ σ.2⟩

/-- The fixing subgroup of the class field of `V` is `V`: an open subgroup is closed, so the
infinite Galois correspondence recovers it from its fixed field. -/
@[simp]
theorem fixingSubgroup_classField (V : OpenNormalSubgroup (AbsoluteGaloisGroup F)) :
    (classField F V).fixingSubgroup = V.toSubgroup :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨V.toSubgroup, V.toOpenSubgroup.isClosed⟩

variable (F) in
/-- **The Galois dictionary reverses inclusions**: a larger subgroup cuts out a smaller field.
This turns a class-field correspondence that preserves the order on subgroups into the classical
order-reversing correspondence on fields. -/
theorem classField_le_classField_iff (V W : OpenNormalSubgroup (AbsoluteGaloisGroup F)) :
    classField F W ≤ classField F V ↔ V ≤ W :=
  (le_iff_le V.toSubgroup (classField F W)).trans <| by
    rw [fixingSubgroup_classField]
    exact Iff.rfl

variable (F) in
/-- Distinct open normal subgroups cut out distinct class fields. -/
theorem classField_injective : Function.Injective (classField F) := fun V W h ↦
  le_antisymm ((classField_le_classField_iff F V W).1 h.ge)
    ((classField_le_classField_iff F W V).1 h.le)

/-- The class field of `V` is `F` exactly when `V` is the whole absolute Galois group. -/
@[simp]
theorem classField_eq_bot_iff {V : OpenNormalSubgroup (AbsoluteGaloisGroup F)} :
    classField F V = ⊥ ↔ V.toSubgroup = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← fixingSubgroup_classField, h, fixingSubgroup_bot]
  · rw [classField, h, InfiniteGalois.fixedField_bot]

/-- The class field of `V` is finite over `F`, because `V` is open. -/
instance finiteDimensional_classField (V : OpenNormalSubgroup (AbsoluteGaloisGroup F)) :
    FiniteDimensional F (classField F V) :=
  (InfiniteGalois.isOpen_iff_finite (classField F V)).1
    (by simpa only [fixingSubgroup_classField] using V.isOpen')

/-- The class field of `V` is Galois over `F`, because `V` is normal. -/
instance isGalois_classField (V : OpenNormalSubgroup (AbsoluteGaloisGroup F)) :
    IsGalois F (classField F V) :=
  (InfiniteGalois.normal_iff_isGalois (classField F V)).1
    (by simpa only [fixingSubgroup_classField] using V.isNormal')

/-- **The class fields are exactly the finite Galois subextensions of `Fˢ`.** -/
theorem exists_classField_eq_iff (L : IntermediateField F (SeparableClosure F)) :
    (∃ V, classField F V = L) ↔ FiniteDimensional F L ∧ IsGalois F L := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨V, rfl⟩
    exact ⟨inferInstance, inferInstance⟩
  · obtain ⟨hopen, hnormal⟩ := (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois L).2 h
    exact ⟨⟨⟨L.fixingSubgroup, hopen⟩, hnormal⟩, InfiniteGalois.fixedField_fixingSubgroup L⟩

/-- **The degree of the class field of `V` is the index of `V`.** -/
theorem finrank_classField (V : OpenNormalSubgroup (AbsoluteGaloisGroup F)) :
    Module.finrank F (classField F V) = V.toSubgroup.index := by
  have : (⟨V.toSubgroup, V.toOpenSubgroup.isClosed⟩ :
      ClosedSubgroup (AbsoluteGaloisGroup F)).Normal := V.isNormal'
  rw [← IsGalois.card_aut_eq_finrank, Subgroup.index]
  exact Nat.card_congr
    (InfiniteGalois.normalAutEquivQuotient ⟨V.toSubgroup, V.toOpenSubgroup.isClosed⟩).symm.toEquiv

end Basic

section Layer

variable {F : Type} [Field F]

/-- **The Galois group of a class field is the Galois group of its layer**: restriction to
`classField F V` identifies `Gal(classField F V / F)` with the finite Galois group `G_F ⧸ V` of
the normal layer `V ◁ G_F`. -/
def galClassFieldEquiv (V : OpenNormalSubgroup (AbsoluteGaloisGroup F)) :
    Gal(classField F V/F) ≃* (NormalLayer.ofOpenNormal V).Gal :=
  have : (⟨V.toSubgroup, V.toOpenSubgroup.isClosed⟩ :
      ClosedSubgroup (AbsoluteGaloisGroup F)).Normal := V.isNormal'
  ((NormalLayer.galOfOpenNormalEquiv V).trans
    (InfiniteGalois.normalAutEquivQuotient ⟨V.toSubgroup, V.toOpenSubgroup.isClosed⟩ :
      AbsoluteGaloisGroup F ⧸ V.toSubgroup ≃* Gal(classField F V/F))).symm

/-- The inverse of `galClassFieldEquiv` sends the class of `σ ∈ G_F` to the restriction of `σ` to
the class field. -/
@[simp]
theorem galClassFieldEquiv_symm_mk (V : OpenNormalSubgroup (AbsoluteGaloisGroup F))
    (σ : (NormalLayer.ofOpenNormal V).ground) :
    (galClassFieldEquiv V).symm (QuotientGroup.mk σ) =
      AlgEquiv.restrictNormalHom (classField F V) (σ : AbsoluteGaloisGroup F) := by
  -- `galClassFieldEquiv` is defined as the inverse of this composite; unfolding it by `rw` would
  -- expose the fixed field, which is not syntactically `classField F V`.
  have : (galClassFieldEquiv V).symm (QuotientGroup.mk σ) =
      InfiniteGalois.normalAutEquivQuotient ⟨V.toSubgroup, V.toOpenSubgroup.isClosed⟩
        (NormalLayer.galOfOpenNormalEquiv V (QuotientGroup.mk σ)) := (rfl)
  rw [this, NormalLayer.galOfOpenNormalEquiv_mk]
  exact InfiniteGalois.normalAutEquivQuotient_apply _ _

/-- Read in `G_F ⧸ V`, `galClassFieldEquiv` sends the restriction of `σ ∈ G_F` to the class field
to the class of `σ`. -/
@[simp]
theorem galOfOpenNormalEquiv_galClassFieldEquiv_restrictNormalHom
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup F)) (σ : AbsoluteGaloisGroup F) :
    NormalLayer.galOfOpenNormalEquiv V
        (galClassFieldEquiv V (AlgEquiv.restrictNormalHom (classField F V) σ)) =
      (σ : AbsoluteGaloisGroup F ⧸ V.toSubgroup) := by
  rw [← galClassFieldEquiv_symm_mk V ⟨σ, by simp⟩, MulEquiv.apply_symm_apply,
    NormalLayer.galOfOpenNormalEquiv_mk]

/-- **The class field of `V` is abelian over `F` exactly when `V` is an abelian layer.** -/
theorem isAbelianGalois_classField_iff {V : OpenNormalSubgroup (AbsoluteGaloisGroup F)} :
    IsAbelianGalois F (classField F V) ↔ V.IsAbelianClassFieldLayer := by
  rw [V.isAbelianClassFieldLayer_iff_isMulCommutative]
  let e := (galClassFieldEquiv V).trans (NormalLayer.galOfOpenNormalEquiv V)
  exact ⟨fun h ↦ e.surjective.isMulCommutative h.toIsMulCommutative,
    fun h ↦ { toIsMulCommutative := e.symm.surjective.isMulCommutative h }⟩

end Layer

end TauCeti.ClassFieldTheory
