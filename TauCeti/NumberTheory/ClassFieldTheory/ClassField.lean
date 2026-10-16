/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.Galois.Infinite
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
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

The same dictionary reads an arbitrary finite normal layer `V ◁ U` of `G_F`, whose ground `U` is
any open subgroup: if `E` and `L` are the fixed fields of `U` and `V`, then `L/E` is Galois
(`NormalLayer.isGalois_of_fixedField`) and restriction to `L` identifies the Galois group `U ⧸ V`
of the layer with `Gal(L/E)` (`NormalLayer.galEquivOfFixedField`).

## Main definitions

* `TauCeti.ClassFieldTheory.classField F V`: the fixed field of `V` in `Fˢ`.
* `TauCeti.ClassFieldTheory.galClassFieldEquiv`: the Galois group of `classField F V` over `F` is
  the Galois group of the finite normal layer `V ◁ G_F`.
* `TauCeti.ClassFieldTheory.NormalLayer.galEquivOfFixedField`: the Galois group of a finite
  normal layer `V ◁ U` is `Gal(L/E)` for the fixed fields `E` of `U` and `L` of `V`.

## Main results

* `TauCeti.ClassFieldTheory.fixingSubgroup_classField`: the fixing subgroup of the class field of
  `V` is `V`.
* `TauCeti.ClassFieldTheory.fixingOpenNormalSubgroup_classField`: the bundled open normal subgroup
  cut out by the class field of `V` is `V`.
* `TauCeti.ClassFieldTheory.classField_le_classField_iff`: `classField F W ≤ classField F V` if
  and only if `V ≤ W`.
* `TauCeti.ClassFieldTheory.exists_classField_eq_iff`: the class fields are exactly the finite
  Galois subextensions of `Fˢ`.
* `TauCeti.ClassFieldTheory.finrank_classField`: the degree of the class field of `V` is the index
  of `V`.
* `TauCeti.ClassFieldTheory.isAbelianGalois_classField_iff`: the class field of `V` is abelian
  over `F` if and only if `V` is an abelian layer.
* `TauCeti.ClassFieldTheory.NormalLayer.isGalois_of_fixedField`: the fixed field of the top
  subgroup of a layer is Galois over the fixed field of its ground subgroup.

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
  -- `classField F V` is defined as the fixed field of `V`.
  finiteDimensional_fixedField_toSubgroup V.toOpenSubgroup

/-- The class field of `V` is Galois over `F`, because `V` is normal. -/
instance isGalois_classField (V : OpenNormalSubgroup (AbsoluteGaloisGroup F)) :
    IsGalois F (classField F V) :=
  (InfiniteGalois.normal_iff_isGalois (classField F V)).1
    (by simpa only [fixingSubgroup_classField] using V.isNormal')

/-- Cutting out the class field of `V` and then taking the open normal subgroup that fixes it
recovers `V`. -/
@[simp]
theorem fixingOpenNormalSubgroup_classField (V : OpenNormalSubgroup (AbsoluteGaloisGroup F)) :
    fixingOpenNormalSubgroup F (classField F V) = V := by
  apply OpenNormalSubgroup.toSubgroup_injective
  -- Expose the underlying subgroups so the finite-extension fixing-subgroup theorem rewrites.
  change (fixingOpenNormalSubgroup F (classField F V)).toSubgroup = V.toSubgroup
  rw [fixingOpenNormalSubgroup_toSubgroup (classField F V).val,
    IntermediateField.fieldRange_val, fixingSubgroup_classField]

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
  -- Chained as terms: `rw` would type-check its motives over the class field's Galois group.
  exact this.trans ((congrArg _ (NormalLayer.galOfOpenNormalEquiv_mk V σ)).trans
    (InfiniteGalois.normalAutEquivQuotient_apply _ _))

/-- The fixed field of the top subgroup `V` of the layer `V ◁ G_F` is the class field of `V`. -/
theorem fixedField_top_ofOpenNormal_eq_classField (V : OpenNormalSubgroup (AbsoluteGaloisGroup F)) :
    fixedField (NormalLayer.ofOpenNormal V).top.toSubgroup = classField F V := by
  rw [NormalLayer.top_ofOpenNormal, ← InfiniteGalois.fixedField_fixingSubgroup (classField F V),
    fixingSubgroup_classField]

/-- The inverse of `galClassFieldEquiv` sends the class of `u ∈ G_F` to an automorphism of the
class field acting as `u`. -/
theorem coe_galClassFieldEquiv_symm_apply (V : OpenNormalSubgroup (AbsoluteGaloisGroup F))
    (u : (NormalLayer.ofOpenNormal V).ground) (x : classField F V) :
    ((galClassFieldEquiv V).symm u x : SeparableClosure F) = (u : AbsoluteGaloisGroup F) x := by
  rw [galClassFieldEquiv_symm_mk]
  exact AlgEquiv.restrictNormal_commutes _ _ x

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
  exact ⟨fun h ↦ have := h.toIsMulCommutative; e.surjective.isMulCommutative,
    fun _ ↦ { toIsMulCommutative := e.symm.surjective.isMulCommutative }⟩

end Layer

/-! ### The fixed fields of an arbitrary layer -/

section FixedField

variable {F : Type} [Field F] (Lay : NormalLayer (AbsoluteGaloisGroup F))
  {E L : IntermediateField F (SeparableClosure F)} [Algebra E L]
  [IsScalarTower E L (SeparableClosure F)]

namespace NormalLayer

/-- The ground subgroup of a layer with fixed field `E`, read as `Gal(Fˢ/E)`. -/
private def groundEquivOfFixedField (hE : fixedField Lay.ground.toSubgroup = E) :
    Lay.ground ≃* Gal(SeparableClosure F/E) :=
  (MulEquiv.subgroupCongr (toSubgroup_eq_fixingSubgroup_of_fixedField_eq hE)).trans
    E.fixingSubgroupEquiv

private theorem groundEquivOfFixedField_apply (hE : fixedField Lay.ground.toSubgroup = E)
    (g : Lay.ground) (x : SeparableClosure F) :
    Lay.groundEquivOfFixedField hE g x = (g : AbsoluteGaloisGroup F) x :=
  (rfl)

/-- An element of the ground subgroup lies in the top subgroup exactly when it fixes the fixed
field of the top subgroup pointwise. -/
private theorem mem_relativeTop_iff (hL : fixedField Lay.top.toSubgroup = L) (g : Lay.ground) :
    g ∈ Lay.relativeTop ↔ ∀ x : L, (g : AbsoluteGaloisGroup F) x = x := by
  rw [Subgroup.mem_subgroupOf, toSubgroup_eq_fixingSubgroup_of_fixedField_eq hL,
    IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x ↦ h x x.2, fun h x hx ↦ h ⟨x, hx⟩⟩

/-- Read in `Gal(Fˢ/E)`, the top subgroup of the layer is the subgroup fixing `L`. -/
private theorem fixingSubgroup_fieldRange (hE : fixedField Lay.ground.toSubgroup = E)
    (hL : fixedField Lay.top.toSubgroup = L) :
    (IsScalarTower.toAlgHom E L (SeparableClosure F)).fieldRange.fixingSubgroup =
      Lay.relativeTop.map (Lay.groundEquivOfFixedField hE) := by
  ext σ
  obtain ⟨g, rfl⟩ := (Lay.groundEquivOfFixedField hE).surjective σ
  rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.mem_comap, MonoidHom.coe_ofClass,
    MulEquiv.symm_apply_apply, Lay.mem_relativeTop_iff hL,
    IntermediateField.mem_fixingSubgroup_iff]
  simp only [AlgHom.mem_fieldRange, IsScalarTower.coe_toAlgHom', forall_exists_index,
    forall_apply_eq_imp_iff, groundEquivOfFixedField_apply, IntermediateField.algebraMap_apply]

/-- The image of `L` in `Fˢ` is Galois over `E`: its fixing subgroup is the image of the top
subgroup of the layer, normal in `Gal(Fˢ/E)`. -/
private theorem isGalois_fieldRange (hE : fixedField Lay.ground.toSubgroup = E)
    (hL : fixedField Lay.top.toSubgroup = L) :
    IsGalois E (IsScalarTower.toAlgHom E L (SeparableClosure F)).fieldRange := by
  have : IsGalois E (SeparableClosure F) := IsGalois.tower_top_of_isGalois F E _
  refine (InfiniteGalois.normal_iff_isGalois _).1 ?_
  rw [Lay.fixingSubgroup_fieldRange hE hL]
  exact Subgroup.Normal.map inferInstance _ (Lay.groundEquivOfFixedField hE).surjective

/-- **A layer is Galois on fixed fields**: if the ground and top subgroups of a layer `V ◁ U` of
`G_F` have fixed fields `E` and `L`, then `L/E` is a Galois extension. -/
theorem isGalois_of_fixedField (hE : fixedField Lay.ground.toSubgroup = E)
    (hL : fixedField Lay.top.toSubgroup = L) : IsGalois E L :=
  have := Lay.isGalois_fieldRange hE hL
  IsGalois.of_algEquiv (IsScalarTower.toAlgHom E L (SeparableClosure F)).equivFieldRange.symm

/-- **The Galois group of a layer is the Galois group of its fixed fields**: if the ground and top
subgroups of a layer `V ◁ U` of `G_F` have fixed fields `E` and `L`, restriction to `L` identifies
the Galois group `U ⧸ V` of the layer with `Gal(L/E)`. -/
def galEquivOfFixedField (hE : fixedField Lay.ground.toSubgroup = E)
    (hL : fixedField Lay.top.toSubgroup = L) : Lay.Gal ≃* Gal(L/E) :=
  have : IsGalois E (SeparableClosure F) := IsGalois.tower_top_of_isGalois F E _
  have := (Lay.isGalois_fieldRange hE hL).to_normal
  (QuotientGroup.congr _ _ (Lay.groundEquivOfFixedField hE)
      (Lay.fixingSubgroup_fieldRange hE hL).symm).trans
    ((quotientFixingSubgroupEquiv E (SeparableClosure F) _).toMulEquiv.trans
      (AlgEquiv.autCongr (IsScalarTower.toAlgHom E L (SeparableClosure F)).equivFieldRange.symm))

/-- `galEquivOfFixedField` sends the class of `g` in the ground subgroup to the restriction of `g`
to `L`: its value at `x ∈ L` is `g x`. -/
@[simp]
theorem coe_galEquivOfFixedField_mk_apply (hE : fixedField Lay.ground.toSubgroup = E)
    (hL : fixedField Lay.top.toSubgroup = L) (g : Lay.ground) (x : L) :
    ((Lay.galEquivOfFixedField hE hL (g : Lay.Gal) x : L) : SeparableClosure F) =
      (g : AbsoluteGaloisGroup F) x := by
  have : IsGalois E (SeparableClosure F) := IsGalois.tower_top_of_isGalois F E _
  have := (Lay.isGalois_fieldRange hE hL).to_normal
  -- Read in `Fˢ`, a point of `L` and its image in the field range are the same point.
  have he (y : (IsScalarTower.toAlgHom E L (SeparableClosure F)).fieldRange) :
      (((IsScalarTower.toAlgHom E L (SeparableClosure F)).equivFieldRange.symm y : L) :
        SeparableClosure F) = y := by
    conv_rhs => rw [← AlgEquiv.apply_symm_apply
      (IsScalarTower.toAlgHom E L (SeparableClosure F)).equivFieldRange y]
    rw [AlgHom.equivFieldRange_apply_coe, IsScalarTower.coe_toAlgHom',
      IntermediateField.algebraMap_apply]
  rw [galEquivOfFixedField, MulEquiv.trans_apply, MulEquiv.trans_apply, AlgEquiv.autCongr_apply,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.symm_symm, he, QuotientGroup.congr_mk,
    ContinuousMulEquiv.toMulEquiv_eq_coe]
  simp only [ContinuousMulEquiv.coe_toMulEquiv, quotientFixingSubgroupEquiv_mk,
    AlgEquiv.restrictNormalHom_apply, AlgHom.equivFieldRange_apply_coe, IsScalarTower.coe_toAlgHom',
    IntermediateField.algebraMap_apply, groundEquivOfFixedField_apply]

end NormalLayer

end FixedField

end TauCeti.ClassFieldTheory
