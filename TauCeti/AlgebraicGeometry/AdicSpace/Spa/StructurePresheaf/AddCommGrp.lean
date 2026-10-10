/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Basic

/-!
# The structure presheaf on the opens of a fixed open, as a presheaf of abelian groups

Let `W` be an open subset of `X = Spa(A, A⁺)`. The opens of `X` contained in `W` form the
meet-semilattice `Set.Iic W`, whose greatest element is `W`; in the corresponding category `W` is
a terminal object and binary products are meets. Covers of `W` are therefore families in
`Set.Iic W`, and their Čech complexes (`CategoryTheory.cechComplexFunctor`, with the augmentation
`TauCeti.CategoryTheory.cechAugmentation`) are defined for presheaves on `Set.Iic W` with values in
an abelian category. This file provides the presheaf to which they are applied: the
presentation-limit presheaf, restricted to `Set.Iic W` and regarded as a presheaf of abelian
groups.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitAddCommGrpPresheaf`: the presentation-limit
  presheaf on the opens contained in `W`, as a presheaf of abelian groups.
* `TauCeti.ValuationSpectrum.presentationLimitAddCommGrpPresheafObjEquiv`: its sections over `V`
  are the additive group of `presentationLimit Aplus V`; under this identification its restriction
  maps are the `presentationLimitMap`s
  (`TauCeti.ValuationSpectrum.presentationLimitAddCommGrpPresheafObjEquiv_map_apply`).
-/

public section

open CategoryTheory TopologicalSpace Opposite TauCeti.Huber

universe v

namespace TauCeti.ValuationSpectrum

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A)

/-- The presentation-limit presheaf restricted to the opens contained in `W`, as a presheaf of
abelian groups: its value at `V ≤ W` is the additive group of `presentationLimit Aplus V` and its
restriction maps are the `presentationLimitMap`s, as for `presentationLimitPresheaf`. Its Čech
complexes for families in `Set.Iic W` are those of covers of `W`. -/
noncomputable def presentationLimitAddCommGrpPresheaf (W : Opens ↥(spa Aplus)) :
    (Set.Iic W)ᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj V := AddCommGrpCat.of (presentationLimit (P := P) Aplus V.unop.1)
  map h := AddCommGrpCat.ofHom
    (presentationLimitMap (P := P) (Subtype.coe_le_coe.mpr (leOfHom h.unop))).hom.1.toAddMonoidHom
  map_id V := by
    ext x
    exact ConcreteCategory.congr_hom (presentationLimitMap_refl (P := P) Aplus V.unop.1) x
  map_comp h₁ h₂ := by
    ext x
    exact (presentationLimitMap_apply_presentationLimitMap_apply (P := P) _ _ x).symm

/-- The sections of `presentationLimitAddCommGrpPresheaf` over `V` are the additive group of
`presentationLimit Aplus V`. -/
-- Not `@[simp]`: rewriting the objects of the functor would put its morphisms in mismatched types.
theorem presentationLimitAddCommGrpPresheaf_obj (W : Opens ↥(spa Aplus)) (V : (Set.Iic W)ᵒᵖ) :
    (presentationLimitAddCommGrpPresheaf P Aplus W).obj V =
      AddCommGrpCat.of (presentationLimit (P := P) Aplus V.unop.1) :=
  (rfl)

/-- The sections of `presentationLimitAddCommGrpPresheaf` over `V`, identified with the additive
group of `presentationLimit Aplus V`. -/
noncomputable def presentationLimitAddCommGrpPresheafObjEquiv {W : Opens ↥(spa Aplus)}
    (V : Set.Iic W) :
    (presentationLimitAddCommGrpPresheaf P Aplus W).obj (op V) ≃+
      presentationLimit (P := P) Aplus V.1 :=
  AddEquiv.refl _

/-- Under `presentationLimitAddCommGrpPresheafObjEquiv`, the restriction maps of
`presentationLimitAddCommGrpPresheaf` are the `presentationLimitMap`s. -/
@[simp]
theorem presentationLimitAddCommGrpPresheafObjEquiv_map_apply {W : Opens ↥(spa Aplus)}
    {V V' : Set.Iic W} (h : V' ⟶ V)
    (x : (presentationLimitAddCommGrpPresheaf P Aplus W).obj (op V)) :
    presentationLimitAddCommGrpPresheafObjEquiv P Aplus V'
        ((presentationLimitAddCommGrpPresheaf P Aplus W).map h.op x) =
      (presentationLimitMap (P := P) (Subtype.coe_le_coe.mpr (leOfHom h))).hom.1
        (presentationLimitAddCommGrpPresheafObjEquiv P Aplus V x) :=
  (rfl)

end TauCeti.ValuationSpectrum
