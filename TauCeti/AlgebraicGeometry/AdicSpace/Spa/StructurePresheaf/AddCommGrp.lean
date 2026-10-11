/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.Lattice
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Functor

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

For an open `Y ≤ W`, the restriction of a cover `U` of `W` to `Y` is computed by the presheaf
`V ↦ 𝒪(Y ∩ V)` on the opens contained in `W`. This presheaf is pulled back from the opens contained
in `Y` along `V ↦ Y ∩ V`, so the restriction of `U` to `Y` is acyclic exactly when the cover
`Y ∩ U` of `Y` is (`quasiIso_cechAugmentation_prod_iff`).

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitAddCommGrpPresheaf`: the presentation-limit
  presheaf on the opens contained in `W`, as a presheaf of abelian groups.
* `TauCeti.ValuationSpectrum.presentationLimitAddCommGrpPresheafObjEquiv`: its sections over `V`
  are the additive group of `presentationLimit Aplus V`; under this identification its restriction
  maps are the `presentationLimitMap`s
  (`TauCeti.ValuationSpectrum.presentationLimitAddCommGrpPresheafObjEquiv_map_apply`).

## Main results

* `TauCeti.ValuationSpectrum.quasiIso_cechAugmentation_prod_iff`: the restriction to `Y ≤ W` of a
  family of opens contained in `W` is acyclic for the structure presheaf if and only if its
  intersection with `Y`, as a cover of `Y`, is.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite TauCeti.Huber TauCeti.CategoryTheory

universe v w

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

/-! ### Restriction to a smaller open -/

section Restrict

variable {Aplus} {W : Opens ↥(spa Aplus)}

/-- Intersection with `Y`, from the opens contained in `W` to the opens contained in `Y`. -/
private noncomputable def interFunctor (Y : Set.Iic W) : Set.Iic W ⥤ Set.Iic Y.1 :=
  Monotone.functor (f := fun V ↦ ⟨Y.1 ⊓ V.1, Set.mem_Iic.2 inf_le_left⟩)
    fun _ _ h ↦ inf_le_inf_left _ h

/-- The structure presheaf restricted to `Y`, as a presheaf on the opens contained in `W`, is the
pullback of the structure presheaf on the opens contained in `Y` along intersection with `Y`. Its
components are restriction maps between equal opens. -/
private noncomputable def restrIso (Y : Set.Iic W) :
    (prod.functor.obj Y).op ⋙ presentationLimitAddCommGrpPresheaf P Aplus W ≅
      (interFunctor Y).op ⋙ presentationLimitAddCommGrpPresheaf P Aplus Y.1 :=
  NatIso.ofComponents (fun V ↦
    have e : ((prod.functor.obj Y).obj V.unop).1 = ((interFunctor Y).obj V.unop).1 :=
      congrArg Subtype.val (CompleteLattice.prod_eq_inf Y V.unop)
    { hom := AddCommGrpCat.ofHom (presentationLimitMap (P := P) e.ge).hom.1.toAddMonoidHom
      inv := AddCommGrpCat.ofHom (presentationLimitMap (P := P) e.le).hom.1.toAddMonoidHom
      hom_inv_id := by
        ext x
        exact (presentationLimitMap_apply_presentationLimitMap_apply _ _ x).trans
          (ConcreteCategory.congr_hom (presentationLimitMap_refl (P := P) Aplus _) x)
      inv_hom_id := by
        ext x
        exact (presentationLimitMap_apply_presentationLimitMap_apply _ _ x).trans
          (ConcreteCategory.congr_hom (presentationLimitMap_refl (P := P) Aplus _) x) })
    fun _ ↦ by
      ext x
      exact (presentationLimitMap_apply_presentationLimitMap_apply _ _ x).trans
        (presentationLimitMap_apply_presentationLimitMap_apply _ _ x).symm

/-- **Restricting a cover to a smaller open.** Let `Y ≤ W` be opens of `Spa(A, A⁺)` and let `U` be a
family of opens contained in `W`. The augmented Čech complex of the structure presheaf restricted
to `Y`, the presheaf `V ↦ 𝒪(Y ∩ V)` on the opens contained in `W`, for `U` is exact if and only if
the augmented Čech complex of the structure presheaf on the opens contained in `Y` for the family
`Y ∩ U i` is. -/
theorem quasiIso_cechAugmentation_prod_iff [HasProducts.{w} AddCommGrpCat.{v}] (Y : Set.Iic W)
    {ι : Type w} (U : ι → Set.Iic W) :
    QuasiIso (cechAugmentation U isTerminalTop
        ((prod.functor.obj Y).op ⋙ presentationLimitAddCommGrpPresheaf P Aplus W)) ↔
      QuasiIso (cechAugmentation
        (fun i ↦ (⟨Y.1 ⊓ (U i).1, Set.mem_Iic.2 inf_le_left⟩ : Set.Iic Y.1)) isTerminalTop
        (presentationLimitAddCommGrpPresheaf P Aplus Y.1)) := by
  rw [quasiIso_cechAugmentation_iff_of_iso _ _ _ (restrIso P Y)]
  -- intersection with `Y` sends products of members into the intersection of their product
  have hG (m : ℕ) (a : Fin (m + 1) → ι) :
      Nonempty ((∏ᶜ fun j ↦ (interFunctor Y).obj (U (a j))) ⟶
        (interFunctor Y).obj (∏ᶜ fun j ↦ U (a j))) := by
    refine ⟨homOfLE (Subtype.mk_le_mk.2 (le_inf (∏ᶜ fun j ↦ (interFunctor Y).obj (U (a j))).2 ?_))⟩
    let Z : Set.Iic W :=
      ⟨_, Set.mem_Iic.2 ((∏ᶜ fun j ↦ (interFunctor Y).obj (U (a j))).2.trans Y.2)⟩
    have hπ (j : Fin (m + 1)) : (∏ᶜ fun j ↦ (interFunctor Y).obj (U (a j))).1 ≤
        ((interFunctor Y).obj (U (a j))).1 :=
      Subtype.coe_le_coe.2 (leOfHom (Pi.π _ j))
    have hZ : Z ⟶ ∏ᶜ fun j ↦ U (a j) := Pi.lift fun j ↦ homOfLE (Subtype.coe_le_coe.1
      ((hπ j).trans (show Y.1 ⊓ (U (a j)).1 ≤ _ from inf_le_right)))
    exact leOfHom hZ
  -- intersection with `Y` sends `W` to `Y`
  have hGT : IsTerminal ((interFunctor Y).obj ⊤) :=
    isTerminalTop.ofIso (eqToIso (Subtype.ext (inf_eq_left.2 Y.2)).symm)
  rw [quasiIso_cechAugmentation_op_comp_iff (interFunctor Y) _ _ hG isTerminalTop hGT]
  suffices h : ∀ {T : Set.Iic Y.1} (hT : IsTerminal T), T = ⊤ →
      (QuasiIso (cechAugmentation (fun i ↦ (interFunctor Y).obj (U i)) hT
        (presentationLimitAddCommGrpPresheaf P Aplus Y.1)) ↔
      QuasiIso (cechAugmentation (fun i ↦ (interFunctor Y).obj (U i)) isTerminalTop
        (presentationLimitAddCommGrpPresheaf P Aplus Y.1))) from
    h hGT (Subtype.ext (inf_eq_left.2 Y.2))
  rintro T hT rfl
  rw [Subsingleton.elim hT isTerminalTop]

end Restrict

end TauCeti.ValuationSpectrum
