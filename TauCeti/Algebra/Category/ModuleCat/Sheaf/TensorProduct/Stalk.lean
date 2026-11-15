/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.TensorProduct.Stalk.Equiv
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic

/-!
# Tensor products and stalks of sheaves of modules

This file constructs, over an arbitrary topological space and for arbitrary sheaves of modules
`M`, `N`, the canonical linear map from the stalk of their tensor product to the tensor product
of their stalks over the ring stalk, and computes its values on germs of sheafified pure tensors.
The comparison is a linear equivalence, with no finiteness or quasi-coherence hypotheses.

It is the sectionwise comparison `PresheafOfModules.tensorStalkComparison`, precomposed with
the inverse of the identification `PresheafOfModules.sheafificationStalkEquiv` of a stalk with
the stalk of the sheafification, and with the stalk map (`PresheafOfModules.stalkMapCommRing`)
of the defining isomorphism `tensorProductIso`.

## Main declarations

* `SheafOfModules.tensorStalkComparison`: the comparison as a linear map over the ring stalk;
* `SheafOfModules.tensorStalkEquiv`: the same comparison as a linear equivalence;
* `SheafOfModules.tensorStalkEquiv_naturality`: compatibility with morphisms in both factors;
* `SheafOfModules.tensorStalkEquiv_symm_tmul_germ`: its inverse on tensors of germs;
* `SheafOfModules.tensorStalkComparison_apply`: its description as the composite above;
* `SheafOfModules.tensorStalkComparison_germ_unit_tmul`: its value on the germ of a sheafified
  pure tensor.
-/

public section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (M N : SheafOfModules.{u} (ringCatSheaf R)) (x : X)

/-- The canonical linear map from the stalk of the tensor product of two sheaves of modules to
the tensor product of their stalks. -/
def tensorStalkComparison :
    ↑(TopCat.Presheaf.stalk (tensorProduct R M N).val.presheaf x) →ₗ[
      ↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk M.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk R.obj x)]
        ↑(TopCat.Presheaf.stalk N.val.presheaf x) :=
  (PresheafOfModules.tensorStalkComparison M.val N.val x).comp
    (((PresheafOfModulesOfCommRing.Monoidal.tensorObj M.val N.val).sheafificationStalkEquiv
      R x).symm.toLinearMap.comp
        (PresheafOfModules.stalkMapCommRing (S := R.obj) x (tensorProductIso R M N).hom.val))

/-- The tensor stalk comparison is the sectionwise comparison, applied after transporting along
`tensorProductIso` and identifying the stalk of the sheafification with the original stalk. -/
theorem tensorStalkComparison_apply
    (s : ↑(TopCat.Presheaf.stalk (tensorProduct R M N).val.presheaf x)) :
    tensorStalkComparison R M N x s =
      PresheafOfModules.tensorStalkComparison M.val N.val x
        (((PresheafOfModulesOfCommRing.Monoidal.tensorObj M.val N.val).sheafificationStalkEquiv
          R x).symm
            (PresheafOfModules.stalkMapCommRing (S := R.obj) x
              (tensorProductIso R M N).hom.val s)) := by
  -- After unfolding, both sides are the same composite applied to `s`.
  unfold tensorStalkComparison
  rfl

/-- The tensor stalk comparison sends the germ of the pure tensor `m ⊗ₜ n`, pushed through the
sheafification unit and transported along `tensorProductIso`, to the tensor product of the
germs of `m` and `n`. -/
@[simp]
theorem tensorStalkComparison_germ_unit_tmul (U : Opens X) (hx : x ∈ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, CategoryTheory.Functor.id_obj,
      CategoryTheory.Functor.comp_obj]
    (tensorStalkComparison R M N x
        (TopCat.Presheaf.germ (tensorProduct R M N).val.presheaf U x hx
          ((tensorProductIso R M N).inv.val.app (op U)
            (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
              (M.val ⊗ N.val)).app (op U) (m ⊗ₜ[(R.obj).obj (op U)] n)))) =
      TopCat.Presheaf.germ M.val.presheaf U x hx m ⊗ₜ[↑(TopCat.Presheaf.stalk R.obj x)]
        TopCat.Presheaf.germ N.val.presheaf U x hx n) := by
  rw [tensorStalkComparison_apply]
  -- `M.val`, `N.val` live over `(ringCatSheaf R).obj`, while the presheaf-level germ lemmas are
  -- stated over `R.obj ⋙ forget₂ CommRingCat RingCat`; the two agree only by unfolding
  -- `ringCatSheaf`, so these rewrites need `erw`.
  erw [PresheafOfModules.stalkMapCommRing_germ,
    ((_root_.SheafOfModules.evaluation _ (op U)).mapIso (tensorProductIso R M N)).inv_hom_id_apply,
    PresheafOfModules.sheafificationStalkEquiv_symm_germ_unit,
    PresheafOfModules.tensorStalkComparison_germ_tmul]
  -- The two sides differ only in writing the ring stalk via `(sheafToPresheaf _ _).obj R`,
  -- which is `R.obj` by definition.
  rfl

/-- The canonical tensor stalk comparison is bijective for arbitrary sheaves of modules. -/
theorem tensorStalkComparison_bijective :
    Function.Bijective (tensorStalkComparison R M N x) := by
  unfold tensorStalkComparison
  apply (PresheafOfModules.tensorStalkComparison_bijective M.val N.val x).comp
  apply ((PresheafOfModulesOfCommRing.Monoidal.tensorObj M.val N.val).sheafificationStalkEquiv
    R x).symm.bijective.comp
  -- The linear stalk map is the underlying additive stalk map of the defining tensor
  -- isomorphism, so it is bijective because the stalk functor preserves isomorphisms.
  have h : (PresheafOfModules.stalkMapCommRing (S := R.obj) x
      (tensorProductIso R M N).hom.val : _ → _) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf _).map (tensorProductIso R M N).hom.val) := by
    funext t
    obtain ⟨U, hx, t, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (tensorProduct R M N).val.presheaf t
    erw [PresheafOfModules.stalkMapCommRing_germ,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rfl
  have : IsIso (tensorProductIso R M N).hom.val :=
    inferInstanceAs (IsIso ((_root_.SheafOfModules.forget _).map
      (tensorProductIso R M N).hom))
  erw [h]
  exact (ConcreteCategory.isIso_iff_bijective _).mp (by infer_instance)

/-- The stalk of the sheaf tensor product is canonically the tensor product of the stalks
over the ring stalk. Its forward map is the existing tensor stalk comparison. -/
def tensorStalkEquiv :
    ↑(TopCat.Presheaf.stalk (tensorProduct R M N).val.presheaf x) ≃ₗ[
      ↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk M.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk R.obj x)]
        ↑(TopCat.Presheaf.stalk N.val.presheaf x) :=
  LinearEquiv.ofBijective (tensorStalkComparison R M N x)
    (tensorStalkComparison_bijective R M N x)

/-- The tensor stalk equivalence is the canonical comparison. -/
@[simp]
theorem tensorStalkEquiv_apply
    (t : ↑(TopCat.Presheaf.stalk (tensorProduct R M N).val.presheaf x)) :
    tensorStalkEquiv R M N x t = tensorStalkComparison R M N x t := (rfl)

/-- The inverse sends a tensor of germs to the germ of the sheafified tensor of their
representatives on a common neighborhood. -/
@[simp]
theorem tensorStalkEquiv_symm_tmul_germ (U : Opens X) (hx : x ∈ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, CategoryTheory.Functor.id_obj,
      CategoryTheory.Functor.comp_obj]
    ((tensorStalkEquiv R M N x).symm
        (TopCat.Presheaf.germ M.val.presheaf U x hx m ⊗ₜ[↑(TopCat.Presheaf.stalk R.obj x)]
          TopCat.Presheaf.germ N.val.presheaf U x hx n) =
      TopCat.Presheaf.germ (tensorProduct R M N).val.presheaf U x hx
        ((tensorProductIso R M N).inv.val.app (op U)
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
            (M.val ⊗ N.val)).app (op U) (m ⊗ₜ[R.obj.obj (op U)] n)))) := by
  apply (tensorStalkEquiv R M N x).symm_apply_eq.mpr
  exact (tensorStalkComparison_germ_unit_tmul R M N x U hx m n).symm

private theorem tensorStalkEquiv_map_germ_unit_tmul
    {M' N' : SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ M') (g : N ⟶ N')
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, Functor.id_obj, Functor.comp_obj]
    (tensorStalkEquiv R M' N' x
      (PresheafOfModules.stalkMapCommRing (S := R.obj) x
        ((tensorProductIso R M N).hom ≫
          (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map (f.val ⊗ₘ g.val) ≫
            (tensorProductIso R M' N').inv).val
        (TopCat.Presheaf.germ (tensorProduct R M N).val.presheaf U x hx
          ((tensorProductIso R M N).inv.val.app (op U)
            (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
              (M.val ⊗ N.val)).app (op U) (m ⊗ₜ[R.obj.obj (op U)] n))))) =
      TopCat.Presheaf.germ M'.val.presheaf U x hx (f.val.app (op U) m) ⊗ₜ[
        ↑(TopCat.Presheaf.stalk R.obj x)]
        TopCat.Presheaf.germ N'.val.presheaf U x hx (g.val.app (op U) n)) := by
  -- Give the unit its underlying-presheaf codomain, eliminating the identity scalar
  -- restriction in the adjunction's right functor before applying categorical naturality.
  let η (P : PresheafOfModules.{u} (ringCatSheaf R).obj) :
      P ⟶ ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj P).val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app P
  have hη : η (M.val ⊗ N.val) ≫
      ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map (f.val ⊗ₘ g.val)).val =
      (f.val ⊗ₘ g.val) ≫ η (M'.val ⊗ N'.val) :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit_naturality _
  have hi : (tensorProductIso R M N).inv.val ≫ (tensorProductIso R M N).hom.val = 𝟙 _ :=
    ((_root_.SheafOfModules.forget _).mapIso (tensorProductIso R M N)).inv_hom_id
  have h :
      η (M.val ⊗ N.val) ≫ (tensorProductIso R M N).inv.val ≫
        ((tensorProductIso R M N).hom ≫
          (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map (f.val ⊗ₘ g.val) ≫
            (tensorProductIso R M' N').inv).val =
      (f.val ⊗ₘ g.val) ≫
        η (M'.val ⊗ N'.val) ≫ (tensorProductIso R M' N').inv.val := by
    simp only [_root_.SheafOfModules.comp_val]
    rw [← Category.assoc (tensorProductIso R M N).inv.val, hi,
      Category.id_comp, ← Category.assoc, hη, Category.assoc]
  erw [PresheafOfModules.stalkMapCommRing_germ]
  have hs := congrArg (fun k ↦ k.app (op U) (m ⊗ₜ[R.obj.obj (op U)] n)) h
  simp only [PresheafOfModules.comp_app] at hs
  dsimp only [η] at hs
  refine (congrArg (fun s ↦ tensorStalkEquiv R M' N' x
    (TopCat.Presheaf.germ (tensorProduct R M' N').val.presheaf U x hx s)) hs).trans ?_
  exact tensorStalkComparison_germ_unit_tmul R M' N' x U hx
    (f.val.app (op U) m) (g.val.app (op U) n)

/-- The tensor stalk equivalence commutes with morphisms in both factors. The map on the sheaf
tensor product is the sheafification of the sectionwise tensor map, read through
`tensorProductIso`. -/
-- The type ascriptions identify the presheaf stalk maps with the sheaf stalk module instances.
theorem tensorStalkEquiv_naturality
    {M' N' : SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ M') (g : N ⟶ N') :
    (tensorStalkEquiv R M' N' x).toLinearMap.comp
        (show ↑(TopCat.Presheaf.stalk (tensorProduct R M N).val.presheaf x) →ₗ[
          ↑(TopCat.Presheaf.stalk R.obj x)]
          ↑(TopCat.Presheaf.stalk (tensorProduct R M' N').val.presheaf x) from
          PresheafOfModules.stalkMapCommRing (S := R.obj) x
          ((tensorProductIso R M N).hom ≫
            (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
              (f.val ⊗ₘ g.val) ≫ (tensorProductIso R M' N').inv).val) =
      (TensorProduct.map
        (show ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
          ↑(TopCat.Presheaf.stalk M'.val.presheaf x) from
          PresheafOfModules.stalkMapCommRing (S := R.obj) x f.val)
        (show ↑(TopCat.Presheaf.stalk N.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
          ↑(TopCat.Presheaf.stalk N'.val.presheaf x) from
          PresheafOfModules.stalkMapCommRing (S := R.obj) x g.val)).comp
          (tensorStalkEquiv R M N x).toLinearMap := by
  apply (LinearMap.cancel_right (tensorStalkEquiv R M N x).symm.surjective).mp
  apply TensorProduct.ext'
  intro m n
  -- Expand the linear-map compositions on the left; the equivalence and stalk map have
  -- definitionally equal presheaf and sheaf module structures.
  change tensorStalkEquiv R M' N' x
      (PresheafOfModules.stalkMapCommRing (S := R.obj) x
        ((tensorProductIso R M N).hom ≫
          (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
            (f.val ⊗ₘ g.val) ≫ (tensorProductIso R M' N').inv).val
          ((tensorStalkEquiv R M N x).symm
            (m ⊗ₜ[↑(TopCat.Presheaf.stalk R.obj x)] n))) =
    _
  conv_rhs =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  have hmap := TensorProduct.map_tmul
    (show ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk M'.val.presheaf x) from
      PresheafOfModules.stalkMapCommRing (S := R.obj) x f.val)
    (show ↑(TopCat.Presheaf.stalk N.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk N'.val.presheaf x) from
      PresheafOfModules.stalkMapCommRing (S := R.obj) x g.val) m n
  rw [hmap]
  obtain ⟨U, hxU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  obtain ⟨V, hVU, hxV, n, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq N.val.presheaf n hxU
  rw [← TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE hVU) x hxV m]
  erw [tensorStalkEquiv_symm_tmul_germ, tensorStalkEquiv_map_germ_unit_tmul]
  conv_rhs =>
    erw [PresheafOfModules.stalkMapCommRing_germ (S := R.obj) x f.val,
      PresheafOfModules.stalkMapCommRing_germ (S := R.obj) x g.val]
  rfl

end SheafOfModules

end

end TauCeti
