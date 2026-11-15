/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.Topology.Sheaves.Module
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.TensorProduct.Stalk.Equiv
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal

/-!
# Tensor products and stalks of sheaves of modules

This file constructs, over an arbitrary topological space and for arbitrary sheaves of modules
`M`, `N`, the canonical linear map from the stalk of their tensor product to the tensor product
of their stalks over the ring stalk, and computes its values on germs of sheafified pure tensors.
The comparison is a linear equivalence, with no finiteness or quasi-coherence hypotheses.

It is given both for the explicit sheaf `SheafOfModules.tensorProduct R M N` and for the monoidal
tensor product `M ⊗ N` (`TauCeti.SheafOfModules.monoidalCategory`). The former is the sectionwise
comparison `PresheafOfModules.tensorStalkComparison`, precomposed with the inverse of
`PresheafOfModules.sheafificationStalkEquiv` and with the stalk map of `tensorProductIso`; the
latter transports this identification along `M.tensorUnderlyingIso N` and `tensorProductIso`
(`tensorObjStalkComparison` and `tensorObjStalkEquiv`), commuting with `f ⊗ₘ g` on stalks.
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

section Monoidal
open TopCat.Presheaf
open _root_.SheafOfModules (stalkMap stalkMap_germ isIso_iff_stalkMap_bijective)

/-- The canonical `R_x`-linear comparison `(M ⊗ N)_x →ₗ[R_x] M_x ⊗[R_x] N_x` for the monoidal
tensor product of sheaves of modules. -/
def tensorObjStalkComparison :
    ↑(stalk (M ⊗ N).val.presheaf x) →ₗ[↑(stalk R.obj x)]
      ↑(stalk M.val.presheaf x) ⊗[↑(stalk R.obj x)] ↑(stalk N.val.presheaf x) :=
  (tensorStalkComparison R M N x).comp
    (stalkMap ((M.tensorUnderlyingIso N).hom ≫ (tensorProductIso R M N).inv) x)

/-- On the germ of the image of `m ⊗ₜ n` under `Functor.LaxMonoidal.μ (forget _)`,
`tensorObjStalkComparison` evaluates to the pure tensor of the germs of `m` and `n`. -/
@[simp] theorem tensorObjStalkComparison_germ_μ_tmul (U : Opens X) (hx : x ∈ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, Functor.id_obj, Functor.comp_obj]
    (tensorObjStalkComparison R M N x (germ (M ⊗ N).val.presheaf U x hx
          (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app
            (op U)) (m ⊗ₜ[R.obj.obj (op U)] n))) =
      germ M.val.presheaf U x hx m ⊗ₜ[↑(stalk R.obj x)] germ N.val.presheaf U x hx n) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)
  let F := _root_.SheafOfModules.forget (ringCatSheaf R) ⋙
    PresheafOfModules.restrictScalars (𝟙 (ringCatSheaf R).obj)
  let _ := adj.rightAdjointLaxMonoidal
  let p : M ⊗ N ⟶ tensorProduct R M N :=
    (M.tensorUnderlyingIso N).hom ≫ (tensorProductIso R M N).inv
  have hd : Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj))
        (F.obj M) (F.obj N) ≫ (adj.counit.app M ⊗ₘ adj.counit.app N) =
      (M.tensorUnderlyingIso N).inv :=
    ((_root_.SheafOfModules.tensorUnderlyingIso_inv M N).trans
      (congrArg (Functor.OplaxMonoidal.δ _ M.val N.val ≫ ·)
        (congrArg₂ (· ⊗ₘ ·) (sheafificationIso_hom _ M) (sheafificationIso_hom _ N)))).symm
  have hinv : (Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj))
        (F.obj M) (F.obj N) ≫ (adj.counit.app M ⊗ₘ adj.counit.app N)) ≫ p =
      (tensorProductIso R M N).inv :=
    (congrArg (· ≫ p) hd).trans
      (Iso.inv_hom_id_assoc (M.tensorUnderlyingIso N) (tensorProductIso R M N).inv)
  have h₀ := congrArg (fun k ↦ p.val.app (op U) (k.app (op U) (m ⊗ₜ[R.obj.obj (op U)] n)))
    ((_root_.SheafOfModules.sheafificationAdjunction_μ_eq_forget_μ R M N).symm.trans
      ((Adjunction.rightAdjointLaxMonoidal_μ adj M N).trans (Adjunction.homEquiv_unit adj _ _ _)))
  have h₁ := h₀.trans (congrArg (fun q ↦ q.val.app (op U)
    ((adj.unit.app (M.val ⊗ N.val)).app (op U) (m ⊗ₜ[R.obj.obj (op U)] n))) hinv)
  exact (congrArg (tensorStalkComparison R M N x) ((stalkMap_germ p x U hx _).trans
    (congrArg (germ (tensorProduct R M N).val.presheaf U x hx) h₁))).trans
    (tensorStalkComparison_germ_unit_tmul R M N x U hx m n)

/-- `(M ⊗ N)_x →ₗ[R_x] M_x ⊗[R_x] N_x` is bijective for arbitrary sheaves of modules. -/
theorem tensorObjStalkComparison_bijective :
    Function.Bijective (tensorObjStalkComparison R M N x) :=
  (tensorStalkComparison_bijective R M N x).comp
    ((isIso_iff_stalkMap_bijective
      ((M.tensorUnderlyingIso N).hom ≫ (tensorProductIso R M N).inv)).mp inferInstance x)

/-- The canonical `R_x`-linear equivalence `(M ⊗ N)_x ≃ₗ[R_x] M_x ⊗[R_x] N_x` for the monoidal
tensor product of sheaves of modules. -/
def tensorObjStalkEquiv :
    ↑(stalk (M ⊗ N).val.presheaf x) ≃ₗ[↑(stalk R.obj x)]
      ↑(stalk M.val.presheaf x) ⊗[↑(stalk R.obj x)] ↑(stalk N.val.presheaf x) :=
  LinearEquiv.ofBijective (tensorObjStalkComparison R M N x)
    (tensorObjStalkComparison_bijective R M N x)
@[simp] theorem tensorObjStalkEquiv_apply (t : ↑(stalk (M ⊗ N).val.presheaf x)) :
    tensorObjStalkEquiv R M N x t = tensorObjStalkComparison R M N x t := (rfl)

/-- `(tensorObjStalkEquiv R M N x).symm` sends `germ(m) ⊗ₜ germ(n)` to `germ(μ(m ⊗ₜ n))`. -/
@[simp] theorem tensorObjStalkEquiv_symm_tmul_germ (U : Opens X) (hx : x ∈ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, Functor.id_obj, Functor.comp_obj]
    ((tensorObjStalkEquiv R M N x).symm
        (germ M.val.presheaf U x hx m ⊗ₜ[↑(stalk R.obj x)] germ N.val.presheaf U x hx n) =
      germ (M ⊗ N).val.presheaf U x hx
        (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app
          (op U)) (m ⊗ₜ[R.obj.obj (op U)] n))) :=
  (tensorObjStalkEquiv R M N x).symm_apply_eq.mpr
    (tensorObjStalkComparison_germ_μ_tmul R M N x U hx m n).symm

/-- Naturality of `tensorObjStalkComparison` with respect to `f ⊗ₘ g`. -/
theorem tensorObjStalkComparison_naturality
    {M' N' : SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ M') (g : N ⟶ N') :
    (tensorObjStalkComparison R M' N' x).comp (stalkMap (f ⊗ₘ g) x) =
      (TensorProduct.map (stalkMap f x) (stalkMap g x)).comp
        (tensorObjStalkComparison R M N x) := by
  apply (LinearMap.cancel_right (tensorObjStalkEquiv R M N x).symm.surjective).mp
  refine TensorProduct.ext' fun m n ↦ ?_
  obtain ⟨U, hxU, m₀, rfl⟩ := exists_germ_eq M.val.presheaf m
  obtain ⟨V, hVU, hxV, n₀, rfl⟩ := exists_le_germ_eq N.val.presheaf n hxU
  let m₁ : M.val.obj (op V) := M.val.map (homOfLE hVU).op m₀
  rw [← germ_res_apply M.val.presheaf (homOfLE hVU) x hxV m₀]
  have hn := congrArg (fun k ↦ k.app (op V) (m₁ ⊗ₜ[R.obj.obj (op V)] n₀))
    (Functor.LaxMonoidal.μ_natural (_root_.SheafOfModules.forget (ringCatSheaf R)) f g)
  have hL := (congrArg (fun t ↦ tensorObjStalkComparison R M' N' x (stalkMap (f ⊗ₘ g) x t))
      (tensorObjStalkEquiv_symm_tmul_germ R M N x V hxV m₁ n₀)).trans
    ((congrArg (tensorObjStalkComparison R M' N' x)
      ((stalkMap_germ (f ⊗ₘ g) x V hxV _).trans
        (congrArg (germ (M' ⊗ N').val.presheaf V x hxV) hn.symm))).trans
      (tensorObjStalkComparison_germ_μ_tmul R M' N' x V hxV (f.val.app (op V) m₁)
        (g.val.app (op V) n₀)))
  have hR := ((congrArg (TensorProduct.map (stalkMap f x) (stalkMap g x))
      ((tensorObjStalkEquiv R M N x).apply_symm_apply _)).trans
      (TensorProduct.map_tmul _ _ _ _)).trans
    (congrArg₂ (· ⊗ₜ ·) (stalkMap_germ f x V hxV m₁) (stalkMap_germ g x V hxV n₀))
  exact hL.trans hR.symm

/-- Naturality of `tensorObjStalkEquiv` with respect to `f ⊗ₘ g`. -/
theorem tensorObjStalkEquiv_naturality
    {M' N' : SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ M') (g : N ⟶ N') :
    (tensorObjStalkEquiv R M' N' x).toLinearMap.comp (stalkMap (f ⊗ₘ g) x) =
      (TensorProduct.map (stalkMap f x) (stalkMap g x)).comp
        (tensorObjStalkEquiv R M N x).toLinearMap :=
  tensorObjStalkComparison_naturality R M N x f g
end Monoidal
end SheafOfModules

end

end TauCeti
