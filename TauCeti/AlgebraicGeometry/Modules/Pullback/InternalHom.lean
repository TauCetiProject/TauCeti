/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal

/-!
# Pullback of internal Hom from a quasicoherent sheaf

For a quasicoherent sheaf `M` and an arbitrary sheaf of modules `F` on `Y`, construct the
canonical comparison `f* 𝓗om(M, F) ⟶ 𝓗om(f* M, f* F)` for every scheme morphism `f : X ⟶ Y`.
It is invertible whenever `M` has a quasicoherent left dual. In particular, this applies to
finite locally free sources, without flatness of `f` or finiteness of the target.

The comparison is the mate of the inverse tensor comparison with left factor `M`.
It is characterized by evaluation and is natural in every target sheaf of modules.
Use `TauCeti.AlgebraicGeometry.pullbackIhomComparison M f` for the comparison.
Invertibility follows by identifying internal Hom with tensoring by the dual, and using the
tensor comparison with that quasicoherent dual as left factor. The proof uses
`TauCeti.ihomIsoTensorLeft` and `CategoryTheory.Functor.mapExactPairing` to transport
an exact pairing through pullback on quasicoherent sheaves.

## References

* The Stacks Project, Tag 0C6I (base change for sheaf Hom).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Functor
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}} (M : Y.Modules) [M.IsQuasicoherent] (f : X ⟶ Y)

/-- The canonical base-change comparison for internal Hom from a quasicoherent sheaf.
It is natural in arbitrary target sheaves of modules. -/
def pullbackIhomComparison :
    ihom M ⋙ Scheme.Modules.pullback f ⟶
      Scheme.Modules.pullback f ⋙ ihom ((Scheme.Modules.pullback f).obj M) :=
  (mateEquiv (ihom.adjunction M)
    (ihom.adjunction ((Scheme.Modules.pullback f).obj M))
    (.mk _ _ _ _ (Scheme.Modules.pullbackTensorLeftIso f M).inv)).natTrans

/-- Evaluation after the base-change comparison is the pullback of evaluation, preceded by
the inverse canonical tensor comparison. This characterizes the base-change map. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_pullbackIhomComparison_app_comp_ev (F : Y.Modules) :
    (Scheme.Modules.pullback f).obj M ◁ (pullbackIhomComparison M f).app F ≫
        (ihom.ev ((Scheme.Modules.pullback f).obj M)).app
          ((Scheme.Modules.pullback f).obj F) =
      inv (δ (Scheme.Modules.pullback f) M ((ihom M).obj F)) ≫
        (Scheme.Modules.pullback f).map ((ihom.ev M).app F) := by
  have h := mateEquiv_counit (ihom.adjunction M)
    (ihom.adjunction ((Scheme.Modules.pullback f).obj M))
    (.mk _ _ _ _ (Scheme.Modules.pullbackTensorLeftIso f M).inv) F
  -- Express the mate equation using module whiskering and evaluation, rather than
  -- `tensorLeft.map`, `TwoSquare.app`, and the adjunction counits.
  change (Scheme.Modules.pullback f).obj M ◁
      (pullbackIhomComparison M f).app F ≫
        (ihom.ev ((Scheme.Modules.pullback f).obj M)).app
          ((Scheme.Modules.pullback f).obj F) =
    (Scheme.Modules.pullbackTensorLeftIso f M).inv.app
      ((ihom M).obj F) ≫ (Scheme.Modules.pullback f).map ((ihom.ev M).app F) at h
  have hd : (Scheme.Modules.pullbackTensorLeftIso f M).inv.app
      ((ihom M).obj F) = inv (δ (Scheme.Modules.pullback f) M
        ((ihom M).obj F)) := by
    apply IsIso.eq_inv_of_inv_hom_id
    rw [← Scheme.Modules.pullbackTensorLeftIso_hom_app]
    exact (Scheme.Modules.pullbackTensorLeftIso f M).inv_hom_id_app _
  exact h.trans (congrArg (· ≫ (Scheme.Modules.pullback f).map
    ((ihom.ev M).app F)) hd)

/-- The base-change comparison is obtained by currying the pullback of evaluation, after
inverting the canonical tensor comparison. -/
theorem pullbackIhomComparison_app_eq_curry (F : Y.Modules) :
    (pullbackIhomComparison M f).app F =
      curry (inv (δ (Scheme.Modules.pullback f) M ((ihom M).obj F)) ≫
        (Scheme.Modules.pullback f).map ((ihom.ev M).app F)) := by
  exact (curry_uncurry _).symm.trans
    (congrArg curry (whiskerLeft_pullbackIhomComparison_app_comp_ev M f F))

/-- The canonical internal-Hom base-change comparison is invertible for every scheme morphism
when its quasicoherent source has a quasicoherent left dual, without any condition on the target. -/
theorem isIso_pullbackIhomComparison_of_exactPairing
    (D : Y.Modules) [D.IsQuasicoherent] [ExactPairing D M] :
    IsIso (pullbackIhomComparison M f) := by
  let QD : QuasicoherentSheaf Y := ⟨D, inferInstance⟩
  let QM : QuasicoherentSheaf Y := ⟨M, inferInstance⟩
  let : ExactPairing QD QM :=
    @ObjectProperty.exactPairingFullSubcategory Y.Modules _ _ _
      (Scheme.Modules.isMonoidal_isQuasicoherent Y) QD QM inferInstance
  let : ExactPairing ((Scheme.Modules.pullback f).obj D)
      ((Scheme.Modules.pullback f).obj M) :=
    ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
      Scheme.Modules.pullback f).mapExactPairing QD QM
  let P := Scheme.Modules.pullback f
  -- Internal Hom is tensoring by the dual on both schemes; the intervening tensor
  -- comparison is invertible even for an arbitrary right factor.
  let i : ihom M ⋙ P ≅ P ⋙ ihom (P.obj M) :=
    isoWhiskerRight (ihomIsoTensorLeft D M) P ≪≫
      Scheme.Modules.pullbackTensorLeftIso f D ≪≫
        isoWhiskerLeft P (ihomIsoTensorLeft (P.obj D) (P.obj M)).symm
  have hi (F : Y.Modules) :
      P.obj M ◁ i.hom.app F ≫ (ihom.ev (P.obj M)).app (P.obj F) =
        inv (δ P M ((ihom M).obj F)) ≫ P.map ((ihom.ev M).app F) := by
    rw [← cancel_epi (δ P M ((ihom M).obj F)), IsIso.hom_inv_id_assoc]
    dsimp only [i, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, Category.assoc,
      whiskerLeft_ihomIsoTensorLeft_inv_app_comp_ev,
      Scheme.Modules.pullbackTensorLeftIso_hom_app,
      Functor.OplaxMonoidal.δ_natural_right_assoc]
    -- Unfold left tensoring to match the oplax associativity equation.
    dsimp only [curriedTensor_obj_obj]
    erw [Functor.OplaxMonoidal.associativity_inv_assoc]
    -- The image pairing comes from strong monoidal pullback on quasicoherent sheaves.
    have he : ε_ (P.obj D) (P.obj M) =
        inv (δ P M D) ≫ P.map (ε_ D M) ≫ η P := by
      have h := Functor.mapExactPairing_evaluation
        (F := ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ P))
        QD QM
      rw [Scheme.Modules.pullbackToModules_η, ← Scheme.Modules.pullback_η] at h
      -- Read the composite functor on underlying module maps before rewriting the
      -- full-subcategory evaluation; this avoids mixing the two category instances.
      change ε_ (P.obj D) (P.obj M) =
        μ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ P)
          QM QD ≫ P.map ((ε_ QD QM).hom) ≫ η P at h
      erw [ObjectProperty.exactPairingFullSubcategory_evaluation_hom (C := Y.Modules)] at h
      rw [← Functor.Monoidal.inv_δ] at h
      have hd : inv (δ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ P)
          QM QD) =
          inv (δ P M D) :=
        IsIso.inv_eq_inv.mpr (Scheme.Modules.pullbackToModules_δ f _ _)
      rw [hd] at h
      exact h
    rw [he]
    simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [← MonoidalCategory.comp_whiskerRight_assoc, IsIso.hom_inv_id,
      MonoidalCategory.id_whiskerRight, Category.id_comp]
    rw [Functor.OplaxMonoidal.δ_natural_left_assoc,
      Functor.OplaxMonoidal.left_unitality_hom, ← P.map_comp, ← P.map_comp,
      ← P.map_comp, whiskerLeft_ihomIsoTensorLeft_hom_app_comp_evaluation]
  -- Evaluation uniquely characterizes the canonical comparison, so the constructed
  -- natural isomorphism has precisely that forward map.
  have h : (pullbackIhomComparison M f) = i.hom := by
    apply NatTrans.ext
    funext F
    apply uncurry_injective
    exact (whiskerLeft_pullbackIhomComparison_app_comp_ev M f F).trans (hi F).symm
  rw [h]
  infer_instance

end

end TauCeti.AlgebraicGeometry
