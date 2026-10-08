/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.InternalHom.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal

/-!
# Pullback of internal Hom from a finite locally free sheaf

For a finite locally free sheaf `E` and an arbitrary sheaf of modules `F` on `Y`, the canonical
comparison `f* 𝓗om(E, F) ⟶ 𝓗om(f* E, f* F)` is an isomorphism for every scheme morphism
`f : X ⟶ Y`. No flatness assumption on `f` or finiteness assumption on `F` is needed.

The comparison is the mate of the inverse tensor comparison for pullback with left factor
`E`. It is characterized by evaluation and is natural in every target sheaf of modules.
Its invertibility follows by identifying internal Hom with tensoring by the dual of `E`
and using the tensor comparison with that quasicoherent dual as left factor. The proof
uses `TauCeti.ihomIsoTensorLeft` and `CategoryTheory.Functor.mapExactPairing` to transport
the existing exact pairing through pullback on quasicoherent sheaves.

## References

* The Stacks Project, Tag 0C6I (base change for sheaf Hom).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Functor
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}} (E : FiniteLocallyFreeSheaf Y) (f : X ⟶ Y)

/-- The canonical base-change comparison for internal Hom from a finite locally free sheaf.
It is natural in arbitrary target sheaves of modules. -/
def pullbackInternalHomComparison :
    ihom E.obj ⋙ Scheme.Modules.pullback f ⟶
      Scheme.Modules.pullback f ⋙ ihom ((Scheme.Modules.pullback f).obj E.obj) :=
  (mateEquiv (ihom.adjunction E.obj)
    (ihom.adjunction ((Scheme.Modules.pullback f).obj E.obj))
    (.mk _ _ _ _ (Scheme.Modules.pullbackTensorLeftIso f E.obj).inv)).natTrans

/-- Evaluation after the base-change comparison is the pullback of evaluation, preceded by
the inverse canonical tensor comparison. This characterizes the base-change map. -/
@[reassoc (attr := simp)]
theorem pullbackInternalHomComparison_ev (F : Y.Modules) :
    (Scheme.Modules.pullback f).obj E.obj ◁ (pullbackInternalHomComparison E f).app F ≫
        (ihom.ev ((Scheme.Modules.pullback f).obj E.obj)).app
          ((Scheme.Modules.pullback f).obj F) =
      inv (δ (Scheme.Modules.pullback f) E.obj ((ihom E.obj).obj F)) ≫
        (Scheme.Modules.pullback f).map ((ihom.ev E.obj).app F) := by
  have h := mateEquiv_counit (ihom.adjunction E.obj)
    (ihom.adjunction ((Scheme.Modules.pullback f).obj E.obj))
    (.mk _ _ _ _ (Scheme.Modules.pullbackTensorLeftIso f E.obj).inv) F
  -- Express the mate equation using module whiskering and evaluation, rather than
  -- `tensorLeft.map`, `TwoSquare.app`, and the adjunction counits.
  change (Scheme.Modules.pullback f).obj E.obj ◁
      (pullbackInternalHomComparison E f).app F ≫
        (ihom.ev ((Scheme.Modules.pullback f).obj E.obj)).app
          ((Scheme.Modules.pullback f).obj F) =
    (Scheme.Modules.pullbackTensorLeftIso f E.obj).inv.app
      ((ihom E.obj).obj F) ≫ (Scheme.Modules.pullback f).map ((ihom.ev E.obj).app F) at h
  have hd : (Scheme.Modules.pullbackTensorLeftIso f E.obj).inv.app
      ((ihom E.obj).obj F) = inv (δ (Scheme.Modules.pullback f) E.obj
        ((ihom E.obj).obj F)) := by
    apply IsIso.eq_inv_of_inv_hom_id
    rw [← Scheme.Modules.pullbackTensorLeftIso_hom_app]
    exact (Scheme.Modules.pullbackTensorLeftIso f E.obj).inv_hom_id_app _
  exact h.trans (congrArg (· ≫ (Scheme.Modules.pullback f).map
    ((ihom.ev E.obj).app F)) hd)

/-- The base-change comparison is obtained by currying the pullback of evaluation, after
inverting the canonical tensor comparison. -/
theorem pullbackInternalHomComparison_app_eq_curry (F : Y.Modules) :
    (pullbackInternalHomComparison E f).app F =
      curry (inv (δ (Scheme.Modules.pullback f) E.obj ((ihom E.obj).obj F)) ≫
        (Scheme.Modules.pullback f).map ((ihom.ev E.obj).app F)) := by
  exact (curry_uncurry _).symm.trans
    (congrArg curry (pullbackInternalHomComparison_ev E f F))

/-- The internal-Hom dual of `E` forms an exact pairing with `E` in sheaves of modules. -/
local instance : ExactPairing (dual E).obj E.obj :=
  exactPairingOfIsIsoDualTensorIhom (Y := E.obj)

/-- Restrict the dual pairing of `E` to quasicoherent sheaves. -/
local instance : ExactPairing ((toQuasicoherent Y).obj (dual E))
    ((toQuasicoherent Y).obj E) :=
  @ObjectProperty.exactPairingFullSubcategory Y.Modules _ _ _
    (Scheme.Modules.isMonoidal_isQuasicoherent Y) _ _
    (inferInstanceAs (ExactPairing (dual E).obj E.obj))

/-- Pullback transports the quasicoherent dual pairing to sheaves of modules on `X`. -/
local instance : ExactPairing ((Scheme.Modules.pullback f).obj (dual E).obj)
    ((Scheme.Modules.pullback f).obj E.obj) :=
  (((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
    Scheme.Modules.pullback f).mapExactPairing
      ((toQuasicoherent Y).obj (dual E)) ((toQuasicoherent Y).obj E))

/-- The canonical internal-Hom base-change comparison is invertible for every scheme morphism
when its source is finite locally free, without a quasicoherence assumption on the target. -/
instance isIso_pullbackInternalHomComparison : IsIso (pullbackInternalHomComparison E f) := by
  have : (dual E).obj.IsQuasicoherent := ((toQuasicoherent Y).obj (dual E)).property
  let P := Scheme.Modules.pullback f
  -- Internal Hom is tensoring by the dual on both schemes; the intervening tensor
  -- comparison is invertible even for an arbitrary right factor.
  let i : ihom E.obj ⋙ P ≅ P ⋙ ihom (P.obj E.obj) :=
    isoWhiskerRight (ihomIsoTensorLeft (dual E).obj E.obj) P ≪≫
      Scheme.Modules.pullbackTensorLeftIso f (dual E).obj ≪≫
        isoWhiskerLeft P (ihomIsoTensorLeft (P.obj (dual E).obj) (P.obj E.obj)).symm
  have hi (F : Y.Modules) :
      P.obj E.obj ◁ i.hom.app F ≫ (ihom.ev (P.obj E.obj)).app (P.obj F) =
        inv (δ P E.obj ((ihom E.obj).obj F)) ≫ P.map ((ihom.ev E.obj).app F) := by
    rw [← cancel_epi (δ P E.obj ((ihom E.obj).obj F)), IsIso.hom_inv_id_assoc]
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
    have he : ε_ (P.obj (dual E).obj) (P.obj E.obj) =
        inv (δ P E.obj (dual E).obj) ≫ P.map (ε_ (dual E).obj E.obj) ≫ η P := by
      have h := Functor.mapExactPairing_evaluation
        (F := ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ P))
        ((toQuasicoherent Y).obj (dual E)) ((toQuasicoherent Y).obj E)
      rw [Scheme.Modules.pullbackToModules_η, ← Scheme.Modules.pullback_η] at h
      -- Read the composite functor on underlying module maps before rewriting the
      -- full-subcategory evaluation; this avoids mixing the two category instances.
      change ε_ (P.obj (dual E).obj) (P.obj E.obj) =
        μ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ P)
          ((toQuasicoherent Y).obj E) ((toQuasicoherent Y).obj (dual E)) ≫
          P.map ((ε_ ((toQuasicoherent Y).obj (dual E))
            ((toQuasicoherent Y).obj E)).hom) ≫ η P at h
      erw [ObjectProperty.exactPairingFullSubcategory_evaluation_hom (C := Y.Modules)] at h
      rw [← Functor.Monoidal.inv_δ] at h
      have hd : inv (δ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ P)
          ((toQuasicoherent Y).obj E) ((toQuasicoherent Y).obj (dual E))) =
          inv (δ P E.obj (dual E).obj) :=
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
  have h : (pullbackInternalHomComparison E f) = i.hom := by
    apply NatTrans.ext
    funext F
    apply uncurry_injective
    exact (pullbackInternalHomComparison_ev E f F).trans (hi F).symm
  rw [h]
  infer_instance

/-- Arbitrary pullback commutes with internal Hom from a finite locally free sheaf, naturally
in every target sheaf of modules. -/
def pullbackInternalHomIso :
    ihom E.obj ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback f ⋙ ihom ((Scheme.Modules.pullback f).obj E.obj) :=
  asIso (pullbackInternalHomComparison E f)

/-- The forward map of the base-change isomorphism is the canonical comparison. -/
@[simp]
theorem pullbackInternalHomIso_hom :
    (pullbackInternalHomIso E f).hom = pullbackInternalHomComparison E f :=
  (rfl)

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
