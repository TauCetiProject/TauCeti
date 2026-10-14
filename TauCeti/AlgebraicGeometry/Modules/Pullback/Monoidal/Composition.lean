/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Basic

/-!
# Monoidal composition coherence of quasicoherent pullback

The canonical comparison between successive pullbacks of quasicoherent sheaves and pullback
along the composite scheme morphism respects the strong symmetric monoidal structures.
Consequently, composing changes of base is compatible with tensor products and structure sheaves,
without flatness or finiteness assumptions.

The unit and tensor coherence rules simplify before the generic `comp_η` and `comp_δ`
equations expand the composite functor and erase the expression these rules match.

The compatibility restricts `Scheme.Modules.pullback_comp_δ` and
`Scheme.Modules.pullbackObjUnitIso_comp` to quasicoherent sheaves. Mathlib's
`CategoryTheory.NatTrans.IsMonoidal` then supplies compatibility for the inverse comparison.
-/

public section

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti.AlgebraicGeometry.QuasicoherentSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

private lemma pullbackComp_eqToHom (A : QuasicoherentSheaf Z) :
    eqToHom (pullback_obj_obj f ((pullback g).obj A)) ≫
        (Scheme.Modules.pullback f).map (eqToHom (pullback_obj_obj g A)) =
      eqToHom (pullbackComp_obj_obj f g A) := by
  -- Full-subcategory objects expose `SheafOfModules X.ringCatSheaf`, while the functor uses
  -- `X.Modules`. Identifying these also unfolds `TopCat.Sheaf` to the sheaf category on
  -- `Opens.grothendieckTopology`, beyond the transparency used by `rw` and `simp`.
  erw [eqToHom_map, eqToHom_trans]

private lemma pullbackComp_unit_transport :
  let U := 𝟙_ (QuasicoherentSheaf Z)
  let H : Y.Modules ⥤ X.Modules := Scheme.Modules.pullback f
  let G : Y.Modules := ((pullback g).obj U).obj
  let S : X.Modules := ((pullback f).obj ((pullback g).obj U)).obj
  let A : X.Modules := ((pullback f).obj (𝟙_ (QuasicoherentSheaf Y))).obj
  let C : X.Modules := ((pullback (f ≫ g)).obj U).obj
  -- Explicit module carriers keep the full-subcategory's unfolded sheaf presentation out of
  -- the categorical computations below.
  let eS : S ≅ H.obj G := eqToIso (pullback_obj_obj f ((pullback g).obj U))
  let eG : G ≅ (Scheme.Modules.pullback g).obj (𝟙_ Z.Modules) :=
    eqToIso (pullback_obj_obj g U)
  let eU : A ≅ H.obj (𝟙_ Y.Modules) :=
    eqToIso (pullback_obj_obj f (𝟙_ (QuasicoherentSheaf Y)))
  let eD : S ≅ H.obj ((Scheme.Modules.pullback g).obj (𝟙_ Z.Modules)) :=
    eqToIso (pullbackComp_obj_obj f g U)
  let eC : C ≅ (Scheme.Modules.pullback (f ≫ g)).obj (𝟙_ Z.Modules) :=
    eqToIso (pullback_obj_obj (f ≫ g) U)
  let c := Scheme.Modules.pullbackComp f g
  (eS.hom ≫ H.map eG.hom = eD.hom) →
  (eS.hom ≫ H.map (eG.hom ≫ (Scheme.Modules.pullbackObjUnitIso g).hom) ≫ eU.inv) ≫
      (eU.hom ≫ (Scheme.Modules.pullbackObjUnitIso f).hom) =
    (eD.hom ≫ c.hom.app (𝟙_ Z.Modules) ≫ eC.inv) ≫
      (eC.hom ≫ (Scheme.Modules.pullbackObjUnitIso (f ≫ g)).hom) := by
  intro U H G S A C eS eG eU eD eC c he
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
  rw [← Category.assoc, he]
  rw [cancel_epi eD.hom, ← cancel_epi (c.inv.app (𝟙_ Z.Modules))]
  simp only [Iso.inv_hom_id_app_assoc]
  exact Scheme.Modules.pullbackObjUnitIso_comp f g

private lemma pullbackComp_tensor_transport (E F : QuasicoherentSheaf Z) :
  -- First transport the desired equation to explicitly named module carriers.
  let H : Y.Modules ⥤ X.Modules := Scheme.Modules.pullback f
  let K : Z.Modules ⥤ Y.Modules := Scheme.Modules.pullback g
  let M (A : QuasicoherentSheaf Z) : Z.Modules := A.obj
  let G (A : QuasicoherentSheaf Z) : Y.Modules := ((pullback g).obj A).obj
  let S (A : QuasicoherentSheaf Z) : X.Modules :=
    ((pullback f).obj ((pullback g).obj A)).obj
  let C (A : QuasicoherentSheaf Z) : X.Modules := ((pullback (f ≫ g)).obj A).obj
  let T : X.Modules := ((pullback f).obj ((pullback g).obj E ⊗ (pullback g).obj F)).obj
  -- The named carriers fix the ambient module category for all tensor and composition laws.
  let eS (A) : S A ≅ H.obj (G A) := eqToIso (pullback_obj_obj f ((pullback g).obj A))
  let eG (A) : G A ≅ K.obj (M A) := eqToIso (pullback_obj_obj g A)
  let eD (A) : S A ≅ H.obj (K.obj (M A)) := eqToIso (pullbackComp_obj_obj f g A)
  let eC (A) : C A ≅ (Scheme.Modules.pullback (f ≫ g)).obj (M A) :=
    eqToIso (pullback_obj_obj (f ≫ g) A)
  let eT : T ≅ H.obj (G E ⊗ G F) :=
    eqToIso (pullback_obj_obj f ((pullback g).obj E ⊗ (pullback g).obj F))
  let c := Scheme.Modules.pullbackComp f g
  (∀ A, (eS A).hom ≫ H.map (eG A).hom = (eD A).hom) →
      (eS (E ⊗ F)).hom ≫
          H.map ((eG (E ⊗ F)).hom ≫ δ K (M E) (M F) ≫
            ((eG E).inv ⊗ₘ (eG F).inv)) ≫ eT.inv ≫
        (eT.hom ≫ δ H (G E) (G F) ≫ ((eS E).inv ⊗ₘ (eS F).inv)) ≫
        (((eD E).hom ≫ c.hom.app (M E) ≫ (eC E).inv) ⊗ₘ
          ((eD F).hom ≫ c.hom.app (M F) ≫ (eC F).inv)) =
      ((eD (E ⊗ F)).hom ≫ c.hom.app (M E ⊗ M F) ≫ (eC (E ⊗ F)).inv) ≫
        (eC (E ⊗ F)).hom ≫ δ (Scheme.Modules.pullback (f ≫ g)) (M E) (M F) ≫
          ((eC E).inv ⊗ₘ (eC F).inv) := by
  intro H K M G S C T eS eG eD eC eT c he
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
  -- Naturality moves the inner object identifications through the outer tensorator;
  -- cancellation then leaves the existing module-pullback composition equation.
  rw [← Category.assoc, he,
    ← Functor.OplaxMonoidal.δ_natural_assoc H (eG E).inv (eG F).inv]
  simp only [tensorHom_comp_tensorHom]
  rw [← he E, ← he F]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_map_assoc]
  rw [← tensorHom_comp_tensorHom (c.hom.app (M E)) (c.hom.app (M F))
    (eC E).inv (eC F).inv]
  rw [cancel_epi (eD (E ⊗ F)).hom]
  -- Re-anchor the tensor expressions in `X.Modules`. Rewriting `tensorObj_obj` instead
  -- leaves the unfolded sheaf presentation, on which monoidal instance search fails.
  change H.map (δ K (M E) (M F)) ≫ δ H (K.obj (M E)) (K.obj (M F)) ≫
      (c.hom.app (M E) ⊗ₘ c.hom.app (M F)) ≫ ((eC E).inv ⊗ₘ (eC F).inv) =
    c.hom.app (M E ⊗ M F) ≫ δ (Scheme.Modules.pullback (f ≫ g)) (M E) (M F) ≫
      ((eC E).inv ⊗ₘ (eC F).inv)
  simp only [← Category.assoc]
  rw [cancel_mono ((eC E).inv ⊗ₘ (eC F).inv)]
  rw [← cancel_epi (c.inv.app (M E ⊗ M F))]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact (Scheme.Modules.pullback_comp_δ f g (M E) (M F)).symm

/-- The inverse unit comparisons of successive pullbacks agree with the comparison for the
composite morphism through the canonical composition isomorphism. -/
@[reassoc (attr := simp↓)]
theorem pullback_comp_η :
    η (pullback g ⋙ pullback f) =
      (pullbackComp f g).hom.app (𝟙_ (QuasicoherentSheaf Z)) ≫ η (pullback (f ≫ g)) := by
  rw [Functor.OplaxMonoidal.comp_η]
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom]
  rw [pullback_map_hom, pullback_η_hom, pullback_η_hom,
    pullbackComp_hom_app_hom, pullback_η_hom]
  exact pullbackComp_unit_transport f g (pullbackComp_eqToHom f g _)

/-- The inverse tensor comparisons of successive pullbacks agree with the comparison for the
composite morphism through the canonical composition isomorphism. -/
@[reassoc (attr := simp↓)]
theorem pullback_comp_δ (E F : QuasicoherentSheaf Z) :
    δ (pullback g ⋙ pullback f) E F ≫
        ((pullbackComp f g).hom.app E ⊗ₘ (pullbackComp f g).hom.app F) =
      (pullbackComp f g).hom.app (E ⊗ F) ≫ δ (pullback (f ≫ g)) E F := by
  -- Restrict the module equation back using the public full-subcategory comparison laws.
  rw [Functor.OplaxMonoidal.comp_δ]
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  -- The ambient carrier must be explicit to avoid the unfolded sheaf presentation.
  erw [ObjectProperty.tensorHom_def (C := X.Modules)]
  rw [pullback_map_hom, pullback_δ_hom, pullback_δ_hom,
    pullbackComp_hom_app_hom, pullbackComp_hom_app_hom,
    pullbackComp_hom_app_hom, pullback_δ_hom]
  exact pullbackComp_tensor_transport f g E F (pullbackComp_eqToHom f g)

/-- The canonical composition isomorphism of quasicoherent pullback is monoidal. -/
instance isMonoidal_pullbackComp_hom : NatTrans.IsMonoidal (pullbackComp f g).hom where
  unit := by
    rw [← cancel_mono (η (pullback (f ≫ g)))]
    simp [← pullback_comp_η]
  tensor E F := by
    rw [← cancel_epi (δ (pullback g ⋙ pullback f) E F),
      ← cancel_mono (δ (pullback (f ≫ g)) E F)]
    simp only [Category.assoc, Functor.Monoidal.δ_μ_assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]
    exact (pullback_comp_δ f g E F).symm

end

end TauCeti.AlgebraicGeometry.QuasicoherentSheaf
