/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Bidual
public import TauCeti.AlgebraicGeometry.VectorBundle.InternalHom.Pullback

/-!
# Pullback of dual vector bundles

For a finite locally free sheaf `E`, pulling back its dual agrees with taking the dual of
its pullback. The comparison uses the canonical base-change map for internal Hom and the
canonical identification of the pullback of the structure sheaf with the structure sheaf.
The comparison is natural in `E`, so it assembles into a natural isomorphism between
dualizing then pulling back and pulling back then dualizing.

## References

* The Stacks Project, Tag 0C6I (base change for sheaf Hom).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (E : FiniteLocallyFreeSheaf Y)

/-- Pulling back a finite locally free sheaf's dual is canonically isomorphic to the dual
of its pullback. -/
def pullbackDualIso :
    (pullback f).obj (dual E) ≅ dual ((pullback f).obj E) :=
  ObjectProperty.isoMk _
    (eqToIso (pullback_obj_obj f (dual E)) ≪≫
      (pullbackIhomIso E f).app (𝟙_ Y.Modules) ≪≫
      (ihom ((Scheme.Modules.pullback f).obj E.obj)).mapIso
        (Scheme.Modules.pullbackObjUnitIso f) ≪≫
      eqToIso (congrArg (fun M : X.Modules ↦ (ihom M).obj (𝟙_ X.Modules))
        (pullback_obj_obj f E).symm))

/-- The underlying map is the canonical internal-Hom base-change comparison, followed by
the identification `f* 𝒪_Y ≅ 𝒪_X`. -/
@[simp]
theorem pullbackDualIso_hom_hom :
    (pullbackDualIso f E).hom.hom =
      eqToHom (pullback_obj_obj f (dual E)) ≫
        (pullbackIhomComparison E.obj f).app (𝟙_ Y.Modules) ≫
          (ihom ((Scheme.Modules.pullback f).obj E.obj)).map
            (Scheme.Modules.pullbackObjUnitIso f).hom ≫
              eqToHom (congrArg (fun M : X.Modules ↦ (ihom M).obj (𝟙_ X.Modules))
                (pullback_obj_obj f E).symm) := by
  simp only [pullbackDualIso, ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom,
    Iso.trans_hom, Iso.app_hom, pullbackIhomIso_hom, Functor.mapIso_hom,
    eqToIso.hom]

variable {E} in
/-- The dual pullback comparison is natural in maps of finite locally free sheaves. -/
@[reassoc]
theorem pullbackDualIso_naturality {F : FiniteLocallyFreeSheaf Y} (g : E ⟶ F) :
    (pullback f).map (dualFunctor.map g.op) ≫ (pullbackDualIso f E).hom =
      (pullbackDualIso f F).hom ≫ dualFunctor.map (X := .op ((pullback f).obj F))
        (Y := .op ((pullback f).obj E)) ((pullback f).map g).op := by
  have hpre {A B : X.Modules} (e : A = B) :
      (pre (eqToHom e)).app (𝟙_ X.Modules) = eqToHom (by rw [e]) := by
    subst e
    simp only [eqToHom_refl, pre_id, NatTrans.id_app]
  -- Restate dualization by `homMk`, so that the endpoints are syntactically the `dual` objects
  -- of `pullbackDualIso` rather than the definitionally equal `dualFunctor.obj` objects.
  have h : (pullback f).map (ObjectProperty.homMk ((pre g.hom).app (𝟙_ Y.Modules))) ≫
        (pullbackDualIso f E).hom =
      (pullbackDualIso f F).hom ≫
        ObjectProperty.homMk ((pre ((pullback f).map g).hom).app (𝟙_ X.Modules)) := by
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, pullback_map_hom,
      ObjectProperty.homMk_hom, pullbackDualIso_hom_hom, pre_map, NatTrans.comp_app, hpre,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.assoc]
    rw [pullback_map_pre_app_comp_pullbackIhomComparison_app_assoc, NatTrans.naturality_assoc]
  exact h

/-- Pulling back duals of finite locally free sheaves is naturally isomorphic to dualizing
their pullbacks. -/
def pullbackDualNatIso : dualFunctor ⋙ pullback f ≅ (pullback f).op ⋙ dualFunctor :=
  NatIso.ofComponents (fun E ↦ pullbackDualIso f E.unop)
    fun g ↦ pullbackDualIso_naturality f g.unop

/-- The forward component of the natural dual pullback comparison is `pullbackDualIso`. -/
@[simp]
theorem pullbackDualNatIso_hom_app (E : (FiniteLocallyFreeSheaf Y)ᵒᵖ) :
    (pullbackDualNatIso f).hom.app E = (pullbackDualIso f E.unop).hom :=
  (rfl)

/-- The inverse component of the natural dual pullback comparison is `pullbackDualIso`. -/
@[simp]
theorem pullbackDualNatIso_inv_app (E : (FiniteLocallyFreeSheaf Y)ᵒᵖ) :
    (pullbackDualNatIso f).inv.app E = (pullbackDualIso f E.unop).inv :=
  (rfl)

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
