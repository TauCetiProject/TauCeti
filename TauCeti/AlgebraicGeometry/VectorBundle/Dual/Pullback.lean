/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.InternalHom.Coherence
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Bidual
public import TauCeti.AlgebraicGeometry.VectorBundle.Functoriality
public import TauCeti.AlgebraicGeometry.VectorBundle.InternalHom.Pullback

/-!
# Pullback of dual vector bundles

For a finite locally free sheaf `E`, pulling back its dual agrees with taking the dual of
its pullback. The comparison uses the canonical base-change map for internal Hom and the
canonical identification of the pullback of the structure sheaf with the structure sheaf.
The comparison is natural in `E`, so it assembles into a natural isomorphism between
dualizing then pulling back and pulling back then dualizing. It is also coherent: along the
identity it is the identity comparison of pullback, and along a composite `f ≫ g` it is the
comparison along `g` followed by the comparison along `f`, through the composition comparison of
pullback (`pullbackDualIso_hom_id` and `pullbackDualIso_hom_comp`).

## References

* The Stacks Project, Tag 0C6I (base change for sheaf Hom).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (E : FiniteLocallyFreeSheaf Y)

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
  -- Restate dualization by `homMk`, so that the endpoints are syntactically the `dual` objects
  -- of `pullbackDualIso` rather than the definitionally equal `dualFunctor.obj` objects.
  have h : (pullback f).map (ObjectProperty.homMk ((pre g.hom).app (𝟙_ Y.Modules))) ≫
        (pullbackDualIso f E).hom =
      (pullbackDualIso f F).hom ≫
        ObjectProperty.homMk ((pre ((pullback f).map g).hom).app (𝟙_ X.Modules)) := by
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, pullback_map_hom,
      ObjectProperty.homMk_hom, pullbackDualIso_hom_hom, pre_map, NatTrans.comp_app,
      pre_eqToHom_app, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.assoc]
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

/-- Along the identity, the dual pullback comparison is the identity comparison of pullback:
composed with the dual of the inverse identity comparison of `E`, it is the identity comparison
of `dual E`. -/
@[reassoc]
theorem pullbackDualIso_hom_id (E : FiniteLocallyFreeSheaf X) :
    (pullbackDualIso (𝟙 X) E).hom ≫ dualFunctor.map ((pullbackId X).inv.app E).op =
      (pullbackId X).hom.app (dual E) := by
  -- Restate dualization by `homMk`, as in `pullbackDualIso_naturality`, so that the composite is
  -- formed between the `dual` objects of `pullbackDualIso`.
  have h : (pullbackDualIso (𝟙 X) E).hom ≫
      ObjectProperty.homMk ((pre ((pullbackId X).inv.app E).hom).app (𝟙_ X.Modules)) =
        (pullbackId X).hom.app (dual E) := by
    apply ObjectProperty.hom_ext
    dsimp only [Functor.id_obj]
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      pullbackDualIso_hom_hom, pullbackId_inv_app_hom, pullbackId_app_hom_hom,
      Scheme.Modules.pullbackObjUnitIso_id, Category.assoc, pullbackIhomComparison_id_assoc,
      pre_map, NatTrans.comp_app, pre_eqToHom_app, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id_app]
    simp only [Functor.id_obj, pre_id, NatTrans.id_app, Category.comp_id]
  exact h

/-- Along a composite `f ≫ g`, the dual pullback comparison is the comparison along `g` followed by
the comparison along `f`: composed with the dual of the composition comparison of `E`, it is the
inverse composition comparison of `dual E` followed by the pullback along `f` of the comparison
along `g` and the comparison along `f`. -/
@[reassoc]
theorem pullbackDualIso_hom_comp (g : Y ⟶ Z) (E : FiniteLocallyFreeSheaf Z) :
    (pullbackDualIso (f ≫ g) E).hom ≫ dualFunctor.map ((pullbackComp f g).hom.app E).op =
      (pullbackComp f g).inv.app (dual E) ≫ (pullback f).map (pullbackDualIso g E).hom ≫
        (pullbackDualIso f ((pullback g).obj E)).hom := by
  -- As in `pullbackDualIso_hom_id`, restate dualization by `homMk`.
  have h : (pullbackDualIso (f ≫ g) E).hom ≫
      ObjectProperty.homMk ((pre ((pullbackComp f g).hom.app E).hom).app (𝟙_ X.Modules)) =
      (pullbackComp f g).inv.app (dual E) ≫ (pullback f).map (pullbackDualIso g E).hom ≫
        (pullbackDualIso f ((pullback g).obj E)).hom := by
    apply ObjectProperty.hom_ext
    dsimp only [Functor.comp_obj]
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      pullbackDualIso_hom_hom, pullbackComp_inv_app_hom, pullbackComp_app_hom_hom,
      pullback_map_hom, Functor.map_comp, eqToHom_map, Category.assoc, pre_map,
      NatTrans.comp_app, pre_eqToHom_app, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    -- The comparison along `f` is taken at the sheaf underlying `(pullback g).obj E`. Transport it
    -- to the module pullback of `E.obj`: the two agree by `pullback_obj_obj`, but `pullback` is not
    -- exposed, so the equality cannot be used definitionally here.
    have hM (M : Y.Modules) [M.IsQuasicoherent] (e : M = (Scheme.Modules.pullback g).obj E.obj)
        {T : X.Modules}
        (p : (Scheme.Modules.pullback f).obj
          ((ihom ((Scheme.Modules.pullback g).obj E.obj)).obj (𝟙_ Y.Modules)) =
            (Scheme.Modules.pullback f).obj ((ihom M).obj (𝟙_ Y.Modules)))
        (q : (ihom ((Scheme.Modules.pullback f).obj M)).obj (𝟙_ X.Modules) = T) :
        eqToHom p ≫ (pullbackIhomComparison M f).app (𝟙_ Y.Modules) ≫
          (ihom ((Scheme.Modules.pullback f).obj M)).map
            (Scheme.Modules.pullbackObjUnitIso f).hom ≫ eqToHom q =
        (pullbackIhomComparison ((Scheme.Modules.pullback g).obj E.obj) f).app (𝟙_ Y.Modules) ≫
          (ihom ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj E.obj))).map
            (Scheme.Modules.pullbackObjUnitIso f).hom ≫ eqToHom (by rw [← q, e]) := by
      subst e
      simp only [eqToHom_refl, Category.id_comp]
    rw [hM _ (pullback_obj_obj g E)]
    -- On module pullbacks, combine the internal-Hom coherence `pullbackIhomComparison_comp` with
    -- the composition coherence `pullbackObjUnitIso_comp` of the structure-sheaf comparison.
    have hn := (pullbackIhomComparison ((Scheme.Modules.pullback g).obj E.obj) f).naturality
      (Scheme.Modules.pullbackObjUnitIso g).hom
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn
    have hu : (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackObjUnitIso g).hom ≫
        (Scheme.Modules.pullbackObjUnitIso f).hom =
          (Scheme.Modules.pullbackComp f g).hom.app (𝟙_ Z.Modules) ≫
            (Scheme.Modules.pullbackObjUnitIso (f ≫ g)).hom := by
      rw [← Scheme.Modules.pullbackObjUnitIso_comp, Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% hn, ← Functor.map_comp_assoc, hu, Functor.map_comp_assoc,
      pullbackIhomComparison_comp_assoc, Iso.inv_hom_id_app_assoc, ← NatTrans.naturality_assoc]
  exact h

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
