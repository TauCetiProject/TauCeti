/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.InternalHom.Evaluation
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace.InternalHom
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace.FunctorOfPoints

/-!
# Pullback of points of the internal-Hom bundle

Precomposition on the points of the internal-Hom bundle is pullback of bundle maps, using
the canonical comparison between composite and successive pullback.
-/

public section

open CategoryTheory MonoidalClosed

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.Modules

universe u

variable {X Y Z : Scheme.{u}}

/-- The points-to-morphisms equivalence of the internal-Hom bundle takes precomposition to
pullback of module maps. The composite-pullback isomorphism transports both endpoints. -/
theorem totalSpaceIhomHomEquiv_comp (E F : FiniteLocallyFreeSheaf Z)
    (q : Y ⟶ Z) (g : X ⟶ Y) {q' : X ⟶ Z} (h : g ≫ q = q')
    (t : Over.mk q ⟶ (MorphismProperty.Over.forget _ _ Z).obj
      ((totalSpaceScheme Z).obj ((ihom E).obj F))) :
    totalSpaceIhomHomEquiv E F (Over.mk q') (Over.homMk (V := Over.mk q) g h ≫ t) =
      ((pullbackComp g q ≪≫ pullbackCongr h).inv.app E.obj) ≫
        (pullback g).map (totalSpaceIhomHomEquiv E F (Over.mk q) t) ≫
      ((pullbackComp g q ≪≫ pullbackCongr h).hom.app F.obj) := by
  subst q'
  let g' : Over.mk (g ≫ q) ⟶ Over.mk q := Over.homMk g rfl
  have hs := totalSpaceHomEquiv_comp ((ihom E).obj F) g' t
  have hcomp : pullbackCongr (Over.w g') = Iso.refl _ := rfl
  rw [hcomp, Iso.refl_hom, NatTrans.id_app] at hs
  -- The slice morphism `g'` has underlying morphism `g`.
  change totalSpaceHomEquiv _ _ (g' ≫ t) =
    (pullbackObjUnitIso g).inv ≫ (pullback g).map (totalSpaceHomEquiv _ _ t) ≫
      (pullbackComp g q).hom.app ((ihom E).obj F).obj ≫ 𝟙 _ at hs
  simp only [Category.comp_id] at hs
  rw [totalSpaceIhomHomEquiv_apply, hs, totalSpaceIhomHomEquiv_apply,
    g.pullback_map_uncurry']
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom,
    Iso.trans_inv, Iso.trans_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
  -- Compare curried maps, after cancelling the source comparison isomorphism.
  apply (Iso.eq_inv_comp ((pullbackComp g q).app E.obj)).mpr
  apply curry'_injective
  rw [← curry'_pre_app, ← curry'_ihom_map, curry'_uncurry', curry'_uncurry']
  -- Normalize the slice projections before applying pullback composition coherence.
  let s := totalSpaceHomEquiv ((ihom E).obj F) (Over.mk q) t
  change (((pullbackObjUnitIso g).inv ≫ (pullback g).map s ≫
      (pullbackComp g q).hom.app ((ihom E).obj F).obj) ≫
        ((pullback (g ≫ q)).ihomComparison E.obj).app F.obj) ≫
          (pre ((pullbackComp g q).hom.app E.obj)).app ((pullback (g ≫ q)).obj F.obj) =
      ((pullbackObjUnitIso g).inv ≫
        (pullback g).map (s ≫ ((pullback q).ihomComparison E.obj).app F.obj) ≫
          ((pullback g).ihomComparison ((pullback q).obj E.obj)).app
            ((pullback q).obj F.obj)) ≫
            (ihom ((pullback g).obj ((pullback q).obj E.obj))).map
              ((pullbackComp g q).hom.app F.obj)
  let p := (pullbackObjUnitIso g).inv
  let a := (pullback g).map s
  let b := (pullbackComp g q).hom.app ((ihom E.obj).obj F.obj)
  let d := ((pullback (g ≫ q)).ihomComparison E.obj).app F.obj
  let n := ((pullback q).ihomComparison E.obj).app F.obj
  let b' := ((pullback g).ihomComparison ((pullback q).obj E.obj)).app ((pullback q).obj F.obj)
  let d' := (ihom ((pullback g).obj ((pullback q).obj E.obj))).map
    ((pullbackComp g q).hom.app F.obj)
  let e := (pre ((pullbackComp g q).hom.app E.obj)).app ((pullback (g ≫ q)).obj F.obj)
  have hl : ((p ≫ a ≫ b) ≫ d) ≫ e = p ≫ a ≫ b ≫ d ≫ e := by
    simp only [Category.assoc]
    exact congrArg (p ≫ ·) (Category.assoc a b (d ≫ e))
  have hr : (p ≫ (pullback g).map (s ≫ n) ≫ b') ≫ d' =
      p ≫ a ≫ (pullback g).map n ≫ b' ≫ d' := by
    simpa only [Category.assoc] using
      congrArg (fun m ↦ p ≫ m ≫ b' ≫ d') ((pullback g).map_comp s n)
  exact hl.trans ((congrArg (p ≫ a ≫ ·)
    (pullback_ihomComparison_comp g q E.obj F.obj).symm).trans hr.symm)

end TauCeti.AlgebraicGeometry
