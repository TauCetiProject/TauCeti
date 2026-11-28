/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.ModCat.Flat.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import TauCeti.CategoryTheory.Preadditive.ModCat.Evaluation

/-!
# Filtered colimits and coproducts of flat modules

A finite relation in a filtered colimit can be lifted to a common stage of the diagram.
If the stage is flat, its trivialization maps to the colimit. The argument uses the
equational criterion of Oberst and Röhrl, *Flat and coherent functors*, Theorem 3.2 (4).
Mitchell, *Rings with several objects*, §10, p. 48, gives closure under directed colimits
using tensor products for small additive categories. The equational proof applies to
an arbitrary preadditive category and follows the pointwise lifting argument in
`Module.Flat.of_isColimit`.

Trivializations add and transport along module morphisms, which gives closure
under binary biproducts. Small coproducts are filtered colimits of their finite
subcoproducts.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The binary biproduct of flat modules is flat. -/
instance flat_biprod (F G : ModCat.{w} C) [F.Flat] [G.Flat] : (F ⊞ G).Flat where
  isTrivialRelation {X n Y} β y h := by
    let p : F ⊞ G ⟶ F := biprod.fst
    let q : F ⊞ G ⟶ G := biprod.snd
    let i : F ⟶ F ⊞ G := biprod.inl
    let j : G ⟶ F ⊞ G := biprod.inr
    have hp : ∑ l, F.obj.map (β l).op (p.hom.app (op (Y l)) (y l)) = 0 := by
      rw [← map_relation_sum, h, map_zero]
    have hq : ∑ l, G.obj.map (β l).op (q.hom.app (op (Y l)) (y l)) = 0 := by
      rw [← map_relation_sum, h, map_zero]
    have hsum (l : Fin n) :
        i.hom.app (op (Y l)) (p.hom.app (op (Y l)) (y l)) +
          j.hom.app (op (Y l)) (q.hom.app (op (Y l)) (y l)) = y l := by
      have ht : p ≫ i + q ≫ j = 𝟙 (F ⊞ G) := biprod.total
      have hadd : (p ≫ i + q ≫ j).hom = (p ≫ i).hom + (q ≫ j).hom := by
        simpa only [ObjectProperty.ι_map] using
          (additiveFunctor Cᵒᵖ AddCommGrpCat.{w}).ι.map_add (f := p ≫ i) (g := q ≫ j)
      simpa only [hadd, ObjectProperty.FullSubcategory.comp_hom,
        ObjectProperty.FullSubcategory.id_hom, NatTrans.app_add, NatTrans.comp_app, NatTrans.id_app,
        AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
        congrArg (fun f : F ⊞ G ⟶ F ⊞ G ↦ f.hom.app (op (Y l)) (y l)) ht
    simpa only [hsum] using
      ((Flat.isTrivialRelation β _ hp).map i).add ((Flat.isTrivialRelation β _ hq).map j)

/-- A filtered colimit of flat modules is flat when the indexing category is essentially
small in the value universe. -/
theorem Flat.of_isColimit {J : Type*} [Category* J] [IsFiltered J] [EssentiallySmall.{w} J]
    {D : J ⥤ ModCat.{w} C} [∀ j, (D.obj j).Flat] {c : Cocone D} (hc : IsColimit c) :
    c.pt.Flat where
  isTrivialRelation {X n Y} β y h := by
    classical
    let e := (equivSmallModel.{w} J).symm
    have := IsFiltered.of_equivalence e.symm
    have (T : C) : PreservesColimitsOfShape J (forgetEval.{w} T) :=
      preservesColimitsOfShape_of_equiv e _
    let c' (T : C) := (forgetEval T).mapCocone c
    have hc' (T : C) : IsColimit (c' T) := isColimitOfPreserves (forgetEval T) hc
    let ι (j : J) : D.obj j ⟶ c.pt := c.ι.app j
    have hι (T : C) (j : J) (x : (D.obj j).obj.obj (op T)) :
        (c' T).ι.app j x = (ι j).hom.app (op T) x := by
      simpa only [c', Functor.mapCocone_ι_app] using forgetEval_map_apply T (ι j) x
    have hmap (T : C) {i j : J} (g : i ⟶ j) (x : (D.obj i).obj.obj (op T)) :
        (D ⋙ forgetEval T).map g x = (D.map g).hom.app (op T) x := by
      simpa only [Functor.comp_map] using forgetEval_map_apply T (D.map g) x
    have hleg (T : C) {i j : J} (g : i ⟶ j) (x : (D.obj i).obj.obj (op T)) :
        (ι j).hom.app (op T) ((D.map g).hom.app (op T) x) = (ι i).hom.app (op T) x := by
      rw [← hmap T g x, ← hι T j, ← hι T i, ← (c' T).w g, types_comp_apply]
    choose j a ha using fun l ↦ Types.jointly_surjective_of_isColimit (hc' (Y l)) (y l)
    let O := Finset.univ.image j
    obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists O
    let f (l : Fin n) : j l ⟶ k := (hk (Finset.mem_image_of_mem j (Finset.mem_univ l))).some
    let b (l : Fin n) := (D.map (f l)).hom.app (op (Y l)) (a l)
    have hb (l : Fin n) : (ι k).hom.app (op (Y l)) (b l) = y l :=
      (hleg (Y l) (f l) (a l)).trans ((hι (Y l) (j l) (a l)).symm.trans (ha l))
    let s : (D.obj k).obj.obj (op X) := ∑ l, (D.obj k).obj.map (β l).op (b l)
    have hk₀ : (c' X).ι.app k s = (c' X).ι.app k (0 : (D.obj k).obj.obj (op X)) := by
      simp only [hι, s, map_relation_sum, hb, h, map_zero]
    obtain ⟨m, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff' (hc' X) _ _).mp hk₀
    let b' (l : Fin n) := (D.map g).hom.app (op (Y l)) (b l)
    have hm : ∑ l, (D.obj m).obj.map (β l).op (b' l) = 0 := by
      simpa only [hmap, s, map_relation_sum, map_zero, b'] using hg
    have hb' (l : Fin n) : (ι m).hom.app (op (Y l)) (b' l) = y l :=
      (hleg (Y l) g (b l)).trans (hb l)
    simpa only [hb'] using (Flat.isTrivialRelation β b' hm).map (ι m)

instance : (flat.{w} C).IsClosedUnderBinaryCoproducts where
  colimitsOfShape_le := by
    rintro P ⟨d⟩
    have hF : (d.diag.obj ⟨WalkingPair.left⟩).Flat := d.prop_diag_obj _
    have hG : (d.diag.obj ⟨WalkingPair.right⟩).Flat := d.prop_diag_obj _
    let e := (diagramIsoPair d.diag).symm
    exact Flat.of_iso ((biprod.isoCoprod _ _) ≪≫ HasColimit.isoOfNatIso e ≪≫
      colimit.isoColimitCocone ⟨_, d.isColimit⟩)

instance : (flat.{w} C).IsClosedUnderFiniteCoproducts :=
  .mk'

instance {J : Type*} [Category* J] [IsFiltered J] [EssentiallySmall.{w} J] :
    (flat.{w} C).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro P ⟨d⟩
    have : ∀ j, (d.diag.obj j).Flat := d.prop_diag_obj
    exact Flat.of_isColimit d.isColimit

/-- A small coproduct of flat modules is flat. -/
instance flat_sigma {ι : Type w} (F : ι → ModCat.{w} C) [∀ i, (F i).Flat] : (∐ F).Flat := by
  let D := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor F)
  have (S : Finset (Discrete ι)) : (D.obj S).Flat :=
    (flat C).prop_coproduct (fun s ↦ inferInstanceAs (F s.val.as).Flat)
  exact Flat.of_isColimit (D := D) (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone F)

end TauCeti.ModCat
