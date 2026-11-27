/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import TauCeti.CategoryTheory.Preadditive.ModCat.Flat.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Filtered colimits, coproducts, and retracts of flat modules

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
open scoped ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The pointwise sum of two trivial relations for the same row is trivial. -/
theorem IsTrivialRelation.add {F : ModCat.{w} C} {X : C} {n : ℕ} {Y : Fin n → C}
    {β : ∀ j, X ⟶ Y j} {y y' : ∀ j, F.obj.obj (op (Y j))}
    (h : F.IsTrivialRelation β y) (h' : F.IsTrivialRelation β y') :
    F.IsTrivialRelation β (fun j ↦ y j + y' j) := by
  obtain ⟨m, Z, z, α, hy, hα⟩ := isTrivialRelation_def.mp h
  obtain ⟨m', Z', z', α', hy', hα'⟩ := isTrivialRelation_def.mp h'
  let W : Fin m ⊕ Fin m' → C := Sum.elim Z Z'
  let t : ∀ i, F.obj.obj (op (W i)) := Sum.rec z z'
  let γ : ∀ i j, Y j ⟶ W i := Sum.rec α α'
  have ha : ∀ i : Fin m ⊕ Fin m', ∑ j, β j ≫ γ i j = 0
    | .inl i => hα i
    | .inr i => hα' i
  have hs (j : Fin n) : y j + y' j = ∑ i, F.obj.map (γ i j).op (t i) := by
    rw [Fintype.sum_sum_type]
    exact congrArg₂ (· + ·) (hy j) (hy' j)
  let e : Fin (m + m') ≃ Fin m ⊕ Fin m' := finSumFinEquiv.symm
  refine isTrivialRelation_def.mpr
    ⟨m + m', W ∘ e, fun i ↦ t (e i), fun i ↦ γ (e i), fun j ↦ (hs j).trans ?_, fun i ↦ ha (e i)⟩
  exact (e.sum_comp fun i ↦ F.obj.map (γ i j).op (t i)).symm

/-- A zero module is flat. -/
theorem Flat.of_isZero {F : ModCat.{w} C} (hF : IsZero F) : F.Flat where
  isTrivialRelation {X n Y} β y _ := by
    refine isTrivialRelation_def.mpr
      ⟨0, Fin.elim0, (fun i ↦ i.elim0), (fun i ↦ i.elim0), ?_, fun i ↦ i.elim0⟩
    intro j
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    have hF' := (IsZero.iff_id_eq_zero F).mp hF
    have hz := congrArg (fun f : F ⟶ F ↦ f.hom.app (op (Y j))) hF'
    exact ConcreteCategory.congr_hom hz (y j)

/-- The binary biproduct of flat modules is flat. -/
instance flat_biprod (F G : ModCat.{w} C) [F.Flat] [G.Flat] : (F ⊞ G).Flat where
  isTrivialRelation {X n Y} β y h := by
    let p : F ⊞ G ⟶ F := biprod.fst
    let q : F ⊞ G ⟶ G := biprod.snd
    let i : F ⟶ F ⊞ G := biprod.inl
    let j : G ⟶ F ⊞ G := biprod.inr
    have hp : ∑ l, F.obj.map (β l).op (p.hom.app (op (Y l)) (y l)) = 0 := by
      simpa only [map_sum, p.hom.naturality_apply, map_zero] using
        congrArg (p.hom.app (op X)) h
    have hq : ∑ l, G.obj.map (β l).op (q.hom.app (op (Y l)) (y l)) = 0 := by
      simpa only [map_sum, q.hom.naturality_apply, map_zero] using
        congrArg (q.hom.app (op X)) h
    have hsum (l : Fin n) :
        i.hom.app (op (Y l)) (p.hom.app (op (Y l)) (y l)) +
          j.hom.app (op (Y l)) (q.hom.app (op (Y l)) (y l)) = y l := by
      have ht : p ≫ i + q ≫ j = 𝟙 (F ⊞ G) := biprod.total
      exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app (op (Y l))) ht) (y l)
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
    have := hasColimitsOfShape_of_essentiallySmall J AddCommGrpCat.{w}
    have := preservesColimitsOfShape_of_equiv e (forget AddCommGrpCat.{w})
    let ev (T : C) :=
      (additiveFunctor Cᵒᵖ AddCommGrpCat.{w}).ι ⋙ (evaluation _ _).obj (op T)
    have hc' (T : C) := isColimitOfPreserves (ev T) hc
    let ι (j : J) : D.obj j ⟶ c.pt := c.ι.app j
    choose j a ha using fun l ↦ Concrete.isColimit_exists_rep (D ⋙ ev (Y l)) (hc' (Y l)) (y l)
    let O := Finset.univ.image j
    obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists O
    let f (l : Fin n) : j l ⟶ k := (hk (Finset.mem_image_of_mem j (Finset.mem_univ l))).some
    let b (l : Fin n) := (D.map (f l)).hom.app (op (Y l)) (a l)
    have hb (l : Fin n) : (ι k).hom.app (op (Y l)) (b l) = y l := by
      have hf := congrArg (fun g ↦ g.hom.app (op (Y l))) (c.w (f l))
      exact (ConcreteCategory.congr_hom hf (a l)).trans (ha l)
    have hk₀ : (ι k).hom.app (op X) (∑ l, (D.obj k).obj.map (β l).op (b l)) =
        (ι k).hom.app (op X) 0 := by
      simp only [map_sum, (ι k).hom.naturality_apply, hb, h, map_zero]
    obtain ⟨m, g, g', hg⟩ := Concrete.isColimit_exists_of_rep_eq (D ⋙ ev X) (hc' X) _ _ hk₀
    let b' (l : Fin n) := (D.map g).hom.app (op (Y l)) (b l)
    have hm : ∑ l, (D.obj m).obj.map (β l).op (b' l) = 0 := by
      -- The maps of the evaluated diagram are the components of the module morphisms.
      change (D.map g).hom.app (op X) (∑ l, (D.obj k).obj.map (β l).op (b l)) =
        (D.map g').hom.app (op X) 0 at hg
      simpa only [map_sum, (D.map g).hom.naturality_apply, map_zero, b'] using hg
    have hb' (l : Fin n) : (ι m).hom.app (op (Y l)) (b' l) = y l := by
      have hg' := congrArg (fun f ↦ f.hom.app (op (Y l))) (c.w g)
      exact (ConcreteCategory.congr_hom hg' (b l)).trans (hb l)
    simpa only [hb'] using (Flat.isTrivialRelation β b' hm).map (ι m)

/-- Flatness as an object property on the category of modules. -/
abbrev flat (C : Type u) [Category.{v} C] [Preadditive C] : ObjectProperty (ModCat.{w} C) :=
  Flat

instance : (flat.{w} C).IsStableUnderRetracts where
  of_retract e h := by
    have : Flat _ := h
    exact Flat.of_retract e

instance : (flat.{w} C).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, Flat.of_isZero (isZero_zero _)⟩

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
