/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import TauCeti.CategoryTheory.Bicategory.Functor.TwoFiberProduct

/-!
# The 2-fiber product of stacks

Let `α : F ⟶ H`, `β : G ⟶ H` be strong transformations between pseudofunctors
`LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` and `TauCeti.Stack.twoFiberProduct α β` their 2-fiber product. For a
Grothendieck topology `J` on `C`, the 2-fiber product of two stacks over a prestack is a
stack (`twoFiberProduct.isStack`), and that of two prestacks over a prestack is a prestack
(`twoFiberProduct.isPrestack`) (Stacks, Lemma 8.4.6 (026G)). Both rest on statements about a single
family of morphisms `f i : X i ⟶ S`: the descent functor of the 2-fiber product is fully faithful
when those of `F` and `G` are and that of `H` is faithful
(`twoFiberProduct.fullyFaithfulToDescentData`), and essentially surjective when those of `F` and `G`
are and that of `H` is fully faithful (`twoFiberProduct.essSurj_toDescentData`).

## Main declarations

* `TauCeti.Stack.twoFiberProduct.descentDataFst`, `TauCeti.Stack.twoFiberProduct.descentDataSnd`:
  the projections of descent data.
* `TauCeti.Stack.twoFiberProduct.isPrestack`, `TauCeti.Stack.twoFiberProduct.isStack`: the 2-fiber
  product of prestacks (respectively stacks) over a prestack is a prestack (respectively stack).

## References

* [Stacks Project, Lemma 026G](https://stacks.math.columbia.edu/tag/026G)
-/

open CategoryTheory Bicategory Limits CategoricalPullback Opposite
open scoped Pseudofunctor.StrongTrans

universe t u' v' v u

@[expose] public section

/-! ### Descent data of the 2-fiber product -/

namespace TauCeti.Stack.twoFiberProduct

open Pseudofunctor Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
  {F G H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', max u' v'}} (α : F ⟶ H) (β : G ⟶ H)

@[simp]
lemma pullHom_fst ⦃X₁ X₂ : C⦄ ⦃M₁ : (twoFiberProduct α β).obj (.mk (op X₁))⦄
    ⦃M₂ : (twoFiberProduct α β).obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : ((twoFiberProduct α β).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((twoFiberProduct α β).map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (pullHom φ g gf₁ gf₂ hgf₁ hgf₂).fst = pullHom (F := F) φ.fst g gf₁ gf₂ hgf₁ hgf₂ := by
  simp only [pullHom, comp_fst', map_map_fst', mapComp'_hom_app_fst, mapComp'_inv_app_fst]
  -- The two sides differ only in the implicit objects of the compositions.
  rfl

@[simp]
lemma pullHom_snd ⦃X₁ X₂ : C⦄ ⦃M₁ : (twoFiberProduct α β).obj (.mk (op X₁))⦄
    ⦃M₂ : (twoFiberProduct α β).obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : ((twoFiberProduct α β).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((twoFiberProduct α β).map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (pullHom φ g gf₁ gf₂ hgf₁ hgf₂).snd = pullHom (F := G) φ.snd g gf₁ gf₂ hgf₁ hgf₂ := by
  simp only [pullHom, comp_snd', map_map_snd', mapComp'_hom_app_snd, mapComp'_inv_app_snd]
  -- The two sides differ only in the implicit objects of the compositions.
  rfl

variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The first projection of descent data of the 2-fiber product. -/
@[simps]
def descentDataFst : (twoFiberProduct α β).DescentData f ⥤ F.DescentData f where
  obj D :=
    { obj i := (D.obj i).fst
      hom _ q _ _ f₁ f₂ hf₁ hf₂ := (D.hom q f₁ f₂ hf₁ hf₂).fst
      pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
        rw [← pullHom_fst, D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
      hom_self _ q _ g hg := congrArg Hom.fst (D.hom_self q g hg)
      hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
        congrArg Hom.fst (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃) }
  map {D D'} φ :=
    { hom i := (φ.hom i).fst
      comm _ q _ _ f₁ f₂ hf₁ hf₂ := congrArg Hom.fst (φ.comm q f₁ f₂ hf₁ hf₂) }

/-- The second projection of descent data of the 2-fiber product. -/
@[simps]
def descentDataSnd : (twoFiberProduct α β).DescentData f ⥤ G.DescentData f where
  obj D :=
    { obj i := (D.obj i).snd
      hom _ q _ _ f₁ f₂ hf₁ hf₂ := (D.hom q f₁ f₂ hf₁ hf₂).snd
      pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
        rw [← pullHom_snd, D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
      hom_self _ q _ g hg := congrArg Hom.snd (D.hom_self q g hg)
      hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
        congrArg Hom.snd (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃) }
  map {D D'} φ :=
    { hom i := (φ.hom i).snd
      comm _ q _ _ f₁ f₂ hf₁ hf₂ := congrArg Hom.snd (φ.comm q f₁ f₂ hf₁ hf₂) }

@[simp]
lemma toDescentData_obj_hom_fst (M : (twoFiberProduct α β).obj (.mk (op S))) ⦃Y : C⦄
    (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) :
    ((((twoFiberProduct α β).toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂).fst =
      ((F.toDescentData f).obj M.fst).hom q f₁ f₂ hf₁ hf₂ := by
  -- Unfold `toDescentData` on the 2-fiber product, whose comparisons are only definitionally
  -- those of `Pseudofunctor.DescentData.ofObj`.
  change (((twoFiberProduct α β).mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc
    _).inv.toNatTrans.app M ≫ ((twoFiberProduct α β).mapComp' (f i₂).op.toLoc f₂.op.toLoc
      q.op.toLoc _).hom.toNatTrans.app M).fst = _
  rw [comp_fst', mapComp'_inv_app_fst, mapComp'_hom_app_fst]
  rfl

@[simp]
lemma toDescentData_obj_hom_snd (M : (twoFiberProduct α β).obj (.mk (op S))) ⦃Y : C⦄
    (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) :
    ((((twoFiberProduct α β).toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂).snd =
      ((G.toDescentData f).obj M.snd).hom q f₁ f₂ hf₁ hf₂ := by
  -- As for `toDescentData_obj_hom_fst`.
  change (((twoFiberProduct α β).mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc
    _).inv.toNatTrans.app M ≫ ((twoFiberProduct α β).mapComp' (f i₂).op.toLoc f₂.op.toLoc
      q.op.toLoc _).hom.toNatTrans.app M).snd = _
  rw [comp_snd', mapComp'_inv_app_snd, mapComp'_hom_app_snd]
  rfl

/-- The first component of a morphism of descent data between objects of the 2-fiber product. -/
@[simps]
def homFst {M N : (twoFiberProduct α β).obj (.mk (op S))}
    (Φ : ((twoFiberProduct α β).toDescentData f).obj M ⟶
      ((twoFiberProduct α β).toDescentData f).obj N) :
    (F.toDescentData f).obj M.fst ⟶ (F.toDescentData f).obj N.fst where
  hom i := (Φ.hom i).fst
  comm _ q _ _ f₁ f₂ hf₁ hf₂ := by
    have := congrArg Hom.fst (Φ.comm q f₁ f₂ hf₁ hf₂)
    rwa [comp_fst', comp_fst', toDescentData_obj_hom_fst, toDescentData_obj_hom_fst] at this

/-- The second component of a morphism of descent data between objects of the 2-fiber product. -/
@[simps]
def homSnd {M N : (twoFiberProduct α β).obj (.mk (op S))}
    (Φ : ((twoFiberProduct α β).toDescentData f).obj M ⟶
      ((twoFiberProduct α β).toDescentData f).obj N) :
    (G.toDescentData f).obj M.snd ⟶ (G.toDescentData f).obj N.snd where
  hom i := (Φ.hom i).snd
  comm _ q _ _ f₁ f₂ hf₁ hf₂ := by
    have := congrArg Hom.snd (Φ.comm q f₁ f₂ hf₁ hf₂)
    rwa [comp_snd', comp_snd', toDescentData_obj_hom_snd, toDescentData_obj_hom_snd] at this

end TauCeti.Stack.twoFiberProduct

end

/-! ### Descent of morphisms and effectivity -/

public section

namespace TauCeti.Stack.twoFiberProduct

open Pseudofunctor Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
  {F G H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', max u' v'}} (α : F ⟶ H) (β : G ⟶ H)

/-- A morphism of pullbacks in the 2-fiber product whose components are the pullbacks of `a` and
`b` exhibits `(a, b)` as compatible with the structure isomorphisms after pulling back along `u`. -/
private lemma map_map_comp_iso_hom {X Y : Cᵒᵖ} (u : X ⟶ Y) {x y : Fiber α β X} (a : x.fst ⟶ y.fst)
    (b : x.snd ⟶ y.snd) (φ : (map α β u).obj x ⟶ (map α β u).obj y)
    (h₁ : (F.map u.toLoc).toFunctor.map a = φ.fst) (h₂ : (G.map u.toLoc).toFunctor.map b = φ.snd) :
    (H.map u.toLoc).toFunctor.map ((α.app (.mk X)).toFunctor.map a ≫ y.iso.hom) =
      (H.map u.toLoc).toFunctor.map (x.iso.hom ≫ (β.app (.mk X)).toFunctor.map b) := by
  have hw := φ.w
  simp only [map_obj_iso, mapIso_hom] at hw
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    ← Pseudofunctor.StrongTrans.naturality_naturality_1 α,
    ← Pseudofunctor.StrongTrans.naturality_naturality_1 β, h₁, h₂,
    ← cancel_epi ((α.naturality u.toLoc).hom.toNatTrans.app x.fst)]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc] at hw ⊢
  rw [← cancel_mono ((β.naturality u.toLoc).inv.toNatTrans.app y.snd)]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app]
  -- The identity lives over `(G.map u ≫ β.app Y).toFunctor.obj y.snd`, which is only
  -- definitionally the source of `(β.naturality u).inv.toNatTrans.app y.snd`.
  erw [Category.comp_id]
  exact hw.trans ((Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _)))

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- If the descent functors of `F` and `G` along a family of morphisms are fully faithful and that
of `H` is faithful, the descent functor of the 2-fiber product along this family is fully
faithful. -/
noncomputable def fullyFaithfulToDescentData (hF : (F.toDescentData f).FullyFaithful)
    (hG : (G.toDescentData f).FullyFaithful) [(H.toDescentData f).Faithful] :
    ((twoFiberProduct α β).toDescentData f).FullyFaithful where
  preimage {M N} Φ :=
    { fst := hF.preimage (homFst α β f Φ)
      snd := hG.preimage (homSnd α β f Φ)
      w := (H.toDescentData f).map_injective (by
        ext i
        have h₁ := congrArg (fun φ ↦ φ.hom i) (hF.map_preimage (homFst α β f Φ))
        have h₂ := congrArg (fun φ ↦ φ.hom i) (hG.map_preimage (homSnd α β f Φ))
        simp only [toDescentData_map_hom, homFst_hom, homSnd_hom] at h₁ h₂
        exact map_map_comp_iso_hom α β (f i).op _ _ (Φ.hom i) h₁ h₂) }
  map_preimage {M N} Φ := by
    ext i
    refine CategoricalPullback.hom_ext ?_ ?_
    · exact congrArg (fun φ ↦ φ.hom i) (hF.map_preimage (homFst α β f Φ))
    · exact congrArg (fun φ ↦ φ.hom i) (hG.map_preimage (homSnd α β f Φ))
  preimage_map {M N} φ := by
    refine CategoricalPullback.hom_ext ?_ ?_
    · exact hF.preimage_map φ.fst
    · exact hG.preimage_map φ.snd

section glue

/-! The construction of the structure isomorphism of a glued object. Given objects `M₁` of `F` and
`M₂` of `G` over `S`, local identifications of their pullbacks with the components of objects `d`
of the 2-fiber product give local morphisms `p^* (α M₁) ⟶ p^* (β M₂)`; when these come from the
pieces of a descent datum, they form a morphism of descent data for `H`. -/

variable (M₁ : F.obj (.mk (op S))) (M₂ : G.obj (.mk (op S)))

/-- The local comparison `p^* (α M₁) ⟶ p^* (β M₂)` through an object `d` of the 2-fiber product
over `X` and morphisms `p^* M₁ ⟶ d.fst` and `d.snd ⟶ p^* M₂`. -/
private def glueHom {X : C} (p : X ⟶ S) (d : Fiber α β (op X))
    (e₁ : (F.map p.op.toLoc).toFunctor.obj M₁ ⟶ d.fst)
    (e₂ : d.snd ⟶ (G.map p.op.toLoc).toFunctor.obj M₂) :
    (H.map p.op.toLoc).toFunctor.obj ((α.app (.mk (op S))).toFunctor.obj M₁) ⟶
      (H.map p.op.toLoc).toFunctor.obj ((β.app (.mk (op S))).toFunctor.obj M₂) :=
  (α.naturality p.op.toLoc).inv.toNatTrans.app M₁ ≫ (α.app (.mk (op X))).toFunctor.map e₁ ≫
    d.iso.hom ≫ (β.app (.mk (op X))).toFunctor.map e₂ ≫
      (β.naturality p.op.toLoc).hom.toNatTrans.app M₂

private lemma isIso_glueHom {X : C} (p : X ⟶ S) (d : Fiber α β (op X))
    (e₁ : (F.map p.op.toLoc).toFunctor.obj M₁ ⟶ d.fst)
    (e₂ : d.snd ⟶ (G.map p.op.toLoc).toFunctor.obj M₂) (h₁ : IsIso e₁) (h₂ : IsIso e₂) :
    IsIso (glueHom α β M₁ M₂ p d e₁ e₂) := by
  dsimp only [glueHom]
  infer_instance

/-- The pullback of `glueHom` along `f₁ : Y ⟶ X`, conjugated by the composition comparisons of
`H`. -/
private lemma pullHom_glueHom {X Y : C} (p : X ⟶ S) (d : Fiber α β (op X))
    (e₁ : (F.map p.op.toLoc).toFunctor.obj M₁ ⟶ d.fst)
    (e₂ : d.snd ⟶ (G.map p.op.toLoc).toFunctor.obj M₂) (f₁ : Y ⟶ X) (q : Y ⟶ S)
    (hq : f₁ ≫ p = q) :
    (H.mapComp' p.op.toLoc f₁.op.toLoc q.op.toLoc (congrArg (·.op.toLoc) hq)).hom.toNatTrans.app _ ≫
        (H.map f₁.op.toLoc).toFunctor.map (glueHom α β M₁ M₂ p d e₁ e₂) ≫
          (H.mapComp' p.op.toLoc f₁.op.toLoc q.op.toLoc
              (congrArg (·.op.toLoc) hq)).inv.toNatTrans.app _ =
      (α.naturality q.op.toLoc).inv.toNatTrans.app M₁ ≫
        (α.app (.mk (op Y))).toFunctor.map
          ((F.mapComp' p.op.toLoc f₁.op.toLoc q.op.toLoc
              (congrArg (·.op.toLoc) hq)).hom.toNatTrans.app M₁ ≫
            (F.map f₁.op.toLoc).toFunctor.map e₁) ≫
        (mapIso α β f₁.op d).hom ≫
          (β.app (.mk (op Y))).toFunctor.map ((G.map f₁.op.toLoc).toFunctor.map e₂ ≫
            (G.mapComp' p.op.toLoc f₁.op.toLoc q.op.toLoc
                (congrArg (·.op.toLoc) hq)).inv.toNatTrans.app
              M₂) ≫
          (β.naturality q.op.toLoc).hom.toNatTrans.app M₂ := by
  simp only [glueHom, mapIso_hom, CategoryTheory.Functor.map_comp, Category.assoc,
    ← Pseudofunctor.StrongTrans.naturality_naturality_1 α,
    ← Pseudofunctor.StrongTrans.naturality_naturality_1 β,
    Pseudofunctor.StrongTrans.naturality_comp'_inv_app α p.op.toLoc f₁.op.toLoc q.op.toLoc
      (congrArg (·.op.toLoc) hq),
    Pseudofunctor.StrongTrans.naturality_comp'_hom_app β p.op.toLoc f₁.op.toLoc q.op.toLoc
      (congrArg (·.op.toLoc) hq)]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Cat.Hom.inv_hom_id_toNatTrans_app,
    Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  -- The identity lives over `(G.map p ≫ G.map f₁).toFunctor.obj M₂`, which is only
  -- definitionally the target of `G.mapComp'`.
  erw [Category.comp_id]

variable {M₁ M₂}

/-- Local comparisons built from the pieces of a descent datum agree on overlaps, conjugated by the
composition comparisons of `H`: they form a morphism of descent data for `H`. -/
private lemma glueHom_comm {X₁ X₂ Y : C} {p₁ : X₁ ⟶ S} {p₂ : X₂ ⟶ S} {d₁ : Fiber α β (op X₁)}
    {d₂ : Fiber α β (op X₂)} {e₁₁ : (F.map p₁.op.toLoc).toFunctor.obj M₁ ⟶ d₁.fst}
    {e₁₂ : (F.map p₂.op.toLoc).toFunctor.obj M₁ ⟶ d₂.fst}
    {e₂₁ : d₁.snd ⟶ (G.map p₁.op.toLoc).toFunctor.obj M₂}
    {e₂₂ : d₂.snd ⟶ (G.map p₂.op.toLoc).toFunctor.obj M₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {q : Y ⟶ S} (hq₁ : f₁ ≫ p₁ = q) (hq₂ : f₂ ≫ p₂ = q)
    (δ₁ : (F.map f₁.op.toLoc).toFunctor.obj d₁.fst ⟶ (F.map f₂.op.toLoc).toFunctor.obj d₂.fst)
    (δ₂ : (G.map f₁.op.toLoc).toFunctor.obj d₁.snd ⟶ (G.map f₂.op.toLoc).toFunctor.obj d₂.snd)
    (hw : (α.app (.mk (op Y))).toFunctor.map δ₁ ≫ (mapIso α β f₂.op d₂).hom =
      (mapIso α β f₁.op d₁).hom ≫ (β.app (.mk (op Y))).toFunctor.map δ₂)
    (h₁ : (F.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
        (congrArg (·.op.toLoc) hq₁)).hom.toNatTrans.app
        M₁ ≫ (F.map f₁.op.toLoc).toFunctor.map e₁₁ ≫ δ₁ =
      (F.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
          (congrArg (·.op.toLoc) hq₂)).hom.toNatTrans.app M₁ ≫
        (F.map f₂.op.toLoc).toFunctor.map e₁₂)
    (h₂ : (G.map f₁.op.toLoc).toFunctor.map e₂₁ ≫
        (G.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₁)).inv.toNatTrans.app M₂ =
      δ₂ ≫ (G.map f₂.op.toLoc).toFunctor.map e₂₂ ≫
        (G.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₂)).inv.toNatTrans.app
          M₂) :
    (H.map f₁.op.toLoc).toFunctor.map (glueHom α β M₁ M₂ p₁ d₁ e₁₁ e₂₁) ≫
        (H.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₁)).inv.toNatTrans.app _ ≫
        (H.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₂)).hom.toNatTrans.app _ =
      ((H.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
          (congrArg (·.op.toLoc) hq₁)).inv.toNatTrans.app _ ≫
        (H.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₂)).hom.toNatTrans.app _) ≫
        (H.map f₂.op.toLoc).toFunctor.map (glueHom α β M₁ M₂ p₂ d₂ e₁₂ e₂₂) := by
  -- The two pullbacks to `Y`, computed by `pullHom_glueHom`, agree by `hw`, `h₁` and `h₂`.
  have hI : (α.app (.mk (op Y))).toFunctor.map
        ((F.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₁)).hom.toNatTrans.app
          M₁ ≫ (F.map f₁.op.toLoc).toFunctor.map e₁₁) ≫ (mapIso α β f₁.op d₁).hom ≫
        (β.app (.mk (op Y))).toFunctor.map ((G.map f₁.op.toLoc).toFunctor.map e₂₁ ≫
          (G.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
              (congrArg (·.op.toLoc) hq₁)).inv.toNatTrans.app
            M₂) =
      (α.app (.mk (op Y))).toFunctor.map
        ((F.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
            (congrArg (·.op.toLoc) hq₂)).hom.toNatTrans.app
          M₁ ≫ (F.map f₂.op.toLoc).toFunctor.map e₁₂) ≫ (mapIso α β f₂.op d₂).hom ≫
        (β.app (.mk (op Y))).toFunctor.map ((G.map f₂.op.toLoc).toFunctor.map e₂₂ ≫
          (G.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
              (congrArg (·.op.toLoc) hq₂)).inv.toNatTrans.app
            M₂) := by
    rw [h₂, ← h₁]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [reassoc_of% hw]
  rw [← cancel_epi ((H.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc
      (congrArg (·.op.toLoc) hq₁)).hom.toNatTrans.app _),
    ← cancel_mono ((H.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc
      (congrArg (·.op.toLoc) hq₂)).inv.toNatTrans.app _)]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id,
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  rw [pullHom_glueHom α β M₁ M₂ p₁ d₁ e₁₁ e₂₁ f₁ q hq₁,
    pullHom_glueHom α β M₁ M₂ p₂ d₂ e₁₂ e₂₂ f₂ q hq₂, reassoc_of% hI]

/-- An isomorphism `m : α M₁ ≅ β M₂` whose pullback along `p` is the local comparison through `d`
makes the identifications of the components of `d` with the pullbacks of `M₁` and `M₂`
compatible with the structure isomorphisms. -/
private lemma glueHom_w {X : C} {p : X ⟶ S} {d : Fiber α β (op X)}
    {e₁ : (F.map p.op.toLoc).toFunctor.obj M₁ ⟶ d.fst}
    {e₂ : (G.map p.op.toLoc).toFunctor.obj M₂ ⟶ d.snd}
    {e₂' : d.snd ⟶ (G.map p.op.toLoc).toFunctor.obj M₂} (he₂ : e₂' ≫ e₂ = 𝟙 _)
    (m : (α.app (.mk (op S))).toFunctor.obj M₁ ≅ (β.app (.mk (op S))).toFunctor.obj M₂)
    (hm : (H.map p.op.toLoc).toFunctor.map m.hom = glueHom α β M₁ M₂ p d e₁ e₂') :
    (α.app (.mk (op X))).toFunctor.map e₁ ≫ d.iso.hom =
      (mapIso α β p.op (⟨M₁, M₂, m⟩ : Fiber α β (op S))).hom ≫
        (β.app (.mk (op X))).toFunctor.map e₂ := by
  simp only [mapIso_hom, hm, glueHom, Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
    ← CategoryTheory.Functor.map_comp, he₂, CategoryTheory.Functor.map_id, Category.comp_id]

end glue

variable {α β} in
/-- If the descent functors of `F` and `G` along a family of morphisms are essentially surjective
and that of `H` is fully faithful, the descent functor of the 2-fiber product along this family is
essentially surjective: a descent datum glues to the triple of the gluings of its components and
the isomorphism glued, in `H`, from the structure isomorphisms of its pieces. -/
lemma essSurj_toDescentData [(F.toDescentData f).EssSurj] [(G.toDescentData f).EssSurj]
    (hH : (H.toDescentData f).FullyFaithful) :
    ((twoFiberProduct α β).toDescentData f).EssSurj where
  mem_essImage D := by
    -- Glue the two components of `D`.
    let e₁ := (F.toDescentData f).objObjPreimageIso ((descentDataFst α β f).obj D)
    let e₂ := (G.toDescentData f).objObjPreimageIso ((descentDataSnd α β f).obj D)
    have he₁ (i : ι) : IsIso (e₁.hom.hom i) :=
      ⟨e₁.inv.hom i, congrArg (fun φ ↦ φ.hom i) e₁.hom_inv_id,
        congrArg (fun φ ↦ φ.hom i) e₁.inv_hom_id⟩
    have he₂ (i : ι) : IsIso (e₂.inv.hom i) :=
      ⟨e₂.hom.hom i, congrArg (fun φ ↦ φ.hom i) e₂.inv_hom_id,
        congrArg (fun φ ↦ φ.hom i) e₂.hom_inv_id⟩
    -- The local comparisons form an isomorphism of descent data for `H`.
    let Ψ : (H.toDescentData f).obj ((α.app _).toFunctor.obj
        ((F.toDescentData f).objPreimage ((descentDataFst α β f).obj D))) ≅
        (H.toDescentData f).obj ((β.app _).toFunctor.obj
          ((G.toDescentData f).objPreimage ((descentDataSnd α β f).obj D))) :=
      DescentData.isoMk (fun i ↦ @asIso _ _ _ _ (glueHom α β _ _ (f i) (D.obj i) (e₁.hom.hom i)
        (e₂.inv.hom i)) (isIso_glueHom α β _ _ _ _ _ _ (he₁ i) (he₂ i)))
        (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
          refine glueHom_comm α β hf₁ hf₂ (D.hom q f₁ f₂ hf₁ hf₂).fst (D.hom q f₁ f₂ hf₁ hf₂).snd
            (D.hom q f₁ f₂ hf₁ hf₂).w ?_ ?_
          -- The compatibilities of `e₁.hom` and `e₂.inv` with the structure morphisms of
          -- `toDescentData`, conjugated by the composition comparisons.
          · exact (Iso.eq_inv_comp ((Cat.Hom.toNatIso (F.mapComp' (f i₁).op.toLoc f₁.op.toLoc
              q.op.toLoc (congrArg (·.op.toLoc) hf₁))).app _)).mp
              ((e₁.hom.comm q f₁ f₂ hf₁ hf₂).trans (Category.assoc _ _ _))
          · exact ((Iso.eq_comp_inv ((Cat.Hom.toNatIso (G.mapComp' (f i₂).op.toLoc f₂.op.toLoc
              q.op.toLoc (congrArg (·.op.toLoc) hf₂))).app _)).mpr
              ((Category.assoc _ _ _).trans (e₂.inv.comm q f₁ f₂ hf₁ hf₂))).trans
                (Category.assoc _ _ _))
    -- It descends to the structure isomorphism of the glued object.
    let m := hH.preimageIso Ψ
    let M : (twoFiberProduct α β).obj (.mk (op S)) := ⟨_, _, m⟩
    have hm (i : ι) := congrArg (fun φ ↦ φ.hom i) (hH.map_preimage Ψ.hom)
    refine ⟨M, ⟨DescentData.isoMk (fun i ↦ mkIso
      ⟨e₁.hom.hom i, e₁.inv.hom i, congrArg (fun φ ↦ φ.hom i) e₁.hom_inv_id,
        congrArg (fun φ ↦ φ.hom i) e₁.inv_hom_id⟩
      ⟨e₂.hom.hom i, e₂.inv.hom i, congrArg (fun φ ↦ φ.hom i) e₂.hom_inv_id,
        congrArg (fun φ ↦ φ.hom i) e₂.inv_hom_id⟩
      (glueHom_w α β (congrArg (fun φ ↦ φ.hom i) e₂.inv_hom_id) m (hm i))) ?_⟩⟩
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    refine CategoricalPullback.hom_ext ?_ ?_
    · exact (e₁.hom.comm q f₁ f₂ hf₁ hf₂).trans
        (congrArg (· ≫ _) (toDescentData_obj_hom_fst α β f M q f₁ f₂ hf₁ hf₂).symm)
    · exact (e₂.hom.comm q f₁ f₂ hf₁ hf₂).trans
        (congrArg (· ≫ _) (toDescentData_obj_hom_snd α β f M q f₁ f₂ hf₁ hf₂).symm)

variable {J : GrothendieckTopology C}

/-- The 2-fiber product of two prestacks over a prestack is a prestack. -/
instance isPrestack [F.IsPrestack J] [G.IsPrestack J] [H.IsPrestack J] :
    (twoFiberProduct α β).IsPrestack J :=
  IsPrestack.of_isPrestackFor fun _ R hR ↦
    have := (H.isPrestackFor' R hR).fullyFaithful.faithful
    ⟨⟨fullyFaithfulToDescentData α β (F.isPrestackFor' R hR).fullyFaithful
      (G.isPrestackFor' R hR).fullyFaithful⟩⟩

/-- The 2-fiber product of two stacks over a prestack is a stack (Stacks, Lemma 8.4.6 (026G)). -/
@[stacks 026G]
instance isStack [F.IsStack J] [G.IsStack J] [H.IsPrestack J] :
    (twoFiberProduct α β).IsStack J where
  essSurj_of_sieve R hR :=
    have := IsStack.essSurj_of_sieve F R hR
    have := IsStack.essSurj_of_sieve G R hR
    essSurj_toDescentData (H.isPrestackFor' R hR).fullyFaithful

end TauCeti.Stack.twoFiberProduct
