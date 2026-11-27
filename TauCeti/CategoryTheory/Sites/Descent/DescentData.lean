/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Descent data utilities

For a descent datum `D` for a pseudofunctor `F` along a family `f : ∀ i, X i ⟶ S`, Mathlib's
morphisms `D.hom q f₁ f₂ hf₁ hf₂` carry the common composite `q : Y ⟶ S` of `f₁ ≫ f i₁` and
`f₂ ≫ f i₂` as an argument. This file records that they do not depend on `q`
(`DescentData.hom_congr`), states the cocycle condition `DescentData.hom_comp` for two morphisms
whose common composites are only propositionally equal (`DescentData.hom_comp_hom`), extracts
component isomorphisms from an isomorphism of descent data (`DescentData.isoApp`,
`DescentData.isoApp_hom_comm`, `DescentData.isoApp_isoMk`), and expresses transition maps and
compatibility squares of `toDescentData` and `pullFunctor` in terms of `Pseudofunctor.compIso`
and flexible factorizations (`DescentData.toDescentData_obj_hom`,
`DescentData.hom_toDescentData_obj_iff`, `DescentData.pullFunctor_obj_hom_eq`).

A morphism of Mathlib's descent data `D₁ ⟶ D₂` along `f` is a family of morphisms
`φ i : D₁.obj i ⟶ D₂.obj i` commuting with the gluing morphisms over every `Y` mapping to two of
the `X i` compatibly with the maps to `S`. When the pairs `X i₁ ×_S X i₂` have pullbacks, it is
enough to check this on the pullbacks themselves: every other `Y` maps to one of them, and the
gluing morphisms over `Y` are pulled back from those over the pullback
(`CategoryTheory.Pseudofunctor.DescentData.homMkOfIsPullback`). This is the form of the
compatibility condition used when descent data are compared with coalgebras.

The argument for `homMkOfIsPullback` is that of Mathlib's
`CategoryTheory.Pseudofunctor.DescentData'.comm`, which proves the same compatibility for descent
data stated on chosen pullbacks.
-/

public section

open CategoryTheory Bicategory Opposite

namespace CategoryTheory.Pseudofunctor.DescentData

variable {C : Type*} [Category* C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat} {ι : Type*}
  {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S} (D : F.DescentData f)

/-- Extract the component isomorphism `D₁.obj i ≅ D₂.obj i` from an isomorphism of descent data
`e : D₁ ≅ D₂`. -/
def isoApp {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) (i : ι) :
    D₁.obj i ≅ D₂.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := by
    simpa only [DescentData.comp_hom, DescentData.id_hom] using
      congrArg (fun φ : D₁ ⟶ D₁ ↦ φ.hom i) e.hom_inv_id
  inv_hom_id := by
    simpa only [DescentData.comp_hom, DescentData.id_hom] using
      congrArg (fun φ : D₂ ⟶ D₂ ↦ φ.hom i) e.inv_hom_id

/-- The forward morphism of `DescentData.isoApp e i` is the `i`-th component of `e.hom`. -/
@[simp]
lemma isoApp_hom {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) (i : ι) :
    (isoApp e i).hom = e.hom.hom i :=
  (rfl)

/-- The inverse morphism of `DescentData.isoApp e i` is the `i`-th component of `e.inv`. -/
@[simp]
lemma isoApp_inv {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) (i : ι) :
    (isoApp e i).inv = e.inv.hom i :=
  (rfl)

/-- Extracting the `i`-th component isomorphism from `Iso.refl D` gives `Iso.refl (D.obj i)`. -/
@[simp]
lemma isoApp_refl (D : F.DescentData f) (i : ι) :
    isoApp (Iso.refl D) i = Iso.refl (D.obj i) :=
  Iso.ext rfl

/-- Extracting the `i`-th component isomorphism from `e.symm` gives `(isoApp e i).symm`. -/
@[simp]
lemma isoApp_symm {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) (i : ι) :
    isoApp e.symm i = (isoApp e i).symm :=
  Iso.ext rfl

/-- Extracting the `i`-th component isomorphism from `e₁ ≪≫ e₂` gives
`isoApp e₁ i ≪≫ isoApp e₂ i`. -/
@[simp]
lemma isoApp_trans {D₁ D₂ D₃ : F.DescentData f} (e₁ : D₁ ≅ D₂) (e₂ : D₂ ≅ D₃) (i : ι) :
    isoApp (e₁ ≪≫ e₂) i = isoApp e₁ i ≪≫ isoApp e₂ i :=
  Iso.ext rfl

/-- The component morphisms `(isoApp e i).hom` commute with the descent-data transition maps. -/
@[reassoc]
lemma isoApp_hom_comm {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q := by cat_disch)
    (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).toFunctor.map (isoApp e i₁).hom ≫ D₂.hom q f₁ f₂ =
      D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (isoApp e i₂).hom := by
  simpa only [isoApp_hom] using e.hom.comm q f₁ f₂ hf₁ hf₂

/-- Extracting the `i`-th component isomorphism from `DescentData.isoMk e comm` recovers `e i`. -/
@[simp]
lemma isoApp_isoMk {D₁ D₂ : F.DescentData f} (e : ∀ i, D₁.obj i ≅ D₂.obj i)
    (comm : ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
      (F.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫ D₂.hom q f₁ f₂ =
        D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (e i₂).hom) (i : ι) :
    isoApp (DescentData.isoMk e comm) i = e i :=
  Iso.ext (by simp only [isoApp_hom, isoMk_hom_hom])

/-- The morphisms `D.hom q f₁ f₂` do not depend on the common composite `q`, which is determined
by `f₁`. -/
lemma hom_congr ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (q q' : Y ⟶ S) (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hq : q = q') :
    D.hom q f₁ f₂ hf₁ hf₂ = D.hom q' f₁ f₂ (hf₁.trans hq) (hf₂.trans hq) := by
  subst hq
  rfl

/-- The cocycle condition `DescentData.hom_comp` for possibly different common composites. -/
@[reassoc]
lemma hom_comp_hom ⦃Y : C⦄ ⦃i₁ i₂ i₃ : ι⦄ (q q' : Y ⟶ S) (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hf₂' : f₂ ≫ f i₂ = q')
    (hf₃ : f₃ ≫ f i₃ = q') :
    D.hom q f₁ f₂ hf₁ hf₂ ≫ D.hom q' f₂ f₃ hf₂' hf₃ =
      D.hom q f₁ f₃ hf₁ (hf₃.trans (hf₂'.symm.trans hf₂)) := by
  obtain rfl : q' = q := hf₂'.symm.trans hf₂
  exact D.hom_comp _ _ _ _ _ _ _

/-- The transition morphisms of `(F.toDescentData f).obj M` expressed in terms of
`Pseudofunctor.compIso`. -/
lemma toDescentData_obj_hom {M : F.obj (.mk (op S))} ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    ((F.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂ =
      (F.compIso (f i₁).op f₁.op q.op (by rw [← op_comp, hf₁]) M).inv ≫
        (F.compIso (f i₂).op f₂.op q.op (by rw [← op_comp, hf₂]) M).hom := by
  dsimp [toDescentData, DescentData.ofObj]
  rw [compIso_inv, compIso_hom]

/-- A compatibility square with `((F.toDescentData f).obj M).hom` on the right-hand side reduces,
after cancelling the left `compIso`, to matching `compIso.hom` components on both sides. -/
lemma hom_toDescentData_obj_iff {M : F.obj (.mk (op S))} ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    {T₁ T₂ : F.obj (.mk (op Y))}
    (lhs : (F.map f₁.op.toLoc).toFunctor.obj ((F.map (f i₁).op.toLoc).toFunctor.obj M) ⟶ T₁)
    (m : T₁ ⟶ T₂)
    (rhs : (F.map f₂.op.toLoc).toFunctor.obj ((F.map (f i₂).op.toLoc).toFunctor.obj M) ⟶ T₂) :
    lhs ≫ m = ((F.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂ ≫ rhs ↔
      (F.compIso (f i₁).op f₁.op q.op (by rw [← op_comp, hf₁]) M).hom ≫ lhs ≫ m =
        (F.compIso (f i₂).op f₂.op q.op (by rw [← op_comp, hf₂]) M).hom ≫ rhs := by
  refine (iff_of_eq (congrArg (lhs ≫ m = · ≫ rhs) (toDescentData_obj_hom q f₁ f₂ hf₁ hf₂))).trans
    ?_
  rw [Category.assoc, ← Iso.eq_inv_comp]

/-- The transition morphisms of `(pullFunctor F w).obj D`, rewritten to an arbitrary common
composite `q'` and factored morphisms `f₁'`, `f₂'`. -/
@[reassoc]
lemma pullFunctor_obj_hom_eq {S' : C} {p : S' ⟶ S} {ι' : Type*} {X' : ι' → C}
    {f' : ∀ j, X' j ⟶ S'} {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)}
    (w : ∀ j, p' j ≫ f (α j) = f' j ≫ p) (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S') ⦃j₁ j₂ : ι'⦄ (f₁ : Y ⟶ X' j₁) (f₂ : Y ⟶ X' j₂)
    (q' : Y ⟶ S) (f₁' : Y ⟶ X (α j₁)) (f₂' : Y ⟶ X (α j₂))
    (hf₁ : f₁ ≫ f' j₁ = q := by cat_disch) (hf₂ : f₂ ≫ f' j₂ = q := by cat_disch)
    (hq' : q ≫ p = q' := by cat_disch)
    (hf₁' : f₁ ≫ p' j₁ = f₁' := by cat_disch)
    (hf₂' : f₂ ≫ p' j₂ = f₂' := by cat_disch) :
    ((pullFunctor F w).obj D).hom q f₁ f₂ hf₁ hf₂ =
      (F.compIso (p' j₁).op f₁.op f₁'.op (by rw [← op_comp, hf₁']) (D.obj (α j₁))).inv ≫
        D.hom q' f₁' f₂'
          (by rw [← hq', ← hf₁', Category.assoc, w, reassoc_of% hf₁])
          (by rw [← hq', ← hf₂', Category.assoc, w, reassoc_of% hf₂]) ≫
        (F.compIso (p' j₂).op f₂.op f₂'.op (by rw [← op_comp, hf₂']) (D.obj (α j₂))).hom := by
  subst hf₁
  rw [compIso_inv, compIso_hom]
  exact (pullFunctorObj_hom w D Y (f₁ ≫ f' j₁) j₁ j₂ f₁ f₂ rfl hf₂).trans
    (pullFunctorObjHom_eq w D (f₁ ≫ f' j₁) f₁ f₂ q' f₁' f₂' rfl hf₂ hq' hf₁' hf₂')

open LocallyDiscreteOpToCat

variable {D₁ D₂ : F.DescentData f}

/-- **Morphisms of descent data are checked on pullbacks.** Given, for all `i j`, a pullback square
`P i j` of `f i` and `f j` with projections `p₁ i j` and `p₂ i j`, a family of morphisms
`φ i : D₁.obj i ⟶ D₂.obj i` which commutes with the gluing morphisms over every `P i j` is a
morphism of descent data. -/
def homMkOfIsPullback (φ : ∀ i, D₁.obj i ⟶ D₂.obj i) {P : ι → ι → C}
    {p₁ : ∀ i j, P i j ⟶ X i} {p₂ : ∀ i j, P i j ⟶ X j}
    (h : ∀ i j, IsPullback (p₁ i j) (p₂ i j) (f i) (f j))
    (comm : ∀ i j, (F.map (p₁ i j).op.toLoc).toFunctor.map (φ i) ≫
        D₂.hom (p₁ i j ≫ f i) (p₁ i j) (p₂ i j) rfl (h i j).w.symm =
      D₁.hom (p₁ i j ≫ f i) (p₁ i j) (p₂ i j) rfl (h i j).w.symm ≫
        (F.map (p₂ i j).op.toLoc).toFunctor.map (φ j)) :
    D₁ ⟶ D₂ where
  hom := φ
  comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
    -- `Y` maps to the pullback `P i₁ i₂` by `g`, and the gluing morphisms over `Y` are the
    -- pullbacks along `g` of those over `P i₁ i₂`.
    let g := (h i₁ i₂).lift f₁ f₂ (hf₁.trans hf₂.symm)
    have hg₁ : g ≫ p₁ i₁ i₂ = f₁ := (h i₁ i₂).lift_fst _ _ _
    have hg₂ : g ≫ p₂ i₁ i₂ = f₂ := (h i₁ i₂).lift_snd _ _ _
    have hq : g ≫ p₁ i₁ i₂ ≫ f i₁ = q := by rw [reassoc_of% hg₁, hf₁]
    rw [← D₁.pullHom_hom g _ q hq _ _ rfl (h i₁ i₂).w.symm _ _ hg₁ hg₂,
      ← D₂.pullHom_hom g _ q hq _ _ rfl (h i₁ i₂).w.symm _ _ hg₁ hg₂]
    -- Move `φ` across the comparison isomorphisms of `F` by their naturality, and apply `comm`
    -- pulled back along `g`.
    dsimp only [pullHom]
    rw [mapComp'_hom_naturality_assoc, ← Functor.map_comp_assoc, comm, Functor.map_comp_assoc,
      mapComp'_inv_naturality]
    simp only [Category.assoc]

/-- The components of `homMkOfIsPullback φ h comm` are the given morphisms `φ i`. -/
@[simp]
lemma homMkOfIsPullback_hom (φ : ∀ i, D₁.obj i ⟶ D₂.obj i) {P : ι → ι → C}
    {p₁ : ∀ i j, P i j ⟶ X i} {p₂ : ∀ i j, P i j ⟶ X j}
    (h : ∀ i j, IsPullback (p₁ i j) (p₂ i j) (f i) (f j))
    (comm : ∀ i j, (F.map (p₁ i j).op.toLoc).toFunctor.map (φ i) ≫
        D₂.hom (p₁ i j ≫ f i) (p₁ i j) (p₂ i j) rfl (h i j).w.symm =
      D₁.hom (p₁ i j ≫ f i) (p₁ i j) (p₂ i j) rfl (h i j).w.symm ≫
        (F.map (p₂ i j).op.toLoc).toFunctor.map (φ j)) (i : ι) :
    (homMkOfIsPullback φ h comm).hom i = φ i :=
  -- The body of `homMkOfIsPullback` is not exposed, so this is not a `rfl` lemma for `dsimp`
  -- outside this module.
  by rfl

end CategoryTheory.Pseudofunctor.DescentData
