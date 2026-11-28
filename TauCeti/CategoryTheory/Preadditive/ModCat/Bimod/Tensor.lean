/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.ModCat.Bimod
public import TauCeti.CategoryTheory.Preadditive.ModCat.Tensor

/-!
# Tensor products of bimodules over preadditive categories

For a `(D, C)`-bimodule `M` and a `(C, E)`-bimodule `N`, the value of their tensor product at
`(d, e)` is the coend tensor of the slices `M(d, -)` and `N(-, e)` over `C`. The resulting
bimodule is contravariant in `d` and covariant in `e`. When the second factor is a left
`C`-module, `tensorLeft M` gives a left `D`-module by the same construction.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), §6, pp. 26–29,
  including the bimodule version of equation (4).
-/

public section

noncomputable section

open CategoryTheory Opposite Functor

namespace TauCeti.ModCat.Bimod

universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {D : Type u₁} [Category.{v₁} D] [Preadditive D]
  {C : Type u₂} [Category.{v₂} C] [Preadditive C]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E]

open LinearBimod (sliceLeft sliceRight)

private abbrev slices {A B L : Type*} [Category* A] [Category* B] [Category* L]
    [Preadditive B] [Preadditive L] (K : A ⥤ B ⥤ L)
    [∀ a, (K.obj a).Additive] (M : ModCat.{w} L) : Aᵒᵖ ⥤ ModCat.{w} B :=
  ObjectProperty.lift _
    (K.op ⋙ Functor.opHom B L ⋙ (Functor.whiskeringRight _ _ _).obj M.obj)
    fun a ↦ (additiveFunctor_iff ((K.obj a.unop).op ⋙ M.obj)).2 inferInstance

private abbrev slicesMap {A B L : Type*} [Category* A] [Category* B] [Category* L]
    [Preadditive B] [Preadditive L] (K : A ⥤ B ⥤ L) [∀ a, (K.obj a).Additive]
    {M M' : ModCat.{w} L} (α : M ⟶ M') : slices K M ⟶ slices K M' where
  app a := ObjectProperty.homMk (whiskerLeft (K.obj a.unop).op α.hom)
  naturality _ _ f := ObjectProperty.hom_ext _ <| NatTrans.ext <| funext fun b ↦
    α.hom.naturality ((K.map f.unop).app b.unop).op

private instance slices_additive {A B L : Type*} [Category* A] [Category* B] [Category* L]
    [Preadditive A] [Preadditive B] [Preadditive L] (K : A ⥤ B ⥤ L) [K.Additive]
    [∀ a, (K.obj a).Additive] (M : ModCat.{w} L) : (slices K M).Additive where
  map_add {a a'} f g := ObjectProperty.hom_ext _ <| NatTrans.ext <| funext fun b ↦ by
    have := (additiveFunctor_iff M.obj).1 M.property
    -- Display the components in the target so that addition is computed pointwise.
    change M.obj.map ((K.map (f + g).unop).app b.unop).op =
      (M.obj.map ((K.map f.unop).app b.unop).op +
        M.obj.map ((K.map g.unop).app b.unop).op)
    simp

private abbrev rightSlices (M : Bimod.{w} D C) : Dᵒᵖ ⥤ ModCat.{w} Cᵒᵖ :=
  slices (LinearTensor.bifunctor ℤ D Cᵒᵖ) M

private instance (e : Eᵒᵖ) : ((LinearTensor.bifunctor ℤ C Eᵒᵖ).flip.obj e).Additive :=
  inferInstanceAs (((LinearTensor.bifunctor ℤ C Eᵒᵖ) ⋙ (evaluation _ _).obj e).Additive)

private instance : (LinearTensor.bifunctor ℤ C Eᵒᵖ).flip.Additive where
  map_add {_ _} f g := NatTrans.ext <| funext fun c ↦
    ((LinearTensor.bifunctor ℤ C Eᵒᵖ).obj c).map_add (f := f) (g := g)

private abbrev leftSlices (N : Bimod.{w} C E) : E ⥤ ModCat.{w} C :=
  opOp E ⋙ slices (LinearTensor.bifunctor ℤ C Eᵒᵖ).flip N

private abbrev rightSlicesMap {M M' : Bimod.{w} D C} (α : M ⟶ M') :
    rightSlices M ⟶ rightSlices M' :=
  slicesMap (LinearTensor.bifunctor ℤ D Cᵒᵖ) α

private abbrev leftSlicesMap {N N' : Bimod.{w} C E} (β : N ⟶ N') :
    leftSlices N ⟶ leftSlices N' :=
  whiskerLeft (opOp E) (slicesMap (LinearTensor.bifunctor ℤ C Eᵒᵖ).flip β)

variable [EssentiallySmall.{w} C]

private abbrev tensorDiagram (M : Bimod.{w} D C) (N : Bimod.{w} C E) :
    Dᵒᵖ ⥤ E ⥤ AddCommGrpCat.{w} :=
  rightSlices M ⋙ ModCat.tensor ⋙ (Functor.whiskeringLeft _ _ _).obj (leftSlices N)

private abbrev tensorDiagramMap {M M' : Bimod.{w} D C} {N N' : Bimod.{w} C E}
    (α : M ⟶ M') (β : N ⟶ N') : tensorDiagram M N ⟶ tensorDiagram M' N' :=
  whiskerRight (rightSlicesMap α)
    (ModCat.tensor ⋙ (Functor.whiskeringLeft _ _ _).obj (leftSlices N)) ≫
    whiskerLeft (rightSlices M' ⋙ ModCat.tensor)
      ((Functor.whiskeringLeft _ _ _).map (leftSlicesMap β))

private abbrev tensorOppositeDiagram (M : Bimod.{w} D C) (N : Bimod.{w} C E) :
    D ⥤ Eᵒᵖ ⥤ AddCommGrpCat.{w}ᵒᵖ :=
  (tensorDiagram M N).rightOp ⋙ (Functor.opUnopEquiv E AddCommGrpCat.{w}).functor

private instance (M : Bimod.{w} D C) (N : Bimod.{w} C E) :
    (tensorOppositeDiagram M N).Additive := by
  let : (Functor.opUnopEquiv E AddCommGrpCat.{w}).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  infer_instance

private instance (M : Bimod.{w} D C) (N : Bimod.{w} C E) (d : D) :
    ((tensorOppositeDiagram M N).obj d).Additive := by
  let : (opOp E).Additive := ⟨rfl⟩
  exact inferInstanceAs (((leftSlices N ⋙ ModCat.tensor.obj (M.sliceRight d)).op).Additive)

private def tensorBimodule (M : Bimod.{w} D C) (N : Bimod.{w} C E) : Bimod.{w} D E :=
  let K := (LinearTensor.lift ℤ (tensorOppositeDiagram M N)).leftOp
  ⟨K, (additiveFunctor_iff K).2 inferInstance⟩

private def tensorMap {M M' : Bimod.{w} D C} {N N' : Bimod.{w} C E}
    (α : M ⟶ M') (β : N ⟶ N') : tensorBimodule M N ⟶ tensorBimodule M' N' :=
  let K := tensorOppositeDiagram M' N'
  let L := tensorOppositeDiagram M N
  let η : K ⟶ L := whiskerRight (tensorDiagramMap α β).rightOp
    (Functor.opUnopEquiv E AddCommGrpCat.{w}).functor
  ObjectProperty.homMk <| NatTrans.leftOp <|
    { app := fun p ↦ (η.app p.fst).app p.snd
      naturality := fun p q t ↦ LinearTensor.naturality_of_tmul
        (G := LinearTensor.lift ℤ K) (G' := LinearTensor.lift ℤ L)
        (fun p ↦ (η.app p.fst).app p.snd)
        (fun {d d'} f e ↦ by
          rw [LinearTensor.lift_map_tmul, LinearTensor.lift_map_tmul]
          -- Use the component objects of the curried functors to simplify their identity maps.
          change ((K.map f).app e ≫ (K.obj d').map (𝟙 e)) ≫ (η.app d').app e =
            (η.app d).app e ≫ (L.map f).app e ≫ (L.obj d').map (𝟙 e)
          simpa only [CategoryTheory.Functor.map_id, Category.comp_id, NatTrans.comp_app] using
            NatTrans.congr_app (η.naturality f) e)
        (fun d {e e'} g ↦ by
          rw [LinearTensor.lift_map_tmul, LinearTensor.lift_map_tmul]
          -- Use the component objects of the curried functors to simplify their identity maps.
          change ((K.map (𝟙 d)).app e ≫ (K.obj d).map g) ≫ (η.app d).app e' =
            (η.app d).app e ≫ (L.map (𝟙 d)).app e ≫ (L.obj d).map g
          simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] using
            (η.app d).naturality g) t }

private theorem tensorMap_hom_app {M M' : Bimod.{w} D C} {N N' : Bimod.{w} C E}
    (α : M ⟶ M') (β : N ⟶ N') (d : D) (e : E) :
    (tensorMap α β).hom.app (op ⟨d, op e⟩) =
      (ModCat.tensor.map ((LinearBimod.sliceRightFunctor d).map α)).app (N.sliceLeft e) ≫
        (ModCat.tensor.obj (M'.sliceRight d)).map ((LinearBimod.sliceLeftFunctor e).map β) := by
  rfl

/-- Tensoring bimodules over `C`, with the right `C`-action in the first argument. -/
def tensor : Bimod.{w} D C ⥤ Bimod.{w} C E ⥤ Bimod.{w} D E where
  obj M :=
    { obj := tensorBimodule M
      map := tensorMap (𝟙 M)
      map_id := fun N ↦ ObjectProperty.hom_ext _ <| NatTrans.ext <| funext fun ⟨⟨d, e⟩⟩ ↦ by
        simp [tensorMap_hom_app _ _ d e.unop]; rfl
      map_comp := fun β γ ↦ ObjectProperty.hom_ext _ <| NatTrans.ext <| funext fun ⟨⟨d, e⟩⟩ ↦ by
        simp [tensorMap_hom_app _ _ d e.unop]; rfl }
  map α :=
    { app := fun N ↦ tensorMap α (𝟙 N)
      naturality := fun N N' β ↦
        ObjectProperty.hom_ext _ <| NatTrans.ext <| funext fun ⟨⟨d, e⟩⟩ ↦ by
          simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
            tensorMap_hom_app _ _ d e.unop, CategoryTheory.Functor.map_id, NatTrans.id_app,
            Category.comp_id, Category.id_comp]
          exact (ModCat.tensor.map ((LinearBimod.sliceRightFunctor d).map α)).naturality
            ((LinearBimod.sliceLeftFunctor e.unop).map β) }
  map_id := fun M ↦ NatTrans.ext <| funext fun N ↦
    ObjectProperty.hom_ext _ <| NatTrans.ext <| funext fun ⟨⟨d, e⟩⟩ ↦ by
      simp [tensorMap_hom_app _ _ d e.unop]; rfl
  map_comp := fun α γ ↦ NatTrans.ext <| funext fun N ↦
    ObjectProperty.hom_ext _ <| NatTrans.ext <| funext fun ⟨⟨d, e⟩⟩ ↦ by
      simp [tensorMap_hom_app _ _ d e.unop]; rfl

/-- The tensor product of a `(D, C)`-bimodule and a `(C, E)`-bimodule over `C`. -/
abbrev tensorObj (M : Bimod.{w} D C) (N : Bimod.{w} C E) : Bimod.{w} D E :=
  (tensor.obj M).obj N

/-- The value of the bimodule tensor is the coend tensor of the corresponding slices. -/
def tensorObjEvalIso (M : Bimod.{w} D C) (N : Bimod.{w} C E) (d : D) (e : E) :
    (tensorObj M N).eval d e ≅ ModCat.tensorObj (M.sliceRight d) (N.sliceLeft e) :=
  Iso.refl _

/-- A pure tensor in the value at `(d, e)`, with both entries taken at the middle object `X`. -/
def tmul {M : Bimod.{w} D C} {N : Bimod.{w} C E} {d : D} {e : E}
    (X : C) (x : M.eval d X) (y : N.eval X e) : (tensorObj M N).eval d e :=
  (tensorObjEvalIso M N d e).inv (ModCat.tmul X x y)

/-- The evaluation isomorphism takes a bimodule pure tensor to the pure tensor of the slices. -/
@[simp]
theorem tensorObjEvalIso_hom_tmul {M : Bimod.{w} D C} {N : Bimod.{w} C E} {d : D} {e : E}
    (X : C) (x : M.eval d X) (y : N.eval X e) :
    (tensorObjEvalIso M N d e).hom (tmul X x y) = ModCat.tmul X x y := by
  rw [tmul, ← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]

/-- The outer morphisms act on their respective entries of a pure tensor. -/
@[simp]
theorem tensorObj_map_tmul (M : Bimod.{w} D C) (N : Bimod.{w} C E)
    {d d' : D} {e e' : E} (f : d ⟶ d') (g : e ⟶ e')
    (X : C) (x : M.eval d' X) (y : N.eval X e) :
    (tensorObj M N).obj.map (LinearTensor.tmul f g.op).op (tmul X x y) =
      tmul X (M.obj.map (LinearTensor.tmul f (𝟙 (op X))).op x)
        (N.obj.map (LinearTensor.tmul (𝟙 X) g.op).op y) := by
  -- Expand the separate actions using the tensor lift before evaluating on the pure tensor.
  have h : (tensorObj M N).obj.map (LinearTensor.tmul f g.op).op =
      ((tensorDiagram M N).obj (op d')).map g ≫ ((tensorDiagram M N).map f.op).app e' := by
    apply Quiver.Hom.op_inj
    exact LinearTensor.lift_map_tmul (tensorOppositeDiagram M N) f g.op
  rw [h]
  let β := (leftSlices N).map g
  let α := (rightSlices M).map f.op
  have hy := ModCat.tensor_obj_map_tmul (M.sliceRight d') β X x y
  have hx := ModCat.tensor_map_app_tmul α (N.sliceLeft e') X x (β.hom.app (op X) y)
  exact (congrArg ((ModCat.tensor.map α).app (N.sliceLeft e')) hy).trans hx

private theorem tensorMap_tmul {M M' : Bimod.{w} D C} {N N' : Bimod.{w} C E}
    (α : M ⟶ M') (β : N ⟶ N') (d : D) (e : E)
    (X : C) (x : M.eval d X) (y : N.eval X e) :
    (tensorMap α β).hom.app (op ⟨d, op e⟩) (tmul X x y) =
      tmul X (α.hom.app (op ⟨d, op X⟩) x) (β.hom.app (op ⟨X, op e⟩) y) := by
  -- Unfold the identity evaluation isomorphism to apply the coend computation rules.
  change (tensorMap α β).hom.app (op ⟨d, op e⟩) (ModCat.tmul X x y) = _
  rw [tensorMap_hom_app]
  let a := (LinearBimod.sliceRightFunctor d).map α
  let b := (LinearBimod.sliceLeftFunctor e).map β
  let T := ModCat.tensor.obj (M'.sliceRight d)
  have hx := ModCat.tensor_map_app_tmul a (N.sliceLeft e) X x y
  have hy := ModCat.tensor_obj_map_tmul (M'.sliceRight d) b X (a.hom.app (op (op X)) x) y
  exact (congrArg (T.map b) hx).trans hy

/-- A map of the first bimodule acts on the first entry of a pure tensor. -/
@[simp]
theorem tensor_map_app_tmul {M M' : Bimod.{w} D C} (α : M ⟶ M') (N : Bimod.{w} C E)
    (d : D) (e : E) (X : C) (x : M.eval d X) (y : N.eval X e) :
    ((tensor.map α).app N).hom.app (op ⟨d, op e⟩) (tmul X x y) =
      tmul X (α.hom.app (op ⟨d, op X⟩) x) y :=
  tensorMap_tmul α (𝟙 N) d e X x y

/-- A map of the second bimodule acts on the second entry of a pure tensor. -/
@[simp]
theorem tensor_obj_map_tmul (M : Bimod.{w} D C) {N N' : Bimod.{w} C E} (β : N ⟶ N')
    (d : D) (e : E) (X : C) (x : M.eval d X) (y : N.eval X e) :
    ((tensor.obj M).map β).hom.app (op ⟨d, op e⟩) (tmul X x y) =
      tmul X x (β.hom.app (op ⟨X, op e⟩) y) :=
  tensorMap_tmul (𝟙 M) β d e X x y

instance (M : Bimod.{w} D C) : ((tensor (E := E)).obj M).Additive where
  map_add {N N'} β γ := ObjectProperty.hom_ext _ <| NatTrans.ext <| funext fun ⟨⟨d, e⟩⟩ ↦ by
    -- Compute addition at the component of the underlying natural transformation.
    change (tensorMap (𝟙 M) (β + γ)).hom.app (op ⟨d, e⟩) =
      (tensorMap (𝟙 M) β).hom.app (op ⟨d, e⟩) +
        (tensorMap (𝟙 M) γ).hom.app (op ⟨d, e⟩)
    simp [tensorMap_hom_app _ _ d e.unop]; rfl

instance : (tensor (D := D) (C := C) (E := E)).Additive where
  map_add {M M'} α γ := NatTrans.ext <| funext fun N ↦
    ObjectProperty.hom_ext _ <| NatTrans.ext <| funext fun ⟨⟨d, e⟩⟩ ↦ by
      -- Compute addition at the component of the underlying natural transformation.
      change (tensorMap (α + γ) (𝟙 N)).hom.app (op ⟨d, e⟩) =
        (tensorMap α (𝟙 N)).hom.app (op ⟨d, e⟩) +
          (tensorMap γ (𝟙 N)).hom.app (op ⟨d, e⟩)
      simp [tensorMap_hom_app _ _ d e.unop, NatTrans.app_add]; rfl

/-- Tensor a `(D, C)`-bimodule with a left `C`-module, retaining the left `D`-action. -/
def tensorLeft (M : Bimod.{w} D C) : ModCat.{w} C ⥤ ModCat.{w} D :=
  ObjectProperty.lift _
    (ModCat.tensor.flip ⋙ (Functor.whiskeringLeft _ _ _).obj (rightSlices M))
    fun F ↦ (additiveFunctor_iff (rightSlices M ⋙ ModCat.tensor.flip.obj F)).2 inferInstance

instance (M : Bimod.{w} D C) : (tensorLeft M).Additive := by
  let : (ModCat.tensor (C := C)).flip.Additive :=
    ⟨NatTrans.ext <| funext fun G ↦ (ModCat.tensor.obj G).map_add⟩
  unfold tensorLeft
  infer_instance

/-- Evaluating the left tensor at `d` is naturally the coend tensor of the right slice
`M(d, -)` with the input module. -/
def tensorLeftCompEvaluationIso (M : Bimod.{w} D C) (d : D) :
    tensorLeft M ⋙ AdditiveFunctor.forget _ _ ⋙ (evaluation _ _).obj (op d) ≅
      ModCat.tensor.obj (M.sliceRight d) :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

/-- A pure tensor in the value of the left tensor at `d`. -/
def tensorLeftTmul (M : Bimod.{w} D C) (F : ModCat.{w} C) (d : D)
    (X : C) (x : M.eval d X) (y : F.obj.obj (op X)) : ((tensorLeft M).obj F).obj.obj (op d) :=
  (tensorLeftCompEvaluationIso M d).inv.app F (ModCat.tmul X x y)

/-- The evaluation isomorphism sends a pure tensor of the left tensor to the slice coend. -/
theorem tensorLeftCompEvaluationIso_hom_app_tmul (M : Bimod.{w} D C) (F : ModCat.{w} C) (d : D)
    (X : C) (x : M.eval d X) (y : F.obj.obj (op X)) :
    (tensorLeftCompEvaluationIso M d).hom.app F (tensorLeftTmul M F d X x y) =
      ModCat.tmul X x y := by
  simpa only [tensorLeftTmul, Iso.app_inv, Iso.app_hom, ConcreteCategory.comp_apply,
    ConcreteCategory.id_apply] using
    ConcreteCategory.congr_hom ((tensorLeftCompEvaluationIso M d).app F).inv_hom_id
      (ModCat.tmul X x y)

/-- A morphism of `D` acts on the first entry of a pure tensor in the left tensor. -/
@[simp]
theorem tensorLeft_obj_map_tmul (M : Bimod.{w} D C) (F : ModCat.{w} C) {d d' : D}
    (f : d ⟶ d') (X : C) (x : M.eval d' X) (y : F.obj.obj (op X)) :
    ((tensorLeft M).obj F).obj.map f.op (tensorLeftTmul M F d' X x y) =
      tensorLeftTmul M F d X (M.obj.map (LinearTensor.tmul f (𝟙 (op X))).op x) y :=
  ModCat.tensor_map_app_tmul ((rightSlices M).map f.op) F X x y

end TauCeti.ModCat.Bimod
