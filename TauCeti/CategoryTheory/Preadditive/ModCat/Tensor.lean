/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import TauCeti.Algebra.Category.Grp.Coend
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic

/-!
# Tensor products over a preadditive category

For a right module `G : ModCat Cᵒᵖ` and a left module `F : ModCat C`, the tensor product
`ModCat.tensorObj G F` is the coend of the ordinary abelian-group tensor products of their
values. Its morphisms out are given by families of bilinear maps that are balanced with
respect to the maps of `C`. The tensor product is additive in each module variable. Tensoring
with a representable in either slot is naturally isomorphic to evaluation.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, §6, pp. 26–27.
-/

public section

open CategoryTheory Limits Opposite TensorProduct

universe w v u

namespace TauCeti

namespace ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

section CoendTensor

variable [EssentiallySmall.{w} C]

private noncomputable abbrev tensorDiagram (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C) :=
  (tensorBifunctor Cᵒᵖ).obj (G.obj, F.obj)

/-- The tensor product over `C`, as a bifunctor with the right module first. -/
noncomputable def tensor : ModCat.{w} Cᵒᵖ ⥤ ModCat.{w} C ⥤ AddCommGrpCat.{w} :=
  Functor.curryObj (((additiveFunctor _ _).ι.prod (additiveFunctor _ _).ι) ⋙
    tensorBifunctor Cᵒᵖ ⋙ coendFunctor Cᵒᵖ AddCommGrpCat.{w})

/-- The tensor product of a right `C`-module and a left `C`-module. -/
noncomputable abbrev tensorObj (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C) : AddCommGrpCat.{w} :=
  (tensor.obj G).obj F

variable {G G' : ModCat.{w} Cᵒᵖ} {F F' : ModCat.{w} C}

/-- The bilinear map sending two elements at `X` to the class of their pure tensor. -/
noncomputable def tmulLinear (X : C) :
    G.obj.obj (op (op X)) →ₗ[ℤ] F.obj.obj (op X) →ₗ[ℤ] tensorObj G F :=
  (TensorProduct.mk ℤ _ _).compr₂ (coend.ι (tensorDiagram G F) (op X)).hom.toIntLinearMap

/-- The class of a pure tensor of elements in the two module values at `X`. -/
noncomputable abbrev tmul (X : C) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    tensorObj G F :=
  tmulLinear X x y

private lemma tmul_eq_coend_ι (X : C) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    tmul (G := G) (F := F) X x y = coend.ι (tensorDiagram G F) (op X) (x ⊗ₜ[ℤ] y) :=
  rfl

@[simp]
lemma tmul_add (X : C) (x : G.obj.obj (op (op X))) (y z : F.obj.obj (op X)) :
    tmul (G := G) (F := F) X x (y + z) = tmul X x y + tmul X x z :=
  map_add (tmulLinear X x) y z

@[simp]
lemma add_tmul (X : C) (x y : G.obj.obj (op (op X))) (z : F.obj.obj (op X)) :
    tmul (G := G) (F := F) X (x + y) z = tmul X x z + tmul X y z :=
  ((tmulLinear X).flip z).map_add x y

@[simp]
lemma tmul_zero (X : C) (x : G.obj.obj (op (op X))) : tmul (G := G) (F := F) X x 0 = 0 :=
  map_zero (tmulLinear X x)

@[simp]
lemma zero_tmul (X : C) (y : F.obj.obj (op X)) : tmul (G := G) (F := F) X 0 y = 0 :=
  ((tmulLinear X).flip y).map_zero

@[simp]
lemma tmul_neg (X : C) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    tmul (G := G) (F := F) X x (-y) = -tmul X x y :=
  map_neg (tmulLinear X x) y

@[simp]
lemma neg_tmul (X : C) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    tmul (G := G) (F := F) X (-x) y = -tmul X x y :=
  map_neg ((tmulLinear X).flip y) x

@[simp]
lemma tmul_sub (X : C) (x : G.obj.obj (op (op X))) (y z : F.obj.obj (op X)) :
    tmul (G := G) (F := F) X x (y - z) = tmul X x y - tmul X x z :=
  map_sub (tmulLinear X x) y z

@[simp]
lemma sub_tmul (X : C) (x y : G.obj.obj (op (op X))) (z : F.obj.obj (op X)) :
    tmul (G := G) (F := F) X (x - y) z = tmul X x z - tmul X y z :=
  map_sub ((tmulLinear X).flip z) x y

/-- A morphism of `C` can be moved between the two factors of a pure tensor. -/
lemma tmul_balance {X Y : C} (f : X ⟶ Y) (x : G.obj.obj (op (op X)))
    (y : F.obj.obj (op Y)) :
    tmul (G := G) (F := F) Y (G.obj.map f.op.op x) y = tmul X x (F.obj.map f.op y) := by
  have h : coend.ι (tensorDiagram G F) (op Y)
      (((tensorDiagram G F).map f.op.op).app (op Y) (x ⊗ₜ[ℤ] y)) =
    coend.ι (tensorDiagram G F) (op X)
      (((tensorDiagram G F).obj (op (op X))).map f.op (x ⊗ₜ[ℤ] y)) :=
    ConcreteCategory.congr_hom (coend.condition (tensorDiagram G F) f.op) (x ⊗ₜ[ℤ] y)
  simp only [tensorBifunctor_map_app_tmul, tensorBifunctor_obj_map_tmul] at h
  rw [tmul_eq_coend_ι, tmul_eq_coend_ι]
  exact h

/-- Homomorphisms from the tensor product over `C` are determined by pure tensors. -/
@[ext]
lemma tensorObj_hom_ext {A : AddCommGrpCat.{w}} {p q : tensorObj G F ⟶ A}
    (h : ∀ (X : C) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)),
      p (tmul X x y) = q (tmul X x y)) : p = q :=
  coend.hom_ext fun X ↦ AddCommGrpCat.tensor_hom_ext (h X.unop)

/-- Every element of the tensor product is generated additively by the classes of pure tensors. -/
@[elab_as_elim]
theorem tensorObj_induction_on {p : tensorObj G F → Prop} (z : tensorObj G F)
    (zero : p 0) (add : ∀ a b, p a → p b → p (a + b)) (neg : ∀ a, p a → p (-a))
    (pure : ∀ X x y, p (tmul X x y)) : p z := by
  let S : AddSubgroup (tensorObj G F) := AddSubgroup.closure {a | ∃ X x y, tmul X x y = a}
  let q : tensorObj G F ⟶ AddCommGrpCat.of ((tensorObj G F) ⧸ S) :=
    AddCommGrpCat.ofHom (QuotientAddGroup.mk' S)
  have hq : q = 0 := by
    apply tensorObj_hom_ext
    intro X x y
    exact (QuotientAddGroup.eq_zero_iff (tmul X x y)).2
      (AddSubgroup.subset_closure ⟨X, x, y, rfl⟩ : tmul X x y ∈ S)
  have hz : z ∈ S := (QuotientAddGroup.eq_zero_iff z).1 (ConcreteCategory.congr_hom hq z)
  induction hz using AddSubgroup.closure_induction with
  | mem _ hx =>
    obtain ⟨X, x, y, rfl⟩ := hx
    exact pure X x y
  | zero => exact zero
  | add a b _ _ ha hb => exact add a b ha hb
  | neg a _ ha => exact neg a ha

omit [EssentiallySmall.{w} C] in
private lemma tensorDesc_condition {A : AddCommGrpCat.{w}}
    (b : ∀ X : C, G.obj.obj (op (op X)) →ₗ[ℤ] F.obj.obj (op X) →ₗ[ℤ] A)
    (hb : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op Y)),
      b Y (G.obj.map f.op.op x) y = b X x (F.obj.map f.op y))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((tensorDiagram G F).map f.op).app X ≫
        AddCommGrpCat.ofHom (TensorProduct.lift (b X.unop)).toAddMonoidHom =
      ((tensorDiagram G F).obj (op Y)).map f ≫
        AddCommGrpCat.ofHom (TensorProduct.lift (b Y.unop)).toAddMonoidHom := by
  apply AddCommGrpCat.tensor_hom_ext
  intro x y
  -- Evaluate the composites in the ordinary tensor products of the module values.
  change TensorProduct.lift (b X.unop) (((tensorDiagram G F).map f.op).app X (x ⊗ₜ[ℤ] y)) =
    TensorProduct.lift (b Y.unop) (((tensorDiagram G F).obj (op Y)).map f (x ⊗ₜ[ℤ] y))
  simp only [tensorBifunctor_map_app_tmul, tensorBifunctor_obj_map_tmul]
  exact hb f.unop x y

/-- Extend a family of balanced bilinear maps to a homomorphism on the tensor product over `C`. -/
noncomputable def tensorDesc {A : AddCommGrpCat.{w}}
    (b : ∀ X : C, G.obj.obj (op (op X)) →ₗ[ℤ] F.obj.obj (op X) →ₗ[ℤ] A)
    (hb : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op Y)),
      b Y (G.obj.map f.op.op x) y = b X x (F.obj.map f.op y)) :
    tensorObj G F ⟶ A :=
  coend.desc (F := tensorDiagram G F)
    (fun X ↦ AddCommGrpCat.ofHom (TensorProduct.lift (b X.unop)).toAddMonoidHom)
    (fun _ _ f ↦ tensorDesc_condition b hb f)

@[simp]
lemma tensorDesc_tmul {A : AddCommGrpCat.{w}}
    (b : ∀ X : C, G.obj.obj (op (op X)) →ₗ[ℤ] F.obj.obj (op X) →ₗ[ℤ] A)
    (hb : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op Y)),
      b Y (G.obj.map f.op.op x) y = b X x (F.obj.map f.op y))
    (X : C) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    tensorDesc b hb (tmul X x y) = b X x y := by
  rw [tmul_eq_coend_ι]
  exact ConcreteCategory.congr_hom
    (coend.ι_desc (F := tensorDiagram G F) (fun X ↦
      AddCommGrpCat.ofHom (TensorProduct.lift (b X.unop)).toAddMonoidHom)
        (fun _ _ f ↦ tensorDesc_condition b hb f) (op X)) (x ⊗ₜ[ℤ] y)

private lemma coend_map_tmul (α : G ⟶ G') (β : F ⟶ F') (X : C)
    (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    coend.map ((tensorBifunctor Cᵒᵖ).map
        (X := (G.obj, F.obj)) (Y := (G'.obj, F'.obj)) (α.hom, β.hom)) (tmul X x y) =
      tmul (G := G') (F := F') X (α.hom.app (op (op X)) x) (β.hom.app (op X) y) := by
  let a := (tensorBifunctor Cᵒᵖ).map
    (X := (G.obj, F.obj)) (Y := (G'.obj, F'.obj)) (α.hom, β.hom)
  have h : coend.map a (coend.ι (tensorDiagram G F) (op X) (x ⊗ₜ[ℤ] y)) =
      coend.ι (tensorDiagram G' F') (op X) (((a.app (op (op X))).app (op X)) (x ⊗ₜ[ℤ] y)) :=
    ConcreteCategory.congr_hom (coend.ι_map a (op X)) (x ⊗ₜ[ℤ] y)
  simp only [a, tensorBifunctor_map_app_app_tmul] at h
  simpa only [tmul_eq_coend_ι] using h

/-- A map in the right-module argument acts on the first entry of a pure tensor. -/
@[simp]
lemma tensor_map_app_tmul (α : G ⟶ G') (F : ModCat.{w} C) (X : C)
    (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    (tensor.map α).app F (tmul X x y) = tmul X (α.hom.app (op (op X)) x) y :=
  coend_map_tmul α (𝟙 F) X x y

/-- A map in the left-module argument acts on the second entry of a pure tensor. -/
@[simp]
lemma tensor_obj_map_tmul (G : ModCat.{w} Cᵒᵖ) (β : F ⟶ F') (X : C)
    (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    (tensor.obj G).map β (tmul X x y) = tmul X x (β.hom.app (op X) y) :=
  coend_map_tmul (𝟙 G) β X x y

instance (G : ModCat.{w} Cᵒᵖ) : (tensor.obj G).Additive where
  map_add := by
    intro F F' f g
    apply tensorObj_hom_ext
    intro X x y
    simp only [tensor_obj_map_tmul, AddCommGrpCat.hom_add_apply]
    exact tmul_add X x _ _

instance (F : ModCat.{w} C) : (tensor.flip.obj F).Additive where
  map_add := by
    intro G G' f g
    apply tensorObj_hom_ext
    intro X x y
    -- Use the unflipped components so that the coercions of the maps match the simp lemma.
    change (tensor.map (f + g)).app F (tmul X x y) =
      (tensor.map f).app F (tmul X x y) + (tensor.map g).app F (tmul X x y)
    simp only [tensor_map_app_tmul]
    exact add_tmul X _ _ y

instance : (tensor (C := C)).Additive where
  map_add := by
    intro G G' f g
    apply NatTrans.ext
    funext F
    exact (tensor.flip.obj F).map_add

end CoendTensor

section Yoneda

variable [EssentiallySmall.{v} C]

private def yonedaLeftPairing (X Y : C) (F : ModCat.{v} C) :
    (op Y ⟶ op X) →ₗ[ℤ] F.obj.obj (op Y) →ₗ[ℤ] F.obj.obj (op X) :=
  letI : F.obj.Additive := (additiveFunctor_iff _).1 F.property
  (addMonoidHomLequivInt ℤ).toLinearMap.comp
    (AddCommGrpCat.homAddEquiv.toAddMonoidHom.comp F.obj.mapAddHom).toIntLinearMap

private def yonedaRightPairing (G : ModCat.{v} Cᵒᵖ) (X Y : C) :
    G.obj.obj (op (op Y)) →ₗ[ℤ] (Y ⟶ X) →ₗ[ℤ] G.obj.obj (op (op X)) :=
  ((yonedaLeftPairing (op X) (op Y) G).comp
    ((opHom (op X) (op Y)).comp (opHom Y X)).toIntLinearMap).flip

omit [EssentiallySmall.{v} C] in
private lemma yonedaRightPairing_balance (G : ModCat.{v} Cᵒᵖ) (X : C)
    {Y Z : C} (f : Y ⟶ Z) (x : G.obj.obj (op (op Y))) (g : Z ⟶ X) :
    yonedaRightPairing G X Z (G.obj.map f.op.op x) g = yonedaRightPairing G X Y x (f ≫ g) :=
  (ConcreteCategory.congr_hom (G.obj.map_comp f.op.op g.op.op) x).symm

/-- Tensoring a right module with the representable left module at `X` evaluates it at `X`. -/
noncomputable def tensorObjYonedaIso (G : ModCat.{v} Cᵒᵖ) (X : C) :
    tensorObj G ((yoneda C).obj X) ≅ G.obj.obj (op (op X)) where
  hom := tensorDesc (yonedaRightPairing G X) (fun _ _ f x g ↦ yonedaRightPairing_balance G X f x g)
  inv := AddCommGrpCat.ofHom
    (((tmulLinear (F := (yoneda C).obj X) X).flip (𝟙 X)).toAddMonoidHom)
  hom_inv_id := by
    apply tensorObj_hom_ext
    intro Y x f
    -- The generator of the representable module at `Y` is a morphism `Y ⟶ X`.
    change Y ⟶ X at f
    have hEval := tensorDesc_tmul (G := G) (F := (yoneda C).obj X) (yonedaRightPairing G X)
      (fun _ _ f x g ↦ yonedaRightPairing_balance G X f x g) Y x f
    have h := tmul_balance (F := (yoneda C).obj X) f x (𝟙 X)
    -- The representable's action in the second factor is precomposition.
    change tmul (F := (yoneda C).obj X) X (G.obj.map f.op.op x) (𝟙 X) =
      tmul (F := (yoneda C).obj X) Y x (f ≫ 𝟙 X) at h
    exact (congrArg (fun z ↦ tmul (F := (yoneda C).obj X) X z (𝟙 X)) hEval).trans
      (h.trans (congrArg (fun g : Y ⟶ X ↦ tmul (F := (yoneda C).obj X) Y x g)
        (Category.comp_id f)))
  inv_hom_id := by
    apply AddCommGrpCat.ext
    intro x
    -- The inverse inserts the identity of the representing object.
    change tensorDesc (F := (yoneda C).obj X) _ _
      (tmul (F := (yoneda C).obj X) X x (𝟙 X)) = x
    exact (tensorDesc_tmul (F := (yoneda C).obj X) _ _ X x (𝟙 X)).trans
      (ConcreteCategory.congr_hom (G.obj.map_id (op (op X))) x)

/-- Yoneda evaluation moves the morphism in the second factor to the right module. -/
@[simp]
lemma tensorObjYonedaIso_hom_tmul (G : ModCat.{v} Cᵒᵖ) {X Y : C}
    (x : G.obj.obj (op (op Y))) (f : Y ⟶ X) :
    (tensorObjYonedaIso G X).hom (tmul Y x f) = G.obj.map f.op.op x :=
  tensorDesc_tmul (G := G) (F := (yoneda C).obj X) (yonedaRightPairing G X)
    (fun _ _ f x g ↦ yonedaRightPairing_balance G X f x g) Y x f

/-- The inverse of Yoneda evaluation tensors with the representing identity. -/
@[simp]
lemma tensorObjYonedaIso_inv_apply (G : ModCat.{v} Cᵒᵖ) (X : C) (x : G.obj.obj (op (op X))) :
    (tensorObjYonedaIso G X).inv x = tmul X x (𝟙 X) :=
  (rfl)

omit [EssentiallySmall.{v} C] in
private lemma yonedaLeftPairing_balance (X : C) (F : ModCat.{v} C)
    {Y Z : C} (f : Y ⟶ Z) (g : op Y ⟶ op X) (y : F.obj.obj (op Z)) :
    yonedaLeftPairing X Z F (f.op ≫ g) y = yonedaLeftPairing X Y F g (F.obj.map f.op y) :=
  ConcreteCategory.congr_hom (F.obj.map_comp f.op g) y

/-- Tensoring the representable right module at `X` with a left module evaluates it at `X`. -/
noncomputable def yonedaTensorObjIso (X : C) (F : ModCat.{v} C) :
    tensorObj ((yoneda Cᵒᵖ).obj (op X)) F ≅ F.obj.obj (op X) where
  hom := tensorDesc (fun Y ↦ yonedaLeftPairing X Y F)
    (fun _ _ f g y ↦ yonedaLeftPairing_balance X F f g y)
  inv := AddCommGrpCat.ofHom
    ((tmulLinear (G := (yoneda Cᵒᵖ).obj (op X)) X (𝟙 (op X))).toAddMonoidHom)
  hom_inv_id := by
    apply tensorObj_hom_ext
    intro Y f y
    -- The generator of the right representable is a morphism in the opposite category.
    change op Y ⟶ op X at f
    have hEval := tensorDesc_tmul (G := (yoneda Cᵒᵖ).obj (op X)) (F := F)
      (fun Y ↦ yonedaLeftPairing X Y F) (fun _ _ f g y ↦ yonedaLeftPairing_balance X F f g y) Y f y
    have h := tmul_balance (G := (yoneda Cᵒᵖ).obj (op X)) f.unop (𝟙 (op X)) y
    -- The right representable acts by precomposition in the opposite category.
    change tmul (G := (yoneda Cᵒᵖ).obj (op X)) Y (f ≫ 𝟙 (op X)) y =
      tmul (G := (yoneda Cᵒᵖ).obj (op X)) X (𝟙 (op X)) (F.obj.map f y) at h
    exact (congrArg (fun z ↦ tmul (G := (yoneda Cᵒᵖ).obj (op X)) X (𝟙 (op X)) z) hEval).trans
      (h.symm.trans (congrArg (fun g : op Y ⟶ op X ↦ tmul (G := (yoneda Cᵒᵖ).obj (op X)) Y g y)
        (Category.comp_id f)))
  inv_hom_id := by
    apply AddCommGrpCat.ext
    intro y
    -- The inverse inserts the identity into the right representable.
    change tensorDesc (G := (yoneda Cᵒᵖ).obj (op X)) _ _
      (tmul (G := (yoneda Cᵒᵖ).obj (op X)) X (𝟙 (op X)) y) = y
    exact (tensorDesc_tmul (G := (yoneda Cᵒᵖ).obj (op X)) _ _ X (𝟙 (op X)) y).trans
      (ConcreteCategory.congr_hom (F.obj.map_id (op X)) y)

/-- Yoneda evaluation moves the morphism in the first factor to the left module. -/
@[simp]
lemma yonedaTensorObjIso_hom_tmul {X Y : C} (F : ModCat.{v} C)
    (f : op Y ⟶ op X) (y : F.obj.obj (op Y)) :
    (yonedaTensorObjIso X F).hom (tmul Y f y) = F.obj.map f y :=
  tensorDesc_tmul (G := (yoneda Cᵒᵖ).obj (op X)) (F := F) (fun Y ↦ yonedaLeftPairing X Y F)
    (fun _ _ f g y ↦ yonedaLeftPairing_balance X F f g y) Y f y

/-- The inverse of Yoneda evaluation tensors with the representing identity. -/
@[simp]
lemma yonedaTensorObjIso_inv_apply (X : C) (F : ModCat.{v} C) (y : F.obj.obj (op X)) :
    (yonedaTensorObjIso X F).inv y = tmul X (𝟙 (op X)) y :=
  (rfl)

private lemma tensorObjYonedaIso_naturality {G G' : ModCat.{v} Cᵒᵖ} (α : G ⟶ G') (X : C) :
    (tensor.map α).app ((yoneda C).obj X) ≫ (tensorObjYonedaIso G' X).hom =
      (tensorObjYonedaIso G X).hom ≫ α.hom.app (op (op X)) := by
  apply tensorObj_hom_ext (G := G) (F := (yoneda C).obj X)
  intro Y x f
  -- Express elements of the representable module as morphisms for the evaluation formula.
  change Y ⟶ X at f
  simpa only [comp_apply, tensor_map_app_tmul α ((yoneda C).obj X) Y x f,
    tensorObjYonedaIso_hom_tmul] using
    (ConcreteCategory.congr_hom (α.hom.naturality f.op.op) x).symm

private lemma yonedaTensorObjIso_naturality {F F' : ModCat.{v} C} (β : F ⟶ F') (X : C) :
    (tensor.obj ((yoneda Cᵒᵖ).obj (op X))).map β ≫ (yonedaTensorObjIso X F').hom =
      (yonedaTensorObjIso X F).hom ≫ β.hom.app (op X) := by
  apply tensorObj_hom_ext (G := (yoneda Cᵒᵖ).obj (op X)) (F := F)
  intro Y f y
  -- Express elements of the right representable as morphisms in the opposite category.
  change op Y ⟶ op X at f
  simpa only [comp_apply, tensor_obj_map_tmul ((yoneda Cᵒᵖ).obj (op X)) β Y f y,
    yonedaTensorObjIso_hom_tmul] using
    (ConcreteCategory.congr_hom (β.hom.naturality f) y).symm

/-- Tensoring with a fixed left representable is naturally isomorphic to evaluation. -/
noncomputable def tensorYonedaIso (X : C) :
    tensor.flip.obj ((yoneda C).obj X) ≅
      (additiveFunctor _ _).ι ⋙ (CategoryTheory.evaluation _ _).obj (op (op X)) :=
  NatIso.ofComponents (fun G ↦ tensorObjYonedaIso G X)
    (fun {_ _} α ↦ tensorObjYonedaIso_naturality α X)

/-- Tensoring with a fixed right representable is naturally isomorphic to evaluation. -/
noncomputable def yonedaTensorIso (X : C) :
    tensor.obj ((yoneda Cᵒᵖ).obj (op X)) ≅
      (additiveFunctor _ _).ι ⋙ (CategoryTheory.evaluation _ _).obj (op X) :=
  NatIso.ofComponents (fun F ↦ yonedaTensorObjIso X F)
    (fun {_ _} β ↦ yonedaTensorObjIso_naturality β X)

@[simp]
lemma tensorYonedaIso_app (X : C) (G : ModCat.{v} Cᵒᵖ) :
    (tensorYonedaIso X).app G = tensorObjYonedaIso G X :=
  (rfl)

@[simp]
lemma yonedaTensorIso_app (X : C) (F : ModCat.{v} C) :
    (yonedaTensorIso X).app F = yonedaTensorObjIso X F :=
  (rfl)

end Yoneda

end ModCat

end TauCeti
