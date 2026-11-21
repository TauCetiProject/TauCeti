/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Projection formulas and internal Hom

Let `C` and `D` be monoidal categories, `F : D ⥤ C` a functor and `L ⊣ R` an adjunction with
`L : C ⥤ D`. A *projection formula* is a natural isomorphism relating `L` with tensor products,
such as `L (B ⊗ F A) ≅ L B ⊗ A`. Under the tensor--Hom adjunctions, such an isomorphism of left
adjoints corresponds to an isomorphism of right adjoints, which is a duality statement for
internal Homs. This is the formal Yoneda argument behind Verdier duality for an exceptional
pushforward `f_! ⊣ f^!` together with `f^* ⊣ f_*`.

* Given also `F ⊣ G` and `B : C`, a projection formula `F ⋙ tensorLeft B ⋙ L ≅ tensorLeft (L B)`,
  natural in `A : D`, is the same as an isomorphism `ihom (L B) ≅ R ⋙ ihom B ⋙ G`, that is,
  `[L B, A'] ≅ G [B, R A']` naturally in `A' : D`
  (`CategoryTheory.MonoidalClosed.ihomLeftAdjointObjEquiv`).
* Given `A : D` and `B : C`, a projection formula `L ⋙ tensorLeft A ≅ tensorLeft B ⋙ L`, natural
  in the source object, is the same as an isomorphism `R ⋙ ihom B ≅ ihom A ⋙ R`, that is,
  `[B, R A'] ≅ R [A, A']` naturally in `A'`
  (`CategoryTheory.MonoidalClosed.ihomRightAdjointEquiv`). In applications `B = F A`, and no
  adjoint of `F` is needed here.

In both cases the correspondence is Mathlib's conjugation of natural isomorphisms between adjoint
functors (`CategoryTheory.conjugateIsoEquiv`) for composites of the given adjunctions with the
tensor--Hom adjunctions. When the projection formulas are natural in the remaining variable as well,
so are the dualities, and we assemble them into isomorphisms of internal-Hom bifunctors
(`CategoryTheory.MonoidalClosed.ihomLeftAdjointIso`,
`CategoryTheory.MonoidalClosed.ihomRightAdjointIso`).

The projection formula is often given with the tensor factor on the other side, as
`L X ⊗ A ≅ L (X ⊗ F A)` naturally in `X`; in braided categories,
`CategoryTheory.BraidedCategory.tensorRightIsoEquivTensorLeftIso` converts it into the form used
by the second duality.

## References

* P. Scholze, *Étale cohomology of diamonds*, proof of Proposition 23.3.
-/

public section

namespace CategoryTheory

open MonoidalCategory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]

namespace MonoidalClosed

section LeftAdjointObj

variable {F : D ⥤ C} {G : C ⥤ D} {L : C ⥤ D} {R : D ⥤ C} (adj₁ : F ⊣ G) (adj₂ : L ⊣ R)

/-- Let `F ⊣ G` and `L ⊣ R` be adjunctions with `F : D ⥤ C` and `L : C ⥤ D`, and `B : C`.
Projection formulas `L (B ⊗ F A) ≅ L B ⊗ A`, natural in `A : D`, correspond bijectively to
duality isomorphisms `[L B, A'] ≅ G [B, R A']`, natural in `A' : D`: both functors
`F ⋙ tensorLeft B ⋙ L` and `tensorLeft (L B)` are left adjoints, to `R ⋙ ihom B ⋙ G` and
`ihom (L B)`, and the correspondence is conjugation of natural isomorphisms. -/
def ihomLeftAdjointObjEquiv (B : C) [Closed B] [Closed (L.obj B)] :
    (F ⋙ tensorLeft B ⋙ L ≅ tensorLeft (L.obj B)) ≃ (ihom (L.obj B) ≅ R ⋙ ihom B ⋙ G) :=
  conjugateIsoEquiv (ihom.adjunction (L.obj B)) (adj₁.comp ((ihom.adjunction B).comp adj₂))

@[simp]
theorem ihomLeftAdjointObjEquiv_apply_hom (B : C) [Closed B] [Closed (L.obj B)]
    (e : F ⋙ tensorLeft B ⋙ L ≅ tensorLeft (L.obj B)) :
    (ihomLeftAdjointObjEquiv adj₁ adj₂ B e).hom = conjugateEquiv (ihom.adjunction (L.obj B))
      (adj₁.comp ((ihom.adjunction B).comp adj₂)) e.hom :=
  (rfl)

@[simp]
theorem ihomLeftAdjointObjEquiv_apply_inv (B : C) [Closed B] [Closed (L.obj B)]
    (e : F ⋙ tensorLeft B ⋙ L ≅ tensorLeft (L.obj B)) :
    (ihomLeftAdjointObjEquiv adj₁ adj₂ B e).inv = conjugateEquiv
      (adj₁.comp ((ihom.adjunction B).comp adj₂)) (ihom.adjunction (L.obj B)) e.inv :=
  (rfl)

@[simp]
theorem ihomLeftAdjointObjEquiv_symm_apply_hom (B : C) [Closed B] [Closed (L.obj B)]
    (φ : ihom (L.obj B) ≅ R ⋙ ihom B ⋙ G) :
    ((ihomLeftAdjointObjEquiv adj₁ adj₂ B).symm φ).hom = (conjugateEquiv
      (ihom.adjunction (L.obj B)) (adj₁.comp ((ihom.adjunction B).comp adj₂))).symm φ.hom :=
  (rfl)

@[simp]
theorem ihomLeftAdjointObjEquiv_symm_apply_inv (B : C) [Closed B] [Closed (L.obj B)]
    (φ : ihom (L.obj B) ≅ R ⋙ ihom B ⋙ G) :
    ((ihomLeftAdjointObjEquiv adj₁ adj₂ B).symm φ).inv = (conjugateEquiv
      (adj₁.comp ((ihom.adjunction B).comp adj₂)) (ihom.adjunction (L.obj B))).symm φ.inv :=
  (rfl)

/-- The duality isomorphism `ihomLeftAdjointObjEquiv adj₁ adj₂ B e` is characterised by its
compatibility with evaluation: transporting it along the two adjunctions to a morphism
`L (B ⊗ F [L B, A']) ⟶ A'` gives `e` followed by evaluation. -/
@[reassoc]
theorem ihomLeftAdjointObjEquiv_hom_app_comp_counit (B : C) [Closed B] [Closed (L.obj B)]
    (e : F ⋙ tensorLeft B ⋙ L ≅ tensorLeft (L.obj B)) (A' : D) :
    L.map (B ◁ F.map ((ihomLeftAdjointObjEquiv adj₁ adj₂ B e).hom.app A')) ≫
        L.map (B ◁ adj₁.counit.app ((ihom B).obj (R.obj A'))) ≫
          L.map ((ihom.ev B).app (R.obj A')) ≫ adj₂.counit.app A' =
      e.hom.app ((ihom (L.obj B)).obj A') ≫ (ihom.ev (L.obj B)).app A' := by
  simpa only [ihomLeftAdjointObjEquiv_apply_hom, Adjunction.comp_counit_app,
    Functor.comp_obj, Functor.comp_map, ihom.ihom_adjunction_counit, curriedTensor_obj_map] using
    conjugateEquiv_counit (ihom.adjunction (L.obj B)) (adj₁.comp ((ihom.adjunction B).comp adj₂))
      e.hom A'

/-- Naturality of `ihomLeftAdjointObjEquiv` in the object `B`: if the projection formulas `e₁`
at `B₁` and `e₂` at `B₂` are compatible with `g : B₁ ⟶ B₂`, then so are the corresponding
duality isomorphisms, with precomposition by `L.map g` and by `g` on the two sides. -/
theorem pre_app_comp_ihomLeftAdjointObjEquiv_hom_app {B₁ B₂ : C} [Closed B₁] [Closed B₂]
    [Closed (L.obj B₁)] [Closed (L.obj B₂)] (g : B₁ ⟶ B₂)
    (e₁ : F ⋙ tensorLeft B₁ ⋙ L ≅ tensorLeft (L.obj B₁))
    (e₂ : F ⋙ tensorLeft B₂ ⋙ L ≅ tensorLeft (L.obj B₂))
    (h : ∀ A : D, L.map (g ▷ F.obj A) ≫ e₂.hom.app A = e₁.hom.app A ≫ L.map g ▷ A) (A' : D) :
    (pre (L.map g)).app A' ≫ (ihomLeftAdjointObjEquiv adj₁ adj₂ B₁ e₁).hom.app A' =
      (ihomLeftAdjointObjEquiv adj₁ adj₂ B₂ e₂).hom.app A' ≫ G.map ((pre g).app (R.obj A')) := by
  have h' : Functor.whiskerLeft F (Functor.whiskerRight ((curriedTensor C).map g) L) ≫ e₂.hom =
      e₁.hom ≫ (curriedTensor D).map (L.map g) := by
    ext A
    exact h A
  have := congr_arg (conjugateEquiv (ihom.adjunction (L.obj B₂))
    (adj₁.comp ((ihom.adjunction B₁).comp adj₂))) h'
  rw [← conjugateEquiv_comp _ (adj₁.comp ((ihom.adjunction B₂).comp adj₂)),
    ← conjugateEquiv_comp _ (ihom.adjunction (L.obj B₁)), conjugateEquiv_whiskerLeft,
    conjugateEquiv_whiskerRight] at this
  rw [pre, pre]
  exact (congr_app this A').symm

variable [MonoidalClosed C] [MonoidalClosed D]

/-- The duality isomorphism `[L B, A'] ≅ G [B, R A']` as an isomorphism of bifunctors
`Cᵒᵖ ⥤ D ⥤ D`, natural in both `B` and `A'`, built from a projection formula
`L B ⊗ A ≅ L (B ⊗ F A)` natural in both `B` and `A`. Its components are given by
`ihomLeftAdjointObjEquiv` (`ihomLeftAdjointIso_hom_app_app`). -/
def ihomLeftAdjointIso
    (π : L ⋙ curriedTensor D ≅
      curriedTensor C ⋙ (Functor.whiskeringLeft D C C).obj F ⋙
        (Functor.whiskeringRight D C D).obj L) :
    L.op ⋙ internalHom ≅
      internalHom ⋙ (Functor.whiskeringLeft D C C).obj R ⋙
        (Functor.whiskeringRight D C D).obj G :=
  NatIso.ofComponents (fun B ↦ ihomLeftAdjointObjEquiv adj₁ adj₂ B.unop (π.app B.unop).symm)
    fun {B₁ B₂} f ↦ by
      ext A'
      exact pre_app_comp_ihomLeftAdjointObjEquiv_hom_app adj₁ adj₂ f.unop _ _
        (fun A ↦ by simpa using NatTrans.congr_app (π.inv.naturality f.unop) A) A'

@[simp]
theorem ihomLeftAdjointIso_hom_app_app
    (π : L ⋙ curriedTensor D ≅
      curriedTensor C ⋙ (Functor.whiskeringLeft D C C).obj F ⋙
        (Functor.whiskeringRight D C D).obj L) (B : Cᵒᵖ) (A' : D) :
    ((ihomLeftAdjointIso adj₁ adj₂ π).hom.app B).app A' =
      (ihomLeftAdjointObjEquiv adj₁ adj₂ B.unop (π.app B.unop).symm).hom.app A' :=
  (rfl)

@[simp]
theorem ihomLeftAdjointIso_inv_app_app
    (π : L ⋙ curriedTensor D ≅
      curriedTensor C ⋙ (Functor.whiskeringLeft D C C).obj F ⋙
        (Functor.whiskeringRight D C D).obj L) (B : Cᵒᵖ) (A' : D) :
    ((ihomLeftAdjointIso adj₁ adj₂ π).inv.app B).app A' =
      (ihomLeftAdjointObjEquiv adj₁ adj₂ B.unop (π.app B.unop).symm).inv.app A' :=
  (rfl)

end LeftAdjointObj

section RightAdjoint

variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- Let `L ⊣ R` be an adjunction with `L : C ⥤ D`, and let `A : D` and `B : C`.
Projection formulas `A ⊗ L X ≅ L (B ⊗ X)`, natural in `X : C`, correspond bijectively to
isomorphisms `[B, R A'] ≅ R [A, A']`, natural in `A' : D`: the functors `L ⋙ tensorLeft A` and
`tensorLeft B ⋙ L` are left adjoints, to `ihom A ⋙ R` and `R ⋙ ihom B`, and the
correspondence is conjugation of natural isomorphisms. -/
def ihomRightAdjointEquiv (A : D) (B : C) [Closed A] [Closed B] :
    (L ⋙ tensorLeft A ≅ tensorLeft B ⋙ L) ≃ (R ⋙ ihom B ≅ ihom A ⋙ R) :=
  conjugateIsoEquiv ((ihom.adjunction B).comp adj) (adj.comp (ihom.adjunction A))

@[simp]
theorem ihomRightAdjointEquiv_apply_hom (A : D) (B : C) [Closed A] [Closed B]
    (e : L ⋙ tensorLeft A ≅ tensorLeft B ⋙ L) :
    (ihomRightAdjointEquiv adj A B e).hom = conjugateEquiv ((ihom.adjunction B).comp adj)
      (adj.comp (ihom.adjunction A)) e.hom :=
  (rfl)

@[simp]
theorem ihomRightAdjointEquiv_apply_inv (A : D) (B : C) [Closed A] [Closed B]
    (e : L ⋙ tensorLeft A ≅ tensorLeft B ⋙ L) :
    (ihomRightAdjointEquiv adj A B e).inv = conjugateEquiv (adj.comp (ihom.adjunction A))
      ((ihom.adjunction B).comp adj) e.inv :=
  (rfl)

@[simp]
theorem ihomRightAdjointEquiv_symm_apply_hom (A : D) (B : C) [Closed A] [Closed B]
    (ψ : R ⋙ ihom B ≅ ihom A ⋙ R) :
    ((ihomRightAdjointEquiv adj A B).symm ψ).hom = (conjugateEquiv
      ((ihom.adjunction B).comp adj) (adj.comp (ihom.adjunction A))).symm ψ.hom :=
  (rfl)

@[simp]
theorem ihomRightAdjointEquiv_symm_apply_inv (A : D) (B : C) [Closed A] [Closed B]
    (ψ : R ⋙ ihom B ≅ ihom A ⋙ R) :
    ((ihomRightAdjointEquiv adj A B).symm ψ).inv = (conjugateEquiv
      (adj.comp (ihom.adjunction A)) ((ihom.adjunction B).comp adj)).symm ψ.inv :=
  (rfl)

/-- The isomorphism `ihomRightAdjointEquiv adj A B e` is characterised by its compatibility with
evaluation: transporting it along the two adjunctions to a morphism `A ⊗ L [B, R A'] ⟶ A'`
gives `e` followed by evaluation. -/
@[reassoc]
theorem ihomRightAdjointEquiv_hom_app_comp_counit (A : D) (B : C) [Closed A] [Closed B]
    (e : L ⋙ tensorLeft A ≅ tensorLeft B ⋙ L) (A' : D) :
    A ◁ L.map ((ihomRightAdjointEquiv adj A B e).hom.app A') ≫
        A ◁ adj.counit.app ((ihom A).obj A') ≫ (ihom.ev A).app A' =
      e.hom.app ((ihom B).obj (R.obj A')) ≫
        L.map ((ihom.ev B).app (R.obj A')) ≫ adj.counit.app A' := by
  simpa only [ihomRightAdjointEquiv_apply_hom, Adjunction.comp_counit_app,
    Functor.comp_obj, Functor.comp_map, Category.assoc, ihom.ihom_adjunction_counit,
    curriedTensor_obj_map] using
    conjugateEquiv_counit ((ihom.adjunction B).comp adj) (adj.comp (ihom.adjunction A))
      e.hom A'

/-- Naturality of `ihomRightAdjointEquiv` in the objects `A` and `B`: if the projection formulas
`e₁` at `(A₁, B₁)` and `e₂` at `(A₂, B₂)` are compatible with `g : A₁ ⟶ A₂` and `g' : B₁ ⟶ B₂`,
then so are the corresponding isomorphisms, with precomposition by `g'` and by `g` on the two
sides. -/
theorem pre_app_comp_ihomRightAdjointEquiv_hom_app {A₁ A₂ : D} {B₁ B₂ : C} [Closed A₁]
    [Closed A₂] [Closed B₁] [Closed B₂] (g : A₁ ⟶ A₂) (g' : B₁ ⟶ B₂)
    (e₁ : L ⋙ tensorLeft A₁ ≅ tensorLeft B₁ ⋙ L)
    (e₂ : L ⋙ tensorLeft A₂ ≅ tensorLeft B₂ ⋙ L)
    (h : ∀ X : C, g ▷ L.obj X ≫ e₂.hom.app X = e₁.hom.app X ≫ L.map (g' ▷ X)) (A' : D) :
    (pre g').app (R.obj A') ≫ (ihomRightAdjointEquiv adj A₁ B₁ e₁).hom.app A' =
      (ihomRightAdjointEquiv adj A₂ B₂ e₂).hom.app A' ≫ R.map ((pre g).app A') := by
  have h' : Functor.whiskerLeft L ((curriedTensor D).map g) ≫ e₂.hom =
      e₁.hom ≫ Functor.whiskerRight ((curriedTensor C).map g') L := by
    ext X
    exact h X
  have := congr_arg (conjugateEquiv ((ihom.adjunction B₂).comp adj)
    (adj.comp (ihom.adjunction A₁))) h'
  rw [← conjugateEquiv_comp _ (adj.comp (ihom.adjunction A₂)),
    ← conjugateEquiv_comp _ ((ihom.adjunction B₁).comp adj), conjugateEquiv_whiskerLeft,
    conjugateEquiv_whiskerRight] at this
  rw [pre, pre]
  exact (congr_app this A').symm

variable [MonoidalClosed C] [MonoidalClosed D] {F : D ⥤ C}

/-- The isomorphism `[F A, R A'] ≅ R [A, A']` as an isomorphism of bifunctors `Dᵒᵖ ⥤ D ⥤ C`,
natural in both `A` and `A'`, built from a projection formula `A ⊗ L X ≅ L (F A ⊗ X)` natural in
both `A` and `X`. Its components are given by `ihomRightAdjointEquiv`
(`ihomRightAdjointIso_hom_app_app`). -/
def ihomRightAdjointIso
    (π : curriedTensor D ⋙ (Functor.whiskeringLeft C D D).obj L ≅
      F ⋙ curriedTensor C ⋙ (Functor.whiskeringRight C C D).obj L) :
    F.op ⋙ internalHom ⋙ (Functor.whiskeringLeft D C C).obj R ≅
      internalHom ⋙ (Functor.whiskeringRight D D C).obj R :=
  NatIso.ofComponents (fun A ↦ ihomRightAdjointEquiv adj A.unop (F.obj A.unop) (π.app A.unop))
    fun {A₁ A₂} f ↦ by
      ext A'
      exact pre_app_comp_ihomRightAdjointEquiv_hom_app adj f.unop (F.map f.unop) _ _
        (fun X ↦ by simpa using NatTrans.congr_app (π.hom.naturality f.unop) X) A'

@[simp]
theorem ihomRightAdjointIso_hom_app_app
    (π : curriedTensor D ⋙ (Functor.whiskeringLeft C D D).obj L ≅
      F ⋙ curriedTensor C ⋙ (Functor.whiskeringRight C C D).obj L) (A : Dᵒᵖ) (A' : D) :
    ((ihomRightAdjointIso adj π).hom.app A).app A' =
      (ihomRightAdjointEquiv adj A.unop (F.obj A.unop) (π.app A.unop)).hom.app A' :=
  (rfl)

@[simp]
theorem ihomRightAdjointIso_inv_app_app
    (π : curriedTensor D ⋙ (Functor.whiskeringLeft C D D).obj L ≅
      F ⋙ curriedTensor C ⋙ (Functor.whiskeringRight C C D).obj L) (A : Dᵒᵖ) (A' : D) :
    ((ihomRightAdjointIso adj π).inv.app A).app A' =
      (ihomRightAdjointEquiv adj A.unop (F.obj A.unop) (π.app A.unop)).inv.app A' :=
  (rfl)

end RightAdjoint

end MonoidalClosed

namespace BraidedCategory

variable [BraidedCategory C] [BraidedCategory D] (L : C ⥤ D) (A : D) (B : C)

/-- In braided categories, the braidings convert projection formulas `L X ⊗ A ≅ L (X ⊗ B)`,
natural in `X`, into projection formulas `A ⊗ L X ≅ L (B ⊗ X)`, natural in `X`, and back. -/
def tensorRightIsoEquivTensorLeftIso :
    (L ⋙ tensorRight A ≅ tensorRight B ⋙ L) ≃ (L ⋙ tensorLeft A ≅ tensorLeft B ⋙ L) :=
  Iso.isoCongr (Functor.isoWhiskerLeft L (tensorLeftIsoTensorRight A).symm)
    (Functor.isoWhiskerRight (tensorLeftIsoTensorRight B).symm L)

@[simp]
theorem tensorRightIsoEquivTensorLeftIso_apply_hom_app
    (e : L ⋙ tensorRight A ≅ tensorRight B ⋙ L) (X : C) :
    (tensorRightIsoEquivTensorLeftIso L A B e).hom.app X =
      (β_ A (L.obj X)).hom ≫ e.hom.app X ≫ L.map (β_ B X).inv := by
  simp [tensorRightIsoEquivTensorLeftIso, tensorLeftIsoTensorRight]

@[simp]
theorem tensorRightIsoEquivTensorLeftIso_apply_inv_app
    (e : L ⋙ tensorRight A ≅ tensorRight B ⋙ L) (X : C) :
    (tensorRightIsoEquivTensorLeftIso L A B e).inv.app X =
      L.map (β_ B X).hom ≫ e.inv.app X ≫ (β_ A (L.obj X)).inv := by
  simp [tensorRightIsoEquivTensorLeftIso, tensorLeftIsoTensorRight]

@[simp]
theorem tensorRightIsoEquivTensorLeftIso_symm_apply_hom_app
    (e : L ⋙ tensorLeft A ≅ tensorLeft B ⋙ L) (X : C) :
    ((tensorRightIsoEquivTensorLeftIso L A B).symm e).hom.app X =
      (β_ A (L.obj X)).inv ≫ e.hom.app X ≫ L.map (β_ B X).hom := by
  simp [tensorRightIsoEquivTensorLeftIso, tensorLeftIsoTensorRight]

@[simp]
theorem tensorRightIsoEquivTensorLeftIso_symm_apply_inv_app
    (e : L ⋙ tensorLeft A ≅ tensorLeft B ⋙ L) (X : C) :
    ((tensorRightIsoEquivTensorLeftIso L A B).symm e).inv.app X =
      L.map (β_ B X).inv ≫ e.inv.app X ≫ (β_ A (L.obj X)).hom := by
  simp [tensorRightIsoEquivTensorLeftIso, tensorLeftIsoTensorRight]

end BraidedCategory

end CategoryTheory
