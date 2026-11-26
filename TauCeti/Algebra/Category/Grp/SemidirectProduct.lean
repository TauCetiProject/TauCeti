/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Semidirect products of group-valued functors

Let `N` and `G` be functors from a category `C` to groups, and let each `G(X)` act on `N(X)` by
group automorphisms `φ_X : G(X) →* MulAut N(X)`, compatibly with the maps of both functors:
`N(f) (φ_X g n) = φ_Y (G(f) g) (N(f) n)` for `f : X ⟶ Y`. Then `X ↦ N(X) ⋊[φ_X] G(X)` is a
group-valued functor, acting on morphisms by Mathlib's `SemidirectProduct.map` of the maps of `N`
and `G`, and its functor laws are those of `N` and `G`.

Natural transformations `N ⟶ N'` and `G ⟶ G'` compatible with the actions induce a natural
transformation of the semidirect products. The projections `N(X) ⋊ G(X) → G(X)` and the sections
`g ↦ (1, g)` are natural; as `N(X) ⋊ G(X)` lives in the larger of the two universes, they are
stated for `G` lifted along `GrpCat.uliftFunctor`. The inclusions `n ↦ (n, 1)` of the normal
factor are natural as well, and commute with the induced maps of semidirect products; they are
stated for `N` valued in a universe containing that of `G`, so that `N` needs no lift.

## Main definitions

* `TauCeti.GrpCat.semidirectProductFunctor N G φ hφ`: the group functor `X ↦ N(X) ⋊[φ_X] G(X)`.
* `TauCeti.GrpCat.semidirectProductMap α β h`: the natural transformation of semidirect products
  induced by compatible natural transformations `α : N ⟶ N'` and `β : G ⟶ G'`, injective where
  `α` and `β` are (`TauCeti.GrpCat.semidirectProductMap_app_injective`).
* `TauCeti.GrpCat.semidirectProductRightHom N G φ hφ`: the natural projection to `G`.
* `TauCeti.GrpCat.semidirectProductInr N G φ hφ`: the natural section `g ↦ (1, g)`, with
  `TauCeti.GrpCat.semidirectProductInr_comp_rightHom`.
* `TauCeti.GrpCat.semidirectProductInl N G φ hφ`: the natural inclusion `n ↦ (n, 1)` of the normal
  factor, with `TauCeti.GrpCat.semidirectProductInl_comp_map`.
-/

public section

open CategoryTheory

universe v u₁ u₂ u

namespace TauCeti.GrpCat

variable {C : Type u} [Category.{v} C] (N : C ⥤ _root_.GrpCat.{u₁}) (G : C ⥤ _root_.GrpCat.{u₂})
  (φ : ∀ X, G.obj X →* MulAut (N.obj X))
  (hφ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (g : G.obj X) (n : N.obj X),
    N.map f (φ X g n) = φ Y (G.map f g) (N.map f n))

/-- The semidirect product `X ↦ N(X) ⋊[φ_X] G(X)` of group-valued functors, for actions `φ_X`
compatible with the maps of `N` and `G`. A morphism `f` acts by `N(f)` and `G(f)` on the two
factors. -/
-- The object carrier must unfold, so that the objects are seen as semidirect products.
@[expose] def semidirectProductFunctor : C ⥤ _root_.GrpCat.{max u₁ u₂} where
  obj X := _root_.GrpCat.of (N.obj X ⋊[φ X] G.obj X)
  map f := _root_.GrpCat.ofHom <| SemidirectProduct.map (N.map f).hom (G.map f).hom
    fun g ↦ MonoidHom.ext fun n ↦ hφ f g n
  map_id X := _root_.GrpCat.ext fun x ↦ SemidirectProduct.ext
    (by simp [SemidirectProduct.map_left]) (by simp [SemidirectProduct.map_right])
  map_comp f g := _root_.GrpCat.ext fun x ↦ SemidirectProduct.ext
    (by simp [SemidirectProduct.map_left]) (by simp [SemidirectProduct.map_right])

/-- The value of the semidirect-product functor at `X` is `N(X) ⋊[φ_X] G(X)`. -/
lemma semidirectProductFunctor_obj (X : C) :
    (semidirectProductFunctor N G φ hφ).obj X = _root_.GrpCat.of (N.obj X ⋊[φ X] G.obj X) :=
  (rfl)

/-- A morphism `f` acts on the semidirect product by `N(f)` and `G(f)` on the two factors. -/
@[simp]
lemma semidirectProductFunctor_map_apply {X Y : C} (f : X ⟶ Y)
    (x : N.obj X ⋊[φ X] G.obj X) :
    (semidirectProductFunctor N G φ hφ).map f x = ⟨N.map f x.left, G.map f x.right⟩ :=
  (rfl)

section Map

variable {N G φ hφ} {N' : C ⥤ _root_.GrpCat.{u₁}} {G' : C ⥤ _root_.GrpCat.{u₂}}
  {φ' : ∀ X, G'.obj X →* MulAut (N'.obj X)}
  {hφ' : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (g : G'.obj X) (n : N'.obj X),
    N'.map f (φ' X g n) = φ' Y (G'.map f g) (N'.map f n)}

/-- The natural transformation `N ⋊ G ⟶ N' ⋊ G'` induced by natural transformations `α : N ⟶ N'`
and `β : G ⟶ G'` compatible with the actions. -/
def semidirectProductMap (α : N ⟶ N') (β : G ⟶ G')
    (h : ∀ X (g : G.obj X) (n : N.obj X), α.app X (φ X g n) = φ' X (β.app X g) (α.app X n)) :
    semidirectProductFunctor N G φ hφ ⟶ semidirectProductFunctor N' G' φ' hφ' where
  app X := _root_.GrpCat.ofHom <| SemidirectProduct.map (α.app X).hom (β.app X).hom
    fun g ↦ MonoidHom.ext fun n ↦ h X g n
  naturality _ _ f := _root_.GrpCat.ext fun x ↦ SemidirectProduct.ext
    (congr($(α.naturality f) x.left) :) (congr($(β.naturality f) x.right) :)

/-- The induced map of semidirect products applies `α` and `β` to the two factors. -/
@[simp]
lemma semidirectProductMap_app_apply (α : N ⟶ N') (β : G ⟶ G')
    (h : ∀ X (g : G.obj X) (n : N.obj X), α.app X (φ X g n) = φ' X (β.app X g) (α.app X n))
    (X : C) (x : N.obj X ⋊[φ X] G.obj X) :
    (semidirectProductMap (hφ := hφ) (hφ' := hφ') α β h).app X x =
      ⟨α.app X x.left, β.app X x.right⟩ :=
  (rfl)

/-- The induced map of semidirect products is injective at `X` when `α` and `β` are. -/
theorem semidirectProductMap_app_injective (α : N ⟶ N') (β : G ⟶ G')
    (h : ∀ X (g : G.obj X) (n : N.obj X), α.app X (φ X g n) = φ' X (β.app X g) (α.app X n))
    (X : C) (hα : Function.Injective (α.app X)) (hβ : Function.Injective (β.app X)) :
    Function.Injective ((semidirectProductMap (hφ := hφ) (hφ' := hφ') α β h).app X) :=
  fun _ _ hxy ↦ SemidirectProduct.ext (hα congr(($hxy).left)) (hβ congr(($hxy).right))

end Map

/-- The projections `N(X) ⋊ G(X) → G(X)`, natural in `X`, with `G` lifted to the universe of the
semidirect product. -/
def semidirectProductRightHom :
    semidirectProductFunctor N G φ hφ ⟶ G ⋙ _root_.GrpCat.uliftFunctor.{u₁} where
  app _ := _root_.GrpCat.ofHom <| MulEquiv.ulift.symm.toMonoidHom.comp SemidirectProduct.rightHom
  naturality _ _ f := _root_.GrpCat.ext fun x ↦ congrArg ULift.up <| DFunLike.congr_fun
    (SemidirectProduct.rightHom_comp_map (N.map f).hom (G.map f).hom
      fun g ↦ MonoidHom.ext fun n ↦ hφ f g n) x

/-- The projection to `G` sends `(n, g)` to `g`. -/
lemma semidirectProductRightHom_app_apply (X : C) (x : N.obj X ⋊[φ X] G.obj X) :
    (semidirectProductRightHom N G φ hφ).app X x = ULift.up x.right :=
  (rfl)

/-- The sections `g ↦ (1, g)` of the projections `N(X) ⋊ G(X) → G(X)`, natural in `X`. -/
def semidirectProductInr :
    G ⋙ _root_.GrpCat.uliftFunctor.{u₁} ⟶ semidirectProductFunctor N G φ hφ where
  app X := _root_.GrpCat.ofHom <| SemidirectProduct.inr.comp
    (MulEquiv.ulift : ULift.{u₁} (G.obj X) ≃* G.obj X).toMonoidHom
  naturality _ _ f :=
    _root_.GrpCat.ext fun g ↦ (SemidirectProduct.map_inr (N.map f).hom (G.map f).hom
      (fun g ↦ MonoidHom.ext fun n ↦ hφ f g n) g.down).symm

/-- The section of the projection to `G` sends `g` to `(1, g)`. -/
lemma semidirectProductInr_app_apply (X : C) (g : ULift.{u₁} (G.obj X)) :
    (semidirectProductInr N G φ hφ).app X g = SemidirectProduct.inr g.down :=
  (rfl)

/-- The natural sections `g ↦ (1, g)` are sections of the natural projections to `G`. -/
@[simp]
theorem semidirectProductInr_comp_rightHom :
    semidirectProductInr N G φ hφ ≫ semidirectProductRightHom N G φ hφ = 𝟙 _ :=
  NatTrans.ext <| funext fun X ↦ _root_.GrpCat.ext fun (g : ULift.{u₁} (G.obj X)) ↦
    congrArg ULift.up (SemidirectProduct.rightHom_inr (φ := φ X) g.down)

section Inl

/-! ### The inclusion of the normal factor

The normal factor `N` is taken valued in `GrpCat.{max u₁ u₂}`, the universe of the semidirect
product, so that the inclusions `n ↦ (n, 1)` are natural transformations out of `N` itself. -/

variable (N : C ⥤ _root_.GrpCat.{max u₁ u₂}) (G : C ⥤ _root_.GrpCat.{u₂})
  (φ : ∀ X, G.obj X →* MulAut (N.obj X))
  (hφ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (g : G.obj X) (n : N.obj X),
    N.map f (φ X g n) = φ Y (G.map f g) (N.map f n))

/-- The inclusions `n ↦ (n, 1)` of the normal factor `N(X)` into `N(X) ⋊ G(X)`, natural in `X`. -/
def semidirectProductInl : N ⟶ semidirectProductFunctor N G φ hφ where
  app _ := _root_.GrpCat.ofHom SemidirectProduct.inl
  naturality _ _ f :=
    _root_.GrpCat.ext fun n ↦ (SemidirectProduct.map_inl (N.map f).hom (G.map f).hom
      (fun g ↦ MonoidHom.ext fun n ↦ hφ f g n) n).symm

/-- The inclusion of the normal factor sends `n` to `(n, 1)`. -/
lemma semidirectProductInl_app_apply (X : C) (n : N.obj X) :
    (semidirectProductInl N G φ hφ).app X n = SemidirectProduct.inl n :=
  (rfl)

variable {N G φ hφ} {N' : C ⥤ _root_.GrpCat.{max u₁ u₂}} {G' : C ⥤ _root_.GrpCat.{u₂}}
  {φ' : ∀ X, G'.obj X →* MulAut (N'.obj X)}
  {hφ' : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (g : G'.obj X) (n : N'.obj X),
    N'.map f (φ' X g n) = φ' Y (G'.map f g) (N'.map f n)}

/-- The induced map of semidirect products restricts to `α` on the normal factors. -/
@[reassoc]
theorem semidirectProductInl_comp_map (α : N ⟶ N') (β : G ⟶ G')
    (h : ∀ X (g : G.obj X) (n : N.obj X), α.app X (φ X g n) = φ' X (β.app X g) (α.app X n)) :
    semidirectProductInl N G φ hφ ≫ semidirectProductMap α β h =
      α ≫ semidirectProductInl N' G' φ' hφ' :=
  NatTrans.ext <| funext fun X ↦ _root_.GrpCat.ext fun n ↦
    SemidirectProduct.map_inl (α.app X).hom (β.app X).hom
      (fun g ↦ MonoidHom.ext fun n ↦ h X g n) n

end Inl

end TauCeti.GrpCat
