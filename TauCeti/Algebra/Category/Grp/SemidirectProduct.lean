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
transformation of the semidirect products. As `N(X) ⋊ G(X)` lives in the larger of the two
universes, the maps between it and one factor are stated for that factor valued in a universe
containing that of the other, so that the factor needs no lift. The inclusions `n ↦ (n, 1)` of the
normal factor are natural and commute with the induced maps of semidirect products. The
projections `N(X) ⋊ G(X) → G(X)` and their sections `g ↦ (1, g)` are natural. For `N` and `G`
valued in a common universe, natural transformations out of `N ⋊ G` are induced by compatible
natural transformations out of the two factors, and are determined by their restrictions to them.

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
* `TauCeti.GrpCat.semidirectProductLift α β h`: the natural transformation out of `N ⋊ G` induced
  by compatible natural transformations out of `N` and `G`, characterized by
  `TauCeti.GrpCat.semidirectProductInl_comp_lift`, `TauCeti.GrpCat.semidirectProductInr_comp_lift`
  and `TauCeti.GrpCat.semidirectProductFunctor_hom_ext`.
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

section Inr

/-! ### The acting factor

The acting factor `G` is taken valued in `GrpCat.{max u₁ u₂}`, the universe of the semidirect
product, so that the projections to `G` and their sections `g ↦ (1, g)` are natural
transformations into and out of `G` itself. -/

variable (N : C ⥤ _root_.GrpCat.{u₁}) (G : C ⥤ _root_.GrpCat.{max u₁ u₂})
  (φ : ∀ X, G.obj X →* MulAut (N.obj X))
  (hφ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (g : G.obj X) (n : N.obj X),
    N.map f (φ X g n) = φ Y (G.map f g) (N.map f n))

/-- The projections `N(X) ⋊ G(X) → G(X)`, natural in `X`. -/
def semidirectProductRightHom : semidirectProductFunctor N G φ hφ ⟶ G where
  app _ := _root_.GrpCat.ofHom SemidirectProduct.rightHom
  naturality _ _ f := _root_.GrpCat.ext <| DFunLike.congr_fun
    (SemidirectProduct.rightHom_comp_map (N.map f).hom (G.map f).hom
      fun g ↦ MonoidHom.ext fun n ↦ hφ f g n)

/-- The projection to `G` sends `(n, g)` to `g`. -/
lemma semidirectProductRightHom_app_apply (X : C) (x : N.obj X ⋊[φ X] G.obj X) :
    (semidirectProductRightHom N G φ hφ).app X x = x.right :=
  (rfl)

/-- The sections `g ↦ (1, g)` of the projections `N(X) ⋊ G(X) → G(X)`, natural in `X`. -/
def semidirectProductInr : G ⟶ semidirectProductFunctor N G φ hφ where
  app _ := _root_.GrpCat.ofHom SemidirectProduct.inr
  naturality _ _ f :=
    _root_.GrpCat.ext fun g ↦ (SemidirectProduct.map_inr (N.map f).hom (G.map f).hom
      (fun g ↦ MonoidHom.ext fun n ↦ hφ f g n) g).symm

/-- The section of the projection to `G` sends `g` to `(1, g)`. -/
lemma semidirectProductInr_app_apply (X : C) (g : G.obj X) :
    (semidirectProductInr N G φ hφ).app X g = SemidirectProduct.inr g :=
  (rfl)

/-- The natural sections `g ↦ (1, g)` are sections of the natural projections to `G`. -/
@[reassoc (attr := simp)]
theorem semidirectProductInr_comp_rightHom :
    semidirectProductInr N G φ hφ ≫ semidirectProductRightHom N G φ hφ = 𝟙 G :=
  NatTrans.ext <| funext fun X ↦ _root_.GrpCat.ext fun g ↦
    SemidirectProduct.rightHom_inr (φ := φ X) g

end Inr

section Lift

/-! ### The universal property

For `N` and `G` valued in a common universe, a natural transformation out of `N ⋊ G` is given by
natural transformations out of the two factors, compatible with the actions. -/

variable {N G : C ⥤ _root_.GrpCat.{u₁}} {φ : ∀ X, G.obj X →* MulAut (N.obj X)}
  {hφ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (g : G.obj X) (n : N.obj X),
    N.map f (φ X g n) = φ Y (G.map f g) (N.map f n)}
  {K : C ⥤ _root_.GrpCat.{u₁}}

/-- The natural transformation `N ⋊ G ⟶ K` induced by natural transformations `α : N ⟶ K` and
`β : G ⟶ K` for which the action of `g` is carried by `α` to conjugation by `β g`. It sends
`(n, g)` to `α n * β g`. -/
def semidirectProductLift (α : N ⟶ K) (β : G ⟶ K)
    (h : ∀ X (g : G.obj X) (n : N.obj X),
      α.app X (φ X g n) = β.app X g * α.app X n * (β.app X g)⁻¹) :
    semidirectProductFunctor N G φ hφ ⟶ K where
  app X := _root_.GrpCat.ofHom <| SemidirectProduct.lift (α.app X).hom (β.app X).hom
    fun g ↦ MonoidHom.ext fun n ↦ h X g n
  naturality _ _ f := _root_.GrpCat.ext fun x ↦
    (congr($(α.naturality f) x.left * $(β.naturality f) x.right) :).trans
      (map_mul (K.map f).hom _ _).symm

/-- The induced map out of the semidirect product sends `(n, g)` to `α n * β g`. -/
lemma semidirectProductLift_app_apply (α : N ⟶ K) (β : G ⟶ K)
    (h : ∀ X (g : G.obj X) (n : N.obj X),
      α.app X (φ X g n) = β.app X g * α.app X n * (β.app X g)⁻¹)
    (X : C) (x : N.obj X ⋊[φ X] G.obj X) :
    (semidirectProductLift (hφ := hφ) α β h).app X x = α.app X x.left * β.app X x.right :=
  (rfl)

/-- The induced map out of the semidirect product restricts to `α` on the normal factor. -/
@[reassoc (attr := simp)]
theorem semidirectProductInl_comp_lift (α : N ⟶ K) (β : G ⟶ K)
    (h : ∀ X (g : G.obj X) (n : N.obj X),
      α.app X (φ X g n) = β.app X g * α.app X n * (β.app X g)⁻¹) :
    semidirectProductInl N G φ hφ ≫ semidirectProductLift α β h = α :=
  NatTrans.ext <| funext fun X ↦ _root_.GrpCat.ext fun n ↦
    SemidirectProduct.lift_inl (α.app X).hom (β.app X).hom
      (fun g ↦ MonoidHom.ext fun n ↦ h X g n) n

/-- The induced map out of the semidirect product restricts to `β` on the acting factor. -/
@[reassoc (attr := simp)]
theorem semidirectProductInr_comp_lift (α : N ⟶ K) (β : G ⟶ K)
    (h : ∀ X (g : G.obj X) (n : N.obj X),
      α.app X (φ X g n) = β.app X g * α.app X n * (β.app X g)⁻¹) :
    semidirectProductInr N G φ hφ ≫ semidirectProductLift α β h = β :=
  NatTrans.ext <| funext fun X ↦ _root_.GrpCat.ext fun g ↦
    SemidirectProduct.lift_inr (α.app X).hom (β.app X).hom
      (fun g ↦ MonoidHom.ext fun n ↦ h X g n) g

/-- Natural transformations out of the semidirect product agree when they agree on the two
factors. -/
theorem semidirectProductFunctor_hom_ext {τ τ' : semidirectProductFunctor N G φ hφ ⟶ K}
    (hl : semidirectProductInl N G φ hφ ≫ τ = semidirectProductInl N G φ hφ ≫ τ')
    (hr : semidirectProductInr N G φ hφ ≫ τ = semidirectProductInr N G φ hφ ≫ τ') :
    τ = τ' :=
  NatTrans.ext <| funext fun X ↦ _root_.GrpCat.hom_ext <| SemidirectProduct.hom_ext
    (congrArg (fun σ ↦ (σ.app X).hom) hl) (congrArg (fun σ ↦ (σ.app X).hom) hr)

end Lift

end TauCeti.GrpCat
