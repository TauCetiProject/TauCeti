/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The contravariant linear-map functor on `ModuleCat`

Given rings `A` and `B` and an `(A, B)`-bimodule `E` (that is, `[Module A E] [Module B E]` and
`[SMulCommClass A B E]`), taking `A`-linear maps into `E` defines a contravariant additive functor

* `ModuleCat.lcompFunctor A B E : (ModuleCat A)ᵒᵖ ⥤ ModuleCat B` (`M ↦ M →ₗ[A] E`).

When `E` is also equipped with `[SMulCommClass B A E]` and `M` is identified with its double dual
`Hom_B(Hom_A(M, E), E)` via evaluation, `ModuleCat.lcompEvalIso` packages that equivalence as a
categorical isomorphism `M ≅ lcompObj B A E (lcompObj A B E M)`, together with naturality and
the triangle identity.
-/

public section

noncomputable section

open CategoryTheory Opposite

namespace ModuleCat

universe u u' v w

section Lcomp

variable (A : Type u) [Ring A] (B : Type u') [Ring B] (E : Type v)
  [AddCommGroup E] [Module A E] [Module B E] [SMulCommClass A B E]

/-- The bundled `B`-module `M →ₗ[A] E` of `A`-linear maps from a bundled `A`-module `M` into an
`(A, B)`-bimodule `E`. -/
def lcompObj (M : ModuleCat.{w} A) : ModuleCat.{max v w} B :=
  ModuleCat.of B (M →ₗ[A] E)

/-- The underlying `B`-module of `lcompObj A B E M` is `M →ₗ[A] E`. -/
def lcompObjEquiv (M : ModuleCat.{w} A) : lcompObj A B E M ≃ₗ[B] (M →ₗ[A] E) :=
  LinearEquiv.refl _ _

/-- Precomposition along an `A`-linear morphism `M ⟶ M'` induces a `B`-linear morphism
`Hom_A(M', E) ⟶ Hom_A(M, E)`. -/
def lcompMap {M M' : ModuleCat.{w} A} (g : M ⟶ M') :
    lcompObj A B E M' ⟶ lcompObj A B E M :=
  ModuleCat.ofHom ((lcompObjEquiv A B E M).symm.toLinearMap ∘ₗ
    g.hom.lcomp B E ∘ₗ (lcompObjEquiv A B E M').toLinearMap)

@[simp]
theorem lcompObjEquiv_map_apply {M M' : ModuleCat.{w} A} (g : M ⟶ M')
    (φ : lcompObj A B E M') (x : M) :
    lcompObjEquiv A B E M (lcompMap A B E g φ) x = lcompObjEquiv A B E M' φ (g x) :=
  (rfl)

/-- The contravariant Hom functor `Hom_A(-, E) : (ModuleCat A)ᵒᵖ ⥤ ModuleCat B` for an
`(A, B)`-bimodule `E`. -/
@[expose]
def lcompFunctor : (ModuleCat.{w} A)ᵒᵖ ⥤ ModuleCat.{max v w} B where
  obj M := lcompObj A B E M.unop
  map g := lcompMap A B E g.unop
  map_id M := by
    ext φ
    apply (lcompObjEquiv A B E M.unop).injective
    ext x
    simp
  map_comp g h := by
    ext φ
    apply (lcompObjEquiv A B E _).injective
    ext x
    simp

@[simp]
theorem lcompFunctor_obj (M : (ModuleCat.{w} A)ᵒᵖ) :
    (lcompFunctor A B E).obj M = lcompObj A B E M.unop :=
  (rfl)

@[simp]
theorem lcompFunctor_map {M M' : (ModuleCat.{w} A)ᵒᵖ} (g : M ⟶ M') :
    (lcompFunctor A B E).map g = lcompMap A B E g.unop :=
  (rfl)

theorem lcompMap_add {M M' : ModuleCat.{w} A} (g h : M ⟶ M') :
    lcompMap A B E (g + h) = lcompMap A B E g + lcompMap A B E h := by
  ext φ
  apply (lcompObjEquiv A B E _).injective
  ext x
  simp [ModuleCat.hom_add]

instance : (lcompFunctor.{u, u', v, w} A B E).Additive where
  map_add := lcompMap_add A B E _ _

end Lcomp

section Eval

variable (A : Type u) [Ring A] (B : Type u') [Ring B] (E : Type v)
  [AddCommGroup E] [Module A E] [Module B E] [SMulCommClass A B E] [SMulCommClass B A E]

/-- Package an evaluation equivalence `M ≃ₗ[A] ((M →ₗ[A] E) →ₗ[B] E)` as a categorical isomorphism
`M ≅ lcompObj B A E (lcompObj A B E M)`. -/
def lcompEvalIso (M : ModuleCat.{max v w} A) (e : M ≃ₗ[A] ((M →ₗ[A] E) →ₗ[B] E)) :
    M ≅ lcompObj B A E (lcompObj A B E M) :=
  let eArrow := LinearEquiv.congrLeft E A (lcompObjEquiv A B E M).symm
  (e.trans (eArrow.trans (lcompObjEquiv B A E _).symm)).toModuleIso

theorem lcompEvalIso_hom_apply (M : ModuleCat.{max v w} A)
    (e : M ≃ₗ[A] ((M →ₗ[A] E) →ₗ[B] E))
    (he : ∀ (m : M) (f : M →ₗ[A] E), e m f = f m)
    (m : M) (f : lcompObj A B E M) :
    lcompObjEquiv B A E _ ((lcompEvalIso A B E M e).hom m) f =
      lcompObjEquiv A B E M f m := by
  simp [lcompEvalIso, LinearEquiv.congrLeft_apply, he]

/-- Naturality of `lcompEvalIso` with respect to `A`-linear morphisms. -/
theorem lcompEvalIso_hom_naturality {M M' : ModuleCat.{max v w} A} (g : M ⟶ M')
    (e : M ≃ₗ[A] ((M →ₗ[A] E) →ₗ[B] E))
    (he : ∀ (m : M) (f : M →ₗ[A] E), e m f = f m)
    (e' : M' ≃ₗ[A] ((M' →ₗ[A] E) →ₗ[B] E))
    (he' : ∀ (m' : M') (f' : M' →ₗ[A] E), e' m' f' = f' m') :
    g ≫ (lcompEvalIso A B E M' e').hom =
      (lcompEvalIso A B E M e).hom ≫ lcompMap B A E (lcompMap A B E g) := by
  ext x
  apply (lcompObjEquiv B A E _).injective
  ext φ
  simp [lcompEvalIso_hom_apply, he, he']

/-- Triangle identity for `lcompEvalIso`: evaluation on `Hom_A(M, E)` is precomposition with the
inverse of evaluation on `M`. -/
theorem lcompEvalIso_lcompObj_hom (M : ModuleCat.{max v w} A)
    (e : M ≃ₗ[A] ((M →ₗ[A] E) →ₗ[B] E))
    (he : ∀ (m : M) (f : M →ₗ[A] E), e m f = f m)
    (e' : lcompObj A B E M ≃ₗ[B] ((lcompObj A B E M →ₗ[B] E) →ₗ[A] E))
    (he' : ∀ (φ : lcompObj A B E M) (Ψ : lcompObj A B E M →ₗ[B] E), e' φ Ψ = Ψ φ) :
    (lcompEvalIso B A E (lcompObj A B E M) e').hom =
      lcompMap A B E (lcompEvalIso A B E M e).inv := by
  ext φ
  apply (lcompObjEquiv A B E _).injective
  ext Ψ
  obtain ⟨x, rfl⟩ : ∃ x, (lcompEvalIso A B E M e).hom x = Ψ :=
    ⟨(lcompEvalIso A B E M e).inv Ψ, (lcompEvalIso A B E M e).inv_hom_id_apply Ψ⟩
  simp [lcompEvalIso_hom_apply, he, he']

end Eval

end ModuleCat
