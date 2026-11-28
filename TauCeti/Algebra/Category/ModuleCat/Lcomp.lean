/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Module.Injective
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.CategoryTheory.Abelian.Injective.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-!
# The contravariant linear-map functor on `ModuleCat`

Given rings `A` and `B` and commuting left `A`- and left `B`-module structures on `E` (that is,
`[Module A E] [Module B E]` and `[SMulCommClass A B E]`), taking `A`-linear maps into `E` defines
a contravariant additive functor

* `ModuleCat.lcompFunctor A B E : (ModuleCat A)ᵒᵖ ⥤ ModuleCat B` (`M ↦ M →ₗ[A] E`),

constructed by composing `ModuleCat.uliftFunctor`, `preadditiveYonedaObj`, and
`ModuleCat.restrictScalars` along the action map from `B` to `End (ULift E)`. As a result it
preserves finite limits, and when `[Small.{v} A]` and `[Module.Injective A E]`, it preserves finite
colimits and homology (`CategoryTheory.Functor.PreservesHomology`).

The object and morphism abbreviations `ModuleCat.lcompObj` and `ModuleCat.lcompMap` come with
the `B`-linear identification `ModuleCat.lcompObjEquiv : lcompObj A B E M ≃ₗ[B] (M →ₗ[A] E)` and
the pointwise precomposition rule `ModuleCat.lcompObjEquiv_map_apply`.

When `E` is also equipped with `[SMulCommClass B A E]` and `M` is identified with its double dual
`Hom_B(Hom_A(M, E), E)` via an arbitrary linear equivalence,
`ModuleCat.lcompBidualIsoOfLinearEquiv` packages that equivalence as a categorical isomorphism
`M ≅ lcompObj B A E (lcompObj A B E M)`, together with evaluation, naturality, and the triangle
identity when the equivalence is evaluation.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

universe u u' v w

section Lcomp

variable (A : Type u) [Ring A] (B : Type u') [Ring B] (E : Type v)
  [AddCommGroup E] [Module A E] [Module B E] [SMulCommClass A B E]

/-- Left multiplication by `B` on `ULift E` as a ring homomorphism into the endomorphism ring of
`(ModuleCat.uliftFunctor.{w, v} A).obj (ModuleCat.of A E)`. -/
private def lcompActionHom :
    B →+* End ((ModuleCat.uliftFunctor.{w, v} A).obj (ModuleCat.of A E)) where
  toFun b := End.of <| ModuleCat.ofHom
    { toFun x := ⟨b • x.down⟩
      map_add' _ _ := by ext; simp [smul_add]
      map_smul' a _ := by ext; simp [smul_comm a b] }
  map_one' := by apply End.ext; apply ModuleCat.hom_ext; apply LinearMap.ext; intro ⟨x⟩; simp; rfl
  map_mul' b₁ b₂ := by
    apply End.ext; apply ModuleCat.hom_ext; apply LinearMap.ext; intro ⟨x⟩
    simp [End.mul_asHom, mul_smul]; rfl
  map_zero' := by apply End.ext; apply ModuleCat.hom_ext; apply LinearMap.ext; intro ⟨x⟩; simp; rfl
  map_add' b₁ b₂ := by
    apply End.ext; apply ModuleCat.hom_ext; apply LinearMap.ext; intro ⟨x⟩
    simp [End.add_asHom, add_smul]; rfl

/-- The contravariant Hom functor `Hom_A(-, E) : (ModuleCat A)ᵒᵖ ⥤ ModuleCat B` for commuting
left `A`- and left `B`-module structures on `E`, built from `ModuleCat.uliftFunctor`,
`preadditiveYonedaObj`, and `ModuleCat.restrictScalars`. -/
def lcompFunctor : (ModuleCat.{w} A)ᵒᵖ ⥤ ModuleCat.{max v w} B :=
  (ModuleCat.uliftFunctor.{v, w} A).op ⋙
    preadditiveYonedaObj ((ModuleCat.uliftFunctor.{w, v} A).obj (ModuleCat.of A E)) ⋙
    ModuleCat.restrictScalars (lcompActionHom A B E)

/-- The bundled `B`-module `M →ₗ[A] E` of `A`-linear maps from a bundled `A`-module `M` into a
module `E` with commuting left `A`- and left `B`-module structures, realized as
`(lcompFunctor A B E).obj (op M)`. -/
abbrev lcompObj (M : ModuleCat.{w} A) : ModuleCat.{max v w} B :=
  (lcompFunctor A B E).obj (op M)

/-- Precomposition along an `A`-linear morphism `M ⟶ M'` induces a `B`-linear morphism
`Hom_A(M', E) ⟶ Hom_A(M, E)`. -/
abbrev lcompMap {M M' : ModuleCat.{w} A} (g : M ⟶ M') :
    lcompObj A B E M' ⟶ lcompObj A B E M :=
  (lcompFunctor A B E).map g.op

/-- The underlying `B`-module of `lcompObj A B E M` is `M →ₗ[A] E`. -/
def lcompObjEquiv (M : ModuleCat.{w} A) : lcompObj A B E M ≃ₗ[B] (M →ₗ[A] E) where
  toFun φ := ULift.moduleEquiv.toLinearMap ∘ₗ φ.hom ∘ₗ ULift.moduleEquiv.symm.toLinearMap
  invFun f := ModuleCat.ofHom
    (ULift.moduleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ULift.moduleEquiv.toLinearMap)
  left_inv φ := by apply ModuleCat.hom_ext; ext ⟨x⟩; rfl
  right_inv f := by ext x; rfl
  map_add' φ ψ := by ext x; rfl
  map_smul' b φ := by
    ext x
    change b • (φ.hom ⟨x⟩).down = b • (φ.hom ⟨x⟩).down
    rfl

@[simp]
theorem lcompObjEquiv_map_apply {M M' : ModuleCat.{w} A} (g : M ⟶ M')
    (φ : lcompObj A B E M') (x : M) :
    lcompObjEquiv A B E M (lcompMap A B E g φ) x =
      lcompObjEquiv A B E M' φ (g x) := by
  rfl

@[simp]
theorem lcompObjEquiv_functor_map_apply {M N : (ModuleCat.{w} A)ᵒᵖ} (g : M ⟶ N)
    (φ : (lcompFunctor A B E).obj M) (x : N.unop) :
    lcompObjEquiv A B E N.unop ((lcompFunctor A B E).map g φ) x =
      lcompObjEquiv A B E M.unop φ (g.unop x) := by
  rfl

instance : (lcompFunctor.{u, u', v, w} A B E).Additive := by
  dsimp only [lcompFunctor]
  infer_instance

instance : PreservesFiniteLimits (lcompFunctor.{u, u', v, w} A B E) := by
  dsimp only [lcompFunctor]
  have : PreservesFiniteLimits (ModuleCat.uliftFunctor.{v, w} A).op :=
    preservesFiniteLimits_op _
  infer_instance

instance [Small.{v} A] [Module.Injective A E] :
    PreservesFiniteColimits (lcompFunctor.{u, u', v, w} A B E) := by
  dsimp only [lcompFunctor]
  have : PreservesFiniteColimits (ModuleCat.uliftFunctor.{v, w} A).op :=
    preservesFiniteColimits_op _
  have : CategoryTheory.Injective (ModuleCat.of A E) :=
    (Module.injective_iff_injective_object A _).mp inferInstance
  have : CategoryTheory.Injective ((ModuleCat.uliftFunctor.{w, v} A).obj (ModuleCat.of A E)) :=
    Functor.injective_obj _ _
  infer_instance

instance [Small.{v} A] [Module.Injective A E] :
    (lcompFunctor.{u, u', v, w} A B E).PreservesHomology :=
  inferInstance

end Lcomp

section Bidual

variable (A : Type u) [Ring A] (B : Type u') [Ring B] (E : Type v)
  [AddCommGroup E] [Module A E] [Module B E] [SMulCommClass A B E] [SMulCommClass B A E]

/-- Package a bidual linear equivalence `M ≃ₗ[A] ((M →ₗ[A] E) →ₗ[B] E)` as a categorical
isomorphism `M ≅ lcompObj B A E (lcompObj A B E M)`. -/
def lcompBidualIsoOfLinearEquiv (M : ModuleCat.{max v w} A)
    (e : M ≃ₗ[A] ((M →ₗ[A] E) →ₗ[B] E)) :
    M ≅ lcompObj B A E (lcompObj A B E M) :=
  let eArrow := LinearEquiv.congrLeft E A (lcompObjEquiv A B E M).symm
  (e.trans (eArrow.trans (lcompObjEquiv B A E _).symm)).toModuleIso

theorem lcompBidualIsoOfLinearEquiv_hom_apply (M : ModuleCat.{max v w} A)
    (e : M ≃ₗ[A] ((M →ₗ[A] E) →ₗ[B] E))
    (he : ∀ (m : M) (f : M →ₗ[A] E), e m f = f m)
    (m : M) (f : lcompObj A B E M) :
    lcompObjEquiv B A E _ ((lcompBidualIsoOfLinearEquiv A B E M e).hom m) f =
      lcompObjEquiv A B E M f m := by
  simp [lcompBidualIsoOfLinearEquiv, LinearEquiv.congrLeft_apply, he]

/-- Naturality of `lcompBidualIsoOfLinearEquiv` with respect to `A`-linear morphisms when `e` and
`e'` are evaluation. -/
theorem lcompBidualIsoOfLinearEquiv_hom_naturality {M M' : ModuleCat.{max v w} A} (g : M ⟶ M')
    (e : M ≃ₗ[A] ((M →ₗ[A] E) →ₗ[B] E))
    (he : ∀ (m : M) (f : M →ₗ[A] E), e m f = f m)
    (e' : M' ≃ₗ[A] ((M' →ₗ[A] E) →ₗ[B] E))
    (he' : ∀ (m' : M') (f' : M' →ₗ[A] E), e' m' f' = f' m') :
    g ≫ (lcompBidualIsoOfLinearEquiv A B E M' e').hom =
      (lcompBidualIsoOfLinearEquiv A B E M e).hom ≫ lcompMap B A E (lcompMap A B E g) := by
  ext x
  apply (lcompObjEquiv B A E _).injective
  ext φ
  simp [lcompBidualIsoOfLinearEquiv_hom_apply, he, he']

/-- Triangle identity for `lcompBidualIsoOfLinearEquiv`: evaluation on `Hom_A(M, E)` is
precomposition with the inverse of evaluation on `M`. -/
theorem lcompBidualIsoOfLinearEquiv_lcompObj_hom (M : ModuleCat.{max v w} A)
    (e : M ≃ₗ[A] ((M →ₗ[A] E) →ₗ[B] E))
    (he : ∀ (m : M) (f : M →ₗ[A] E), e m f = f m)
    (e' : lcompObj A B E M ≃ₗ[B] ((lcompObj A B E M →ₗ[B] E) →ₗ[A] E))
    (he' : ∀ (φ : lcompObj A B E M) (Ψ : lcompObj A B E M →ₗ[B] E), e' φ Ψ = Ψ φ) :
    (lcompBidualIsoOfLinearEquiv B A E (lcompObj A B E M) e').hom =
      lcompMap A B E (lcompBidualIsoOfLinearEquiv A B E M e).inv := by
  ext φ
  apply (lcompObjEquiv A B E _).injective
  ext Ψ
  obtain ⟨x, rfl⟩ : ∃ x, (lcompBidualIsoOfLinearEquiv A B E M e).hom x = Ψ :=
    ⟨(lcompBidualIsoOfLinearEquiv A B E M e).inv Ψ,
      (lcompBidualIsoOfLinearEquiv A B E M e).inv_hom_id_apply Ψ⟩
  simp [lcompBidualIsoOfLinearEquiv_hom_apply, he, he']

end Bidual

end ModuleCat
