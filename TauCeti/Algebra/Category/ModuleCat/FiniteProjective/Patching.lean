/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
public import TauCeti.RingTheory.Patching.PatchedModule

/-!
# Patching triples and the patching functor of a fibre product of rings

Let `π₁ : A₁ →+* Q` and `π₂ : A₂ →+* Q` be ring homomorphisms between possibly noncommutative
rings, and let `D = A₁ ×_Q A₂` be their fibre product, Mathlib's `RingHom.pullback π₁ π₂`, with
projections `p₁` and `p₂`. A **patching triple** `(P₁, P₂, α)` consists of finitely generated
projective right modules `P₁` over `A₁` and `P₂` over `A₂` and an isomorphism
`α : P₁ ⊗ Q ≅ P₂ ⊗ Q` of right `Q`-modules; a morphism of patching triples is a pair of module
maps compatible with the isomorphisms. The category of patching triples is the categorical
pullback of the two extension-of-scalars functors on finitely generated projective right modules.

Every finitely generated projective right `D`-module `P` gives the patching triple
`(P ⊗_D A₁, P ⊗_D A₂, α_P)`, whose isomorphism `α_P` is the canonical one through `P ⊗_D Q`
(`RingHom.finiteProjectiveModulesExtendScalarsCompIso` for the square `π₁ ∘ p₁ = π₂ ∘ p₂`). It
sends `(p ⊗ a) ⊗ q` to `(p ⊗ 1) ⊗ (π₁ a * q)`, in particular `(p ⊗ 1) ⊗ 1` to `(p ⊗ 1) ⊗ 1`
(`RingHom.finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom_tmul`); on underlying modules
it is the gluing isomorphism `TauCeti.BalancedExtension.commSqEquiv`. This is the **patching
functor**. Milnor's patching theorem says that it is an equivalence of categories as soon
as `π₁` or `π₂` is surjective; the inverse sends `(P₁, P₂, α)` to the fibre product module
`{(x, y) ∈ P₁ × P₂ | α (x ⊗ 1) = y ⊗ 1}`.

This file proves the first half of the theorem: the patching functor is fully faithful, for all
`π₁` and `π₂`. On underlying modules this is
`TauCeti.BalancedExtension.existsUnique_map_eq_and_map_eq` over the square of opposite rings: a
compatible pair of maps `P ⊗_D Aⱼ → P' ⊗_D Aⱼ` comes from exactly one map `P → P'`, because a
finitely generated projective module over `D` is the patched module of its triple. Essential
surjectivity, which needs a surjective leg, is not proved here: for the inclusions `ℤ → ℚ ← ℤ`
the fibre product is `ℤ`, and the triple `(ℤ, ℤ, 2)` is not isomorphic to the image `(ℤ, ℤ, 1)` of
any module.

## Main definitions

* `RingHom.PatchingTriples π₁ π₂`: the category of patching triples.
* `RingHom.patchingFunctor π₁ π₂`: the functor `P ↦ (P ⊗_D A₁, P ⊗_D A₂, α_P)` from finitely
  generated projective right `D`-modules to patching triples.

## Main results

* `RingHom.faithful_patchingFunctor`, `RingHom.full_patchingFunctor`: the patching functor is
  faithful and full.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §2
  (projective modules over a fibre product of rings).
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter I, Milnor Patching
  Theorem 2.7, p. 12.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti BalancedExtension

namespace RingHom

universe u

variable {A₁ A₂ Q : Type u} [Ring A₁] [Ring A₂] [Ring Q] (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)

/-- The category of **patching triples** of ring homomorphisms `π₁ : A₁ →+* Q` and
`π₂ : A₂ →+* Q`: the categorical pullback of the extension-of-scalars functors along `π₁` and `π₂`
on finitely generated projective right modules. An object is a triple `(P₁, P₂, α)` with `Pⱼ` a
finitely generated projective right `Aⱼ`-module and `α : P₁ ⊗ Q ≅ P₂ ⊗ Q` an isomorphism of right
`Q`-modules; a morphism is a pair of module maps compatible with the isomorphisms. -/
abbrev PatchingTriples : Type (u + 1) :=
  CategoricalPullback (RingHom.op π₁).finiteProjectiveModulesExtendScalars
    (RingHom.op π₂).finiteProjectiveModulesExtendScalars

/-- The **patching functor** of the fibre product `D = A₁ ×_Q A₂` of `π₁ : A₁ →+* Q` and
`π₂ : A₂ →+* Q`: it sends a finitely generated projective right `D`-module `P` to the patching
triple `(P ⊗_D A₁, P ⊗_D A₂, α_P)`, where `α_P : (P ⊗_D A₁) ⊗ Q ≅ (P ⊗_D A₂) ⊗ Q` is the
canonical isomorphism through `P ⊗_D Q`, and a map to the pair of its extensions. -/
-- Exposed so that the components of the image of a module or map are definitionally its
-- extensions, as recorded by the `simps` lemmas.
@[expose, simps! obj_fst obj_snd obj_iso map_fst map_snd]
def patchingFunctor : FiniteProjectiveRight (π₁.pullback π₂) ⥤ π₁.PatchingTriples π₂ :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
    { fst := (RingHom.op (π₁.pullbackFst π₂)).finiteProjectiveModulesExtendScalars
      snd := (RingHom.op (π₁.pullbackSnd π₂)).finiteProjectiveModulesExtendScalars
      iso := finiteProjectiveModulesExtendScalarsCompIso _ _ _ _ (op_pullback_comm_sq π₁ π₂) }

/-- The gluing isomorphism `α_P` of the patching triple of `P` is
`TauCeti.BalancedExtension.commSqEquiv` over the square of opposite rings. -/
private theorem commSqEquiv_eq_compIso_hom_app (P : FiniteProjectiveRight (π₁.pullback π₂))
    (x : BalancedExtension (RingHom.op π₁)
      (BalancedExtension (RingHom.op (π₁.pullbackFst π₂)) P.obj)) :
    commSqEquiv (op_pullback_comm_sq π₁ π₂) P.obj x =
      ((finiteProjectiveModulesExtendScalarsCompIso _ _ _ _
        (op_pullback_comm_sq π₁ π₂)).hom.app P).hom x := by
  rw [finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom_apply, LinearEquiv.eq_symm_apply,
    cancelBaseChange_commSqEquiv]

/-- The extensions to `Q` of the two components of a morphism of patching triples between images
of the patching functor are intertwined by the gluing isomorphisms `commSqEquiv`. -/
private theorem commSqEquiv_map_hom_fst {P P' : FiniteProjectiveRight (π₁.pullback π₂)}
    (φ : (patchingFunctor π₁ π₂).obj P ⟶ (patchingFunctor π₁ π₂).obj P')
    (x : BalancedExtension (RingHom.op π₁)
      (BalancedExtension (RingHom.op (π₁.pullbackFst π₂)) P.obj)) :
    commSqEquiv (op_pullback_comm_sq π₁ π₂) P'.obj (map (RingHom.op π₁) φ.fst.hom.hom x) =
      map (RingHom.op π₂) φ.snd.hom.hom (commSqEquiv (op_pullback_comm_sq π₁ π₂) P.obj x) :=
  -- The components of `φ.w` are these maps up to the definitional identification of the extended
  -- modules with balanced extensions.
  (commSqEquiv_eq_compIso_hom_app π₁ π₂ P' _).trans
    ((congr($(φ.w).hom x)).trans (congrArg _ (commSqEquiv_eq_compIso_hom_app π₁ π₂ P x).symm))

/-- **The patching functor is faithful**: a map of finitely generated projective right modules over
`A₁ ×_Q A₂` is determined by its extensions to `A₁` and `A₂`. -/
instance faithful_patchingFunctor : (patchingFunctor π₁ π₂).Faithful where
  map_injective {_ _} φ _ hφψ :=
    ObjectProperty.hom_ext _ <| ModuleCat.hom_ext <|
      (existsUnique_map_eq_and_map_eq (op_pullback_comm_sq π₁ π₂)
        (fun _ _ ↦ existsUnique_op_pullbackFst_eq_and_op_pullbackSnd_eq π₁ π₂) _ _
        (commSqEquiv_map _ φ.hom.hom)).unique ⟨rfl, rfl⟩
        ⟨congr($(congrArg CategoricalPullback.Hom.fst hφψ).hom.hom).symm,
          congr($(congrArg CategoricalPullback.Hom.snd hφψ).hom.hom).symm⟩

/-- **The patching functor is full**: a morphism of patching triples between the images of
finitely generated projective right modules `P` and `P'` over `A₁ ×_Q A₂` is the image of a map
`P → P'`. -/
instance full_patchingFunctor : (patchingFunctor π₁ π₂).Full where
  map_surjective {P P'} φ := by
    obtain ⟨g, hg, -⟩ := existsUnique_map_eq_and_map_eq (op_pullback_comm_sq π₁ π₂)
      (fun _ _ ↦ existsUnique_op_pullbackFst_eq_and_op_pullbackSnd_eq π₁ π₂) _ _
      (commSqEquiv_map_hom_fst π₁ π₂ φ)
    exact ⟨ObjectProperty.homMk (ModuleCat.ofHom g), CategoricalPullback.hom_ext
      (ObjectProperty.hom_ext _ (ModuleCat.hom_ext hg.1))
      (ObjectProperty.hom_ext _ (ModuleCat.hom_ext hg.2))⟩

end RingHom
