/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.CategoryTheory.Linear.FullyFaithful

/-!
# Restriction of actions

Restriction along a composite monoid homomorphism is successive restriction, as an equality
of functors, and restriction along the identity is the identity functor. These equality forms
complement Mathlib's natural isomorphisms `Action.resComp` and `Action.resId`.

For homomorphisms related by conjugation by `g`, `Action.ρAut A g` intertwines the
restricted actions, giving the compatibility condition used by `Action.mkIso`.

For actions in a linear category, restriction along a surjective monoid homomorphism preserves
the finrank of morphism spaces. This uses Mathlib's fullness result `Action.full_res` and
`Functor.homLinearEquiv`, and in particular applies to intertwining spaces of finite-dimensional
representations over a commutative ring.

## Main results

* `MonoidHom.actionRes_comp`: restriction along a composite is successive restriction.
* `MonoidHom.actionRes_id`: restriction along the identity is the identity functor.
* `Action.res_ρ_comm_ρAut_hom`: conjugation by `g` intertwines restrictions along
  `σ ∘ φ` and `σ'`, with the compatibility required by `Action.mkIso`.
* `MonoidHom.finrank_hom_actionRes_of_surjective`: restriction along a surjective monoid
  homomorphism preserves the finrank of morphism spaces in a linear category.
-/

public section

open CategoryTheory

variable {V : Type*} [Category V] {H K L : Type*} [Monoid H] [Monoid K] [Monoid L]

/-- Restriction of actions along a composite is successive restriction. This is the equality
form of Mathlib's natural isomorphism `Action.resComp`. -/
theorem MonoidHom.actionRes_comp (φ : K →* L) (ψ : H →* K) :
    Action.res V (φ.comp ψ) = Action.res V φ ⋙ Action.res V ψ :=
  rfl

/-- Restriction of actions along the identity is the identity functor. This is the equality
form of Mathlib's natural isomorphism `Action.resId`. -/
@[simp]
theorem MonoidHom.actionRes_id :
    Action.res V (MonoidHom.id H) = 𝟭 (Action V H) :=
  rfl

/-- If `g * σ (φ y) = σ' y * g` for every `y`, then `(Action.ρAut A g).asIso.hom`
intertwines the restrictions of `A` along `σ ∘ φ` and `σ'`. This is the compatibility
condition for `Action.mkIso`, with the first restriction written as successive restrictions. -/
theorem Action.res_ρ_comm_ρAut_hom {L M N : Type*} [Group L] [Monoid M] [Monoid N]
    (A : Action V L) (g : L) (φ : M →* N) (σ : N →* L) (σ' : M →* L)
    (hg : ∀ y : M, g * σ (φ y) = σ' y * g) (y : M) :
    (((Action.res V φ).obj ((Action.res V σ).obj A)).ρ y).asHom ≫
        (Action.ρAut A g).asIso.hom =
      (Action.ρAut A g).asIso.hom ≫ (((Action.res V σ').obj A).ρ y).asHom := by
  -- Restriction keeps the underlying object and composes its action with the homomorphism.
  -- Rewriting res_obj_ρ in this dependent composition changes the endomorphism type;
  -- read both actions in the common underlying object instead.
  change (A.ρ (σ (φ y))).asHom ≫ (A.ρ g).asHom =
    (A.ρ g).asHom ≫ (A.ρ (σ' y)).asHom
  simp only [← End.mul_asHom, ← map_mul, hg]

/-- Restriction along a surjective monoid homomorphism preserves the finrank of morphism spaces
in a linear category. In particular it preserves the dimension of intertwining spaces of
representations. -/
theorem MonoidHom.finrank_hom_actionRes_of_surjective {k : Type*} [Semiring k]
    [Preadditive V] [Linear k V] (f : H →* K) (hf : Function.Surjective f) (X Y : Action V K) :
    Module.finrank k ((Action.res V f).obj X ⟶ (Action.res V f).obj Y) =
      Module.finrank k (X ⟶ Y) := by
  let : (Action.res V f).Full := Action.full_res V f hf
  exact ((Action.res V f).homLinearEquiv k X Y).finrank_eq.symm
