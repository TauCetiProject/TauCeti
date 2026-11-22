/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Composites of semilinear maps

Forgetting scalar compatibility commutes with composition of semilinear maps
(`LinearMap.toAddMonoidHom_comp`). Composites of injective or surjective semilinear maps are
injective or surjective (`LinearMap.injective_comp`, `LinearMap.surjective_comp`); these restate
`Function.Injective.comp` and `Function.Surjective.comp` for the coercion of `g.comp f`, so that
they can be passed where a proof about exactly this coercion is expected. Pasting a commutative
square onto a factorization gives a factorization (`LinearMap.comp_comp_eq_comp_comp_of_comp_eq`).
It also provides the identity and composition laws for integer linearization of additive
homomorphisms (`AddMonoidHom.toIntLinearMap_id` and `AddMonoidHom.toIntLinearMap_comp`).
-/

public section

namespace LinearMap

variable {R S T M N P : Type*} [Semiring R] [Semiring S] [Semiring T]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module S N] [Module T P]
  {σ : R →+* S} {τ : S →+* T} {υ : R →+* T} [RingHomCompTriple σ τ υ]

/-- The additive map underlying a composite is the composite of the underlying additive maps. -/
@[simp] theorem toAddMonoidHom_comp (g : N →ₛₗ[τ] P) (f : M →ₛₗ[σ] N) :
    (g.comp f : M →ₛₗ[υ] P).toAddMonoidHom =
      g.toAddMonoidHom.comp f.toAddMonoidHom := rfl

/-- A composite of injective semilinear maps is injective, stated for the coercion of `g.comp f`. -/
theorem injective_comp {g : N →ₛₗ[τ] P} {f : M →ₛₗ[σ] N} (hg : Function.Injective g)
    (hf : Function.Injective f) : Function.Injective (g.comp f : M →ₛₗ[υ] P) :=
  hg.comp hf

/-- A composite of surjective semilinear maps is surjective, stated for the coercion of
`g.comp f`. -/
theorem surjective_comp {g : N →ₛₗ[τ] P} {f : M →ₛₗ[σ] N} (hg : Function.Surjective g)
    (hf : Function.Surjective f) : Function.Surjective (g.comp f : M →ₛₗ[υ] P) :=
  hg.comp hf

section Paste

variable {R U V W V' W' Y : Type*} [Semiring R] [AddCommMonoid U] [AddCommMonoid V]
  [AddCommMonoid W] [AddCommMonoid V'] [AddCommMonoid W'] [AddCommMonoid Y] [Module R U]
  [Module R V] [Module R W] [Module R V'] [Module R W'] [Module R Y]

/-- **Pasting a commutative square onto a factorization.** If `ψ ∘ y = g ∘ q` and the square
`b ∘ ψ = ψ' ∘ a` commutes, then `ψ' ∘ (a ∘ y) = (b ∘ g) ∘ q`: a lift of `g ∘ q` along `ψ`,
followed by `a`, is a lift of `(b ∘ g) ∘ q` along `ψ'`. -/
theorem comp_comp_eq_comp_comp_of_comp_eq {ψ : V →ₗ[R] W} {ψ' : V' →ₗ[R] W'} {a : V →ₗ[R] V'}
    {b : W →ₗ[R] W'} (h : b ∘ₗ ψ = ψ' ∘ₗ a) {y : U →ₗ[R] V} {g : Y →ₗ[R] W} {q : U →ₗ[R] Y}
    (hy : ψ ∘ₗ y = g ∘ₗ q) : ψ' ∘ₗ (a ∘ₗ y) = (b ∘ₗ g) ∘ₗ q := by
  rw [← comp_assoc, ← h, comp_assoc, hy, comp_assoc]

end Paste

end LinearMap

namespace AddMonoidHom

/-- Viewing the identity additive homomorphism as a `ℤ`-linear map gives the identity linear map. -/
@[simp]
theorem toIntLinearMap_id (M : Type*) [AddCommGroup M] :
    (AddMonoidHom.id M).toIntLinearMap = LinearMap.id :=
  LinearMap.ext fun _ ↦ by simp

/-- Viewing a composite of additive homomorphisms as a `ℤ`-linear map gives the composite of
their `ℤ`-linear maps. -/
@[simp]
theorem toIntLinearMap_comp {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (g : N →+ P) (f : M →+ N) :
    (g.comp f).toIntLinearMap = g.toIntLinearMap ∘ₗ f.toIntLinearMap :=
  LinearMap.ext fun _ ↦ by simp

end AddMonoidHom
