/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Prod

/-!
# Exact sequences of linear maps

This file records elementary constructions and consequences for exact pairs of linear maps.
-/

public section

namespace TauCeti

/-- The product of exact pairs of linear maps is exact. -/
theorem _root_.Function.Exact.prodMap
    {R M₁ N₁ P₁ M₂ N₂ P₂ : Type*} [Semiring R]
    [AddCommMonoid M₁] [AddCommMonoid N₁] [AddCommMonoid P₁]
    [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂]
    [Module R M₁] [Module R N₁] [Module R P₁]
    [Module R M₂] [Module R N₂] [Module R P₂]
    {f₁ : M₁ →ₗ[R] N₁} {g₁ : N₁ →ₗ[R] P₁}
    {f₂ : M₂ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] P₂}
    (h₁ : Function.Exact f₁ g₁) (h₂ : Function.Exact f₂ g₂) :
    Function.Exact (f₁.prodMap f₂) (g₁.prodMap g₂) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y₁, hy₁⟩ := (h₁ x.1).1 (congrArg Prod.fst hx)
    obtain ⟨y₂, hy₂⟩ := (h₂ x.2).1 (congrArg Prod.snd hx)
    exact ⟨(y₁, y₂), by ext <;> assumption⟩
  · rintro ⟨y, rfl⟩
    exact Prod.ext ((h₁ _).2 ⟨y.1, rfl⟩) ((h₂ _).2 ⟨y.2, rfl⟩)

/-- If `M --f--> N --g--> P` is exact at `N` and both `M` and `P` are finite-dimensional, then so
is `N`.

This is deduced from `Module.Finite.of_exact`, which asks the second map to be surjective, by
corestricting `g` to its range. -/
theorem finiteDimensional_of_exact {k M N P : Type*} [DivisionRing k] [AddCommGroup M]
    [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P] {f : M →ₗ[k] N}
    {g : N →ₗ[k] P}
    (h : Function.Exact f g) [FiniteDimensional k M] [FiniteDimensional k P] :
    FiniteDimensional k N :=
  Module.Finite.of_exact (g := g.rangeRestrict)
    (fun x ↦ by rw [← h x, ← Subtype.coe_inj]; simp) g.surjective_rangeRestrict

/-- If `M --f--> N --g--> P` is exact at `N` and both `M` and `P` are trivial, then so is `N`. -/
theorem subsingleton_of_exact {M N P : Type*} [Zero P] {f : M → N} {g : N → P}
    (h : Function.Exact f g) [Subsingleton M] [Subsingleton P] : Subsingleton N :=
  ⟨fun x y ↦ by
    -- `P` is trivial, so both `x` and `y` are hit by `f`; `M` is trivial, so by the same element.
    obtain ⟨a, rfl⟩ := (h x).1 (Subsingleton.elim _ _)
    obtain ⟨b, rfl⟩ := (h y).1 (Subsingleton.elim _ _)
    rw [Subsingleton.elim a b]⟩

end TauCeti
