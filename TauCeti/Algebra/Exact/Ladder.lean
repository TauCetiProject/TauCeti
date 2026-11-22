/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic

/-!
# Correcting a lift along a ladder

Given a commutative diagram of additive homomorphisms

```text
M₁ --f--> M₂ --g--> M₃
|α        |β        |γ
N₁ --f'-> N₂ --g'-> N₃
```

whose top row composes to zero, whose bottom row is exact and whose left map `α` is surjective,
every `y ∈ M₂` with `γ (g y) = 0` has some `w ∈ M₁` such that `y + f w` lies in `ker β` and has
the same image as `y` under `g`
(`Function.Exact.exists_apply_eq_zero_and_apply_eq_of_surjective`). This is the lifting step of
the snake lemma at `ker γ` when `coker α = 0`. The maps `f` and `f'` need not be injective, and
only `N₂` has to be an additive group, not necessarily commutative.
-/

public section

/-- **Correcting a lift into a kernel.** Given a commutative diagram of additive homomorphisms

```text
M₁ --f--> M₂ --g--> M₃
|α        |β        |γ
N₁ --f'-> N₂ --g'-> N₃
```

whose top row composes to zero, whose bottom row is exact and whose left map `α` is surjective,
every `y ∈ M₂` with `γ (g y) = 0` has some `w ∈ M₁` with `y + f w ∈ ker β` and
`g (y + f w) = g y`. This is the lifting step of the snake lemma at `ker γ` when `coker α = 0`;
the maps `f` and `f'` need not be injective, and only `N₂` needs negation. -/
theorem Function.Exact.exists_apply_eq_zero_and_apply_eq_of_surjective
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddZeroClass M₁] [AddZeroClass M₂] [AddZeroClass M₃]
    [AddZeroClass N₁] [AddGroup N₂] [AddZeroClass N₃] {f : M₁ →+ M₂} {g : M₂ →+ M₃}
    {f' : N₁ →+ N₂} {g' : N₂ →+ N₃} {α : M₁ →+ N₁} {β : M₂ →+ N₂} {γ : M₃ →+ N₃}
    (hfg' : Exact f' g') (hfg : ∀ x, g (f x) = 0) (hα : Surjective α)
    (hαβ : ∀ x, β (f x) = f' (α x)) (hβγ : ∀ y, γ (g y) = g' (β y)) {y : M₂}
    (hy : γ (g y) = 0) : ∃ w, β (y + f w) = 0 ∧ g (y + f w) = g y := by
  -- `g' (-β y) = 0` (`N₃` need not be a group, so this goes through `g' (-β y) + g' (β y) = 0`),
  -- so `-β y = f' (α w) = β (f w)` for some `w ∈ M₁`
  have h : g' (β y) = 0 := (hβγ y).symm.trans hy
  obtain ⟨x, hx⟩ := (hfg' (-β y)).1 <| by simpa [h] using (map_add g' (-β y) (β y)).symm
  obtain ⟨w, rfl⟩ := hα x
  exact ⟨w, by simp [hαβ, hx], by simp [hfg]⟩
