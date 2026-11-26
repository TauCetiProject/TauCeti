/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Normed spaces indexed by a sum type

A family `Sum.elim E₁ E₂` indexed by `α ⊕ β` takes the value `E₁ a` at `Sum.inl a` and `E₂ b` at
`Sum.inr b`. When `E₁` and `E₂` are families of normed groups, normed spaces over `𝕜` or
finite-dimensional spaces over `𝕜`, so is `Sum.elim E₁ E₂`. These are the obstruction spaces of a
product of implicit atlases, in the sense of Pardon.
-/

public section

namespace Sum

universe u

variable {α β : Type*} {E₁ : α → Type u} {E₂ : β → Type u}

/-- The family `Sum.elim E₁ E₂` indexed by `α ⊕ β` is a family of normed groups when `E₁` and `E₂`
are. -/
instance instNormedAddCommGroupElim [∀ a, NormedAddCommGroup (E₁ a)]
    [∀ b, NormedAddCommGroup (E₂ b)] : ∀ i : α ⊕ β, NormedAddCommGroup (Sum.elim E₁ E₂ i)
  | .inl a => inferInstanceAs (NormedAddCommGroup (E₁ a))
  | .inr b => inferInstanceAs (NormedAddCommGroup (E₂ b))

variable (𝕜 : Type*) [NormedField 𝕜] [∀ a, NormedAddCommGroup (E₁ a)]
  [∀ b, NormedAddCommGroup (E₂ b)]

/-- The family `Sum.elim E₁ E₂` indexed by `α ⊕ β` is a family of normed spaces over `𝕜` when `E₁`
and `E₂` are. -/
instance instNormedSpaceElim [∀ a, NormedSpace 𝕜 (E₁ a)] [∀ b, NormedSpace 𝕜 (E₂ b)] :
    ∀ i : α ⊕ β, NormedSpace 𝕜 (Sum.elim E₁ E₂ i)
  | .inl a => inferInstanceAs (NormedSpace 𝕜 (E₁ a))
  | .inr b => inferInstanceAs (NormedSpace 𝕜 (E₂ b))

/-- The family `Sum.elim E₁ E₂` indexed by `α ⊕ β` is a family of finite-dimensional spaces over
`𝕜` when `E₁` and `E₂` are. -/
instance instFiniteDimensionalElim [∀ a, NormedSpace 𝕜 (E₁ a)] [∀ b, NormedSpace 𝕜 (E₂ b)]
    [∀ a, FiniteDimensional 𝕜 (E₁ a)] [∀ b, FiniteDimensional 𝕜 (E₂ b)] :
    ∀ i : α ⊕ β, FiniteDimensional 𝕜 (Sum.elim E₁ E₂ i)
  | .inl a => inferInstanceAs (FiniteDimensional 𝕜 (E₁ a))
  | .inr b => inferInstanceAs (FiniteDimensional 𝕜 (E₂ b))

end Sum
