/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AbsoluteValue.Action
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# The Galois action on infinite places as an action on absolute values

Mathlib's action of `Gal(K/k)` on the infinite places of `K` is the restriction of the action of
`K ≃ₐ[k] K` on all absolute values of `K` by `σ • w = w ∘ σ⁻¹`
(`AbsoluteValue.instMulActionAlgEquiv`): the absolute value underlying `σ • w` is `σ` acting on
the absolute value underlying `w` (`NumberField.InfinitePlace.coe_smul`).
-/

public section

namespace NumberField.InfinitePlace

/-- Mathlib's action of the Galois group on the infinite places is the restriction of its action on
absolute values. -/
@[simp]
theorem coe_smul {k K : Type*} [Field k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (w : InfinitePlace K) :
    (σ • w).1 = σ • w.1 :=
  rfl

end NumberField.InfinitePlace
