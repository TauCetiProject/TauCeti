/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Injectivity of symmetric-algebra generators

The canonical map from a module over a commutative semiring into its symmetric algebra is
injective, without a freeness assumption. Its main application is that an abelian Lie algebra
embeds in its universal enveloping algebra, which is its symmetric algebra
(`TauCeti.UniversalEnvelopingAlgebra.ι_injective_of_isLieAbelian`).
-/

public section

namespace TauCeti.SymmetricAlgebra

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The canonical map into the symmetric algebra is injective for every module over a
commutative semiring. -/
theorem ι_injective : Function.Injective (_root_.SymmetricAlgebra.ι R M) := by
  -- Adapted from Mathlib's `TensorAlgebra.ι_leftInverse`.
  let : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  have : IsCentralScalar R M := ⟨fun _ _ ↦ rfl⟩
  exact Function.LeftInverse.injective (g := (TrivSqZeroExt.sndHom R M).comp
    (_root_.SymmetricAlgebra.lift (TrivSqZeroExt.inrHom R M)).toLinearMap) fun x ↦ by simp

end TauCeti.SymmetricAlgebra
