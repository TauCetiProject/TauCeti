/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Generators of symmetric algebras

The canonical map from a module over a commutative semiring into its symmetric algebra is
injective, without a freeness assumption. Its main application is that an abelian Lie algebra
embeds in its universal enveloping algebra, which is its symmetric algebra
(`TauCeti.UniversalEnvelopingAlgebra.ι_injective_of_isLieAbelian`).

For the symmetric algebra of the base semiring itself, the degree-one element `ι R R 1`
generates the whole algebra. An algebra morphism whose range contains this element is therefore
surjective, a criterion used for coordinate morphisms of additive root subgroups.
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

namespace AlgHom

/-- An algebra morphism into the symmetric algebra of the base semiring is surjective if its
range contains the degree-one generator. -/
theorem surjective_of_ι_one_mem_range {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] (f : A →ₐ[R] SymmetricAlgebra R R)
    (hgen : SymmetricAlgebra.ι R R 1 ∈ f.range) : Function.Surjective f := by
  intro y
  have hy : y ∈ f.range := by
    induction y using SymmetricAlgebra.induction with
    | algebraMap r => exact f.range.algebraMap_mem r
    | ι r =>
        have hr : SymmetricAlgebra.ι R R r = r • SymmetricAlgebra.ι R R 1 := by
          rw [← map_smul]
          simp
        rw [hr]
        exact Submodule.smul_mem f.range.toSubmodule r hgen
    | mul y z hy hz => exact mul_mem hy hz
    | add y z hy hz => exact add_mem hy hz
  exact (AlgHom.mem_range _).mp hy

end AlgHom
