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

A ring homomorphism out of a symmetric algebra is determined by its values on scalars and on
generators (`SymmetricAlgebra.ringHom_ext`), even when its target is nonassociative. The `ext`
tactic reduces equality of these homomorphisms to agreement on scalars and generators.
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

namespace SymmetricAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A ring homomorphism out of a symmetric algebra is determined by its values on scalars and on
generators. See note [partially-applied ext lemmas]. -/
@[ext high]
theorem ringHom_ext {A : Type*} [NonAssocSemiring A] {F G : SymmetricAlgebra R M →+* A}
    (h₁ : F.comp (algebraMap R _) = G.comp (algebraMap R _))
    (h₂ : ∀ m, F (ι R M m) = G (ι R M m)) : F = G := by
  refine RingHom.ext fun x ↦ ?_
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => exact DFunLike.congr_fun h₁ r
  | ι m => exact h₂ m
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

end SymmetricAlgebra

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
        simpa only [← map_smul, smul_eq_mul, mul_one] using
          f.range.smul_mem hgen r
    | mul y z hy hz => exact mul_mem hy hz
    | add y z hy hz => exact add_mem hy hz
  exact (AlgHom.mem_range _).mp hy

end AlgHom
