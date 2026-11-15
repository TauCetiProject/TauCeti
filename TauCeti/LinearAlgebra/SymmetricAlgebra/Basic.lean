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
injective, without a freeness assumption (`SymmetricAlgebra.ι_injective`). Its main application
is that an abelian Lie algebra embeds in its universal enveloping algebra, which is its symmetric
algebra (`TauCeti.UniversalEnvelopingAlgebra.ι_injective_of_isLieAbelian`).

The canonical generators generate the symmetric algebra (`SymmetricAlgebra.adjoin_range_ι`),
and so do the images of any spanning family
(`SymmetricAlgebra.adjoin_range_ι_comp_eq_top_of_span_eq_top`).

For the symmetric algebra of the base semiring itself, the degree-one element `ι R R 1`
generates the whole algebra. An algebra morphism whose range contains this element is therefore
surjective, a criterion used for coordinate morphisms of additive root subgroups.

A ring homomorphism out of a symmetric algebra is determined by its values on scalars and on
generators (`SymmetricAlgebra.ringHom_ext`), even when its target is nonassociative. The `ext`
tactic reduces equality of these homomorphisms to agreement on scalars and generators.
The inverse of the universal property `SymmetricAlgebra.lift` restricts an algebra morphism
to the generators (`SymmetricAlgebra.lift_symm_apply`).
-/

public section

namespace SymmetricAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable (R M) in
/-- The canonical map into the symmetric algebra is injective for every module over a
commutative semiring. -/
theorem ι_injective : Function.Injective (ι R M) := by
  -- Adapted from Mathlib's `TensorAlgebra.ι_leftInverse`.
  let : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  have : IsCentralScalar R M := ⟨fun _ _ ↦ rfl⟩
  exact Function.LeftInverse.injective (g := (TrivSqZeroExt.sndHom R M).comp
    (lift (TrivSqZeroExt.inrHom R M)).toLinearMap) fun x ↦ by simp

variable (R M) in
/-- The symmetric algebra is generated as an algebra by the image of the generator map. -/
theorem adjoin_range_ι : Algebra.adjoin R (Set.range (ι R M)) = ⊤ :=
  top_unique fun x _ ↦ SymmetricAlgebra.induction R M (algebraMap_mem _)
    (fun m ↦ Algebra.subset_adjoin (Set.mem_range_self m)) (fun _ _ ↦ mul_mem)
    (fun _ _ ↦ add_mem) x

/-- The images of a spanning family generate the symmetric algebra as an algebra. -/
theorem adjoin_range_ι_comp_eq_top_of_span_eq_top {ι : Type*} (x : ι → M)
    (hx : Submodule.span R (Set.range x) = ⊤) :
    Algebra.adjoin R (Set.range (SymmetricAlgebra.ι R M ∘ x)) = ⊤ := by
  rw [Set.range_comp, ← Algebra.adjoin_span, Submodule.span_image, hx, Submodule.map_top,
    LinearMap.coe_range, adjoin_range_ι]

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

/-- The inverse of `SymmetricAlgebra.lift` restricts an algebra morphism to the generators: it
sends `H` to the linear map `x ↦ H (ι x)`. -/
@[simp]
theorem lift_symm_apply {A : Type*} [CommSemiring A] [Algebra R A]
    (H : SymmetricAlgebra R M →ₐ[R] A) : lift.symm H = H.toLinearMap ∘ₗ ι R M :=
  lift.symm_apply_eq.2 <| by ext; simp

end SymmetricAlgebra

namespace AlgHom

/-- An algebra morphism into the symmetric algebra of the base semiring is surjective if its
range contains the degree-one generator. -/
theorem surjective_of_ι_one_mem_range {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] (f : A →ₐ[R] SymmetricAlgebra R R)
    (hgen : SymmetricAlgebra.ι R R 1 ∈ f.range) : Function.Surjective f := by
  rw [← f.range_eq_top, eq_top_iff, ← SymmetricAlgebra.adjoin_range_ι, Algebra.adjoin_le_iff]
  rintro _ ⟨r, rfl⟩
  simpa only [SetLike.mem_coe, ← map_smul, smul_eq_mul, mul_one] using f.range.smul_mem hgen r

end AlgHom
