/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.Primitive.Decomposition
public import TauCeti.RingTheory.Idempotents.Projective
public import TauCeti.Algebra.Module.ProjectiveCover.Simple

/-!
# Primitive idempotents and simple heads

In a left Artinian ring `R`, an idempotent `e` is primitive exactly when the head of its left
ideal `Re` is simple. The head is the quotient `Re / J Re`, where `J` is the Jacobson radical.
Every surjection from `Re` onto a simple module is then a projective cover. Given a complete
primitive orthogonal family, these ideals supply projective covers of every simple module.

This connects the decomposition of the regular module by primitive idempotents to the simple
modules. It uses the general simple-head theorem for indecomposable projectives and the existing
occurrence theorem for simple quotients of a complete orthogonal family.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. 1, §I.4.
* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., §§23–24.
-/

public section

namespace TauCeti

variable {R : Type*} [Ring R] {e : R}

/-- If the head of the left ideal of an idempotent is simple, the idempotent is primitive.
This implication does not need an Artinian hypothesis. -/
theorem isPrimitiveIdempotent_of_isSimpleModule_quotient_jacobson_smul_top
    (he : IsIdempotentElem e)
    [IsSimpleModule R ((Ideal.span {e} : Ideal R) ⧸
      Ring.jacobson R • (⊤ : Submodule R (Ideal.span {e} : Ideal R)))] :
    IsPrimitiveIdempotent e := by
  have := he.projective_span_singleton
  have : Module.Finite R (Ideal.span {e} : Ideal R) :=
    Module.Finite.iff_fg.mpr (Submodule.fg_span_singleton e)
  have hcov := isProjectiveCover_mkQ_iff_le_jacobson.mpr
    (Ring.jacobson_smul_top_le R (Ideal.span {e} : Ideal R))
  exact isPrimitiveIdempotent_of_isIndecomposableModule he hcov.isIndecomposableModule

variable [IsArtinianRing R]

/-- The head `Re / J Re` of the left ideal of a primitive idempotent in a left Artinian ring
is simple. -/
theorem IsPrimitiveIdempotent.isSimpleModule_quotient_jacobson_smul_top
    (he : IsPrimitiveIdempotent e) :
    IsSimpleModule R ((Ideal.span {e} : Ideal R) ⧸
      Ring.jacobson R • (⊤ : Submodule R (Ideal.span {e} : Ideal R))) := by
  have := he.isIdempotentElem.projective_span_singleton
  exact he.isIndecomposableModule.isSimpleModule_quotient_jacobson_smul_top
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

/-- Every surjection from the left ideal of a primitive idempotent onto a simple module is
a projective cover. -/
theorem IsPrimitiveIdempotent.isProjectiveCover_of_surjective
    (he : IsPrimitiveIdempotent e) {S : Type*} [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] {f : (Ideal.span {e} : Ideal R) →ₗ[R] S}
    (hf : Function.Surjective f) : IsProjectiveCover f := by
  have := IsSimpleModule.nontrivial R S
  have := he.isIdempotentElem.projective_span_singleton
  have := he.isSimpleModule_quotient_jacobson_smul_top
  exact isProjectiveCover_of_isSimpleModule_quotient_jacobson_smul_top hf

end TauCeti

namespace CompleteOrthogonalIdempotents

variable {R : Type*} [Ring R] [IsArtinianRing R] {ι : Type*} [Fintype ι] {e : ι → R}

/-- A complete family of primitive orthogonal idempotents supplies projective covers of
every simple module by its principal left ideals. -/
theorem exists_isProjectiveCover_of_isSimpleModule (he : CompleteOrthogonalIdempotents e)
    (hprim : ∀ i, TauCeti.IsPrimitiveIdempotent (e i))
    (S : Type*) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    ∃ (i : ι) (f : (Ideal.span {e i} : Ideal R) →ₗ[R] S), TauCeti.IsProjectiveCover f := by
  obtain ⟨i, f, hf⟩ := he.exists_surjective_of_isSimpleModule S
  exact ⟨i, f, (hprim i).isProjectiveCover_of_surjective hf⟩

end CompleteOrthogonalIdempotents
