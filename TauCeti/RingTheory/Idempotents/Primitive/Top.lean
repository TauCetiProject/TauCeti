/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Projective.Top
public import TauCeti.RingTheory.Idempotents.Projective
public import TauCeti.RingTheory.Idempotents.Primitive.Decomposition

/-!
# Simple tops of primitive idempotent ideals

Let `A` be a semiprimary ring, with Jacobson radical `J`.  An idempotent `e` determines the
projective left ideal `Ae`, and its **top** is the semisimple quotient

`Ae / J(Ae)`.

This quotient is simple exactly when `e` is primitive, and its quotient map is the projective cover
of that simple module (`TauCeti.isProjectiveCover_mkQ_smul_top_span_singleton`).  Conversely, every
simple module over a left Artinian ring is isomorphic to the top of `Ae` for some primitive
idempotent `e`.

These results are the specializations to the projective module `Ae`
(`IsIdempotentElem.projective_span_singleton`) of the statements about tops of projective modules
in `TauCeti.Algebra.Module.Projective.Top`, such as
`TauCeti.isIndecomposableModule_iff_isSimpleModule_quotient_jacobson_smul_top`, since primitivity
of `e` is indecomposability of `Ae` (`TauCeti.isPrimitiveIdempotent_iff_isIndecomposableModule`).

## Main results

* `TauCeti.isProjectiveCover_mkQ_smul_top_span_singleton`: `Ae` covers its top.
* `TauCeti.isPrimitiveIdempotent_iff_isSimpleModule_quotient_jacobson_smul_top`: `e` is primitive
  exactly when `Ae / J(Ae)` is simple.
* `TauCeti.isSimpleModule_iff_exists_isPrimitiveIdempotent_quotient_jacobson_smul_top`: over a
  left Artinian ring, the simple modules are precisely these tops, up to linear equivalence.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Section I.4.
* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., Sections 23--24.
-/

public section

open scoped Pointwise

namespace TauCeti

universe u v

variable {A : Type u} [Ring A] {e : A}

/-- **The top of `Ae` is covered by `Ae`.**  For an idempotent `e` and a nilpotent ideal `I`, the
quotient map `Ae →ₗ[A] Ae / I(Ae)` is a projective cover; for `I = J` in a semiprimary ring this is
the cover of the top. -/
theorem isProjectiveCover_mkQ_smul_top_span_singleton (he : IsIdempotentElem e) {I : Ideal A}
    (hI : IsNilpotent I) :
    IsProjectiveCover (I • (⊤ : Submodule A (Ideal.span {e} : Ideal A))).mkQ :=
  have := he.projective_span_singleton
  isProjectiveCover_mkQ_smul_top_of_isNilpotent hI

/-- **A primitive idempotent is characterized by its simple top.**  In a semiprimary ring, an
idempotent `e` is primitive exactly when the radical quotient `Ae / J(Ae)` is a simple module. -/
theorem isPrimitiveIdempotent_iff_isSimpleModule_quotient_jacobson_smul_top
    [IsSemiprimaryRing A] (he : IsIdempotentElem e) :
    IsPrimitiveIdempotent e ↔
      IsSimpleModule A
        ((Ideal.span {e} : Ideal A) ⧸
          Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e} : Ideal A))) :=
  have := he.projective_span_singleton
  (isPrimitiveIdempotent_iff_isIndecomposableModule he).trans
    isIndecomposableModule_iff_isSimpleModule_quotient_jacobson_smul_top

/-- **Simple modules over a left Artinian ring are exactly the tops of primitive idempotent
ideals.** -/
theorem isSimpleModule_iff_exists_isPrimitiveIdempotent_quotient_jacobson_smul_top
    [IsArtinianRing A] (M : Type v) [AddCommGroup M] [Module A M] :
    IsSimpleModule A M ↔
      ∃ e : A, IsPrimitiveIdempotent e ∧
        Nonempty (M ≃ₗ[A]
          ((Ideal.span {e} : Ideal A) ⧸
            Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e} : Ideal A)))) := by
  constructor
  · intro hM
    let _ : IsSimpleModule A M := hM
    obtain ⟨n, e, he, hprim⟩ := exists_completeOrthogonalIdempotents_isPrimitiveIdempotent A
    obtain ⟨i, f, hf⟩ := he.exists_surjective_of_isSimpleModule M
    have := (hprim i).isIdempotentElem.projective_span_singleton
    exact ⟨e i, hprim i,
      ⟨(hprim i).isIndecomposableModule.quotientJacobsonEquivOfSurjective M f hf |>.symm⟩⟩
  · rintro ⟨e, he, ⟨φ⟩⟩
    have htop := (isPrimitiveIdempotent_iff_isSimpleModule_quotient_jacobson_smul_top
      he.isIdempotentElem).mp he
    exact φ.isSimpleModule_iff.mpr htop

end TauCeti
