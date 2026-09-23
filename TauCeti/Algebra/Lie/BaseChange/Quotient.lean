/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Hom
public import TauCeti.Algebra.Lie.Quotient

/-!
# Extension of scalars commutes with quotients of Lie algebras

For a Lie ideal `I` of `L` and an `R`-algebra `A`, extending the scalars of the quotient `L ⧸ I`
gives the same Lie algebra over `A` as quotienting the extension `A ⊗[R] L` by the extension of
`I`:

`(A ⊗[R] L) ⧸ I.baseChange A ≃ₗ⁅A⁆ A ⊗[R] (L ⧸ I)`.

Nothing is asked of the coefficient algebra; in particular `A` need not be flat over `R`.  The
isomorphism is the obvious one on pure tensors, and it and its inverse are both characterized
there, so the bundled equivalence is not opaque.  Its use is to move a question about an ideal of
`A ⊗[R] L` containing an extended ideal to the extension of the corresponding quotient of `L`, as
the base change of the solvable radical does.

## Main definitions

* `LieIdeal.quotientBaseChangeEquiv`: **extension of scalars commutes with quotients.**

## Main results

* `LieIdeal.ker_baseChange_mkQ`: the extension of scalars of the quotient map of `I` kills exactly
  the extension of `I`.

## References

* [N. Bourbaki, *Algebra I, Chapters 1-3*][bourbaki1989], Chapter II, §3, n°6, for the
  right-exactness of the tensor product that the kernel computation rests on.
-/

public section

open TensorProduct

namespace LieIdeal

universe u v w

variable {R : Type u} {L : Type w} [CommRing R] [LieRing L] [LieAlgebra R L]
variable (A : Type v) [CommRing A] [Algebra R A] (I : LieIdeal R L)

/-- The extension of scalars of the quotient map of `I` kills exactly the extension of `I`. -/
@[simp]
theorem ker_baseChange_mkQ : (LieHom.baseChange A I.mkQ).ker = I.baseChange A := by
  rw [LieHom.ker_baseChange_of_surjective A I.mkQ I.mkQ_surjective, ker_mkQ]

/-- **Extension of scalars commutes with quotients of Lie algebras.**  The extension of `L ⧸ I`
is the quotient of the extension of `L` by the extension of `I`, for an arbitrary coefficient
algebra `A`.

The isomorphism sends the class of `a ⊗ₜ x` to `a ⊗ₜ` the class of `x`, which is
`LieIdeal.quotientBaseChangeEquiv_mk_tmul`; `LieIdeal.quotientBaseChangeEquiv_symm_tmul`
describes its inverse.  Both are phrased with `LieSubmodule.Quotient.mk` rather than
`LieIdeal.mkQ`, the form in which the quotient's induction principle presents a class. -/
noncomputable def quotientBaseChangeEquiv :
    ((A ⊗[R] L) ⧸ I.baseChange A) ≃ₗ⁅A⁆ A ⊗[R] (L ⧸ I) :=
  LieEquiv.ofBijective (liftQ (I.baseChange A) (LieHom.baseChange A I.mkQ)
      (ker_baseChange_mkQ A I).ge)
    ⟨liftQ_injective _ _ _ (ker_baseChange_mkQ A I).le,
      liftQ_surjective _ _ _ (LieHom.baseChange_surjective A I.mkQ I.mkQ_surjective)⟩

@[simp]
theorem quotientBaseChangeEquiv_mk (x : A ⊗[R] L) :
    quotientBaseChangeEquiv A I (LieSubmodule.Quotient.mk x) = LieHom.baseChange A I.mkQ x :=
  liftQ_apply (I.baseChange A) (LieHom.baseChange A I.mkQ) _ x

theorem quotientBaseChangeEquiv_mk_tmul (a : A) (x : L) :
    quotientBaseChangeEquiv A I (LieSubmodule.Quotient.mk (a ⊗ₜ[R] x)) =
      a ⊗ₜ[R] LieSubmodule.Quotient.mk x := by
  rw [quotientBaseChangeEquiv_mk, LieHom.baseChange_tmul, mkQ_apply]

@[simp]
theorem quotientBaseChangeEquiv_symm_tmul (a : A) (x : L) :
    (quotientBaseChangeEquiv A I).symm (a ⊗ₜ[R] LieSubmodule.Quotient.mk x) =
      LieSubmodule.Quotient.mk (a ⊗ₜ[R] x) :=
  (quotientBaseChangeEquiv A I).symm_apply_eq.mpr (quotientBaseChangeEquiv_mk_tmul A I a x).symm

end LieIdeal
