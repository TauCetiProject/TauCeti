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

`LieHom.baseChange` extends the scalars of a homomorphism of Lie algebras.  Applied to the
quotient map of an ideal `I` it presents `A ⊗[R] (L ⧸ I)` as the quotient of `A ⊗[R] L` by the
extension of `I`, the isomorphism

`(A ⊗[R] L) ⧸ I.baseChange A ≃ₗ⁅A⁆ A ⊗[R] (L ⧸ I)`.

Both halves of the bijectivity are right-exactness of the tensor product, so nothing is asked of
the coefficient algebra: the kernel is computed by `LieHom.ker_baseChange_of_surjective` and the
surjectivity by `LieHom.baseChange_surjective`.  Flatness enters only for the kernel of a
homomorphism that is *not* surjective, which is `LieHom.ker_baseChange`.

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
theorem ker_baseChange_mkQ : (LieHom.baseChange A I.mkQ).ker = I.baseChange A := by
  rw [LieHom.ker_baseChange_of_surjective A I.mkQ I.mkQ_surjective, ker_mkQ]

/-- **Extension of scalars commutes with quotients of Lie algebras.**  The extended quotient map
presents `A ⊗[R] (L ⧸ I)` as the quotient of `A ⊗[R] L` by the extension of `I`.

The isomorphism is the obvious one, sending the class of `a ⊗ₜ x` to `a ⊗ₜ` the class of `x`;
that is `LieIdeal.quotientBaseChangeEquiv_mk_tmul`.  The characterizing lemmas below are phrased
with `LieSubmodule.Quotient.mk` rather than `LieIdeal.mkQ`, which is the form the quotient's
induction principle produces. -/
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
