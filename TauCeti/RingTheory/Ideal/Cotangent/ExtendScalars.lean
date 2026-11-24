/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import TauCeti.Algebra.Category.ModuleCat.ExtendScalarsQuotient

/-!
# Extension of scalars of an ideal to its quotient ring

For an ideal `J` of a commutative ring `R`, extending scalars of the `R`-module `J` along the
quotient map `R → R ⧸ J` gives the conormal module `J ⧸ J² = J.Cotangent`
(`Ideal.extendScalarsMkEquivQuotSMul` for `M = J`): the algebraic form of the fact that pulling
the ideal sheaf of a closed subscheme back to the subscheme gives its conormal sheaf.

## Main declarations

* `Ideal.extendScalarsMkEquivCotangent J`: the `R ⧸ J`-linear isomorphism between the extension
  of scalars of `J` along `Ideal.Quotient.mk J` and the conormal module `J.Cotangent`.
-/

public section

open CategoryTheory

universe u

namespace Ideal

variable {R : Type u} [CommRing R] (J : Ideal R)

/-- The extension of scalars of the `R`-module `J` along `R → R ⧸ J` is the conormal module
`J ⧸ J²`. -/
noncomputable def extendScalarsMkEquivCotangent :
    (ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj (ModuleCat.of R J) ≃ₗ[R ⧸ J]
      J.Cotangent :=
  extendScalarsMkEquivQuotSMul J J

/-- `Ideal.extendScalarsMkEquivCotangent` sends `Ideal.Quotient.mk J r ⊗ₜ m` to the class of
`r • m` in `J.Cotangent`. -/
@[simp]
theorem extendScalarsMkEquivCotangent_mk_tmul (r : R) (m : J) :
    extendScalarsMkEquivCotangent J
        (Ideal.Quotient.mk J r ⊗ₜ[R] m :
          (ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj (ModuleCat.of R J)) =
      J.toCotangent (r • m) := by
  rw [extendScalarsMkEquivCotangent, extendScalarsMkEquivQuotSMul_mk_tmul, Ideal.toCotangent,
    Submodule.mkQ_apply]

end Ideal
