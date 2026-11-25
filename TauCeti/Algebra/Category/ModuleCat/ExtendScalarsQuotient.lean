/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Extension of scalars to the quotient by an ideal

For an ideal `J` of a commutative ring `R` and an `R`-module `M`, extending scalars of `M` along
the quotient map `R → R ⧸ J` gives `(R ⧸ J) ⊗[R] M ≃ M ⧸ J • M`, as `R ⧸ J`-modules.

## Main declarations

* `Ideal.extendScalarsMkEquivQuotSMul J M`: the `R ⧸ J`-linear isomorphism between the extension
  of scalars of `M` along `Ideal.Quotient.mk J` and `M ⧸ J • M`.
-/

public section

open CategoryTheory

universe u v

namespace Ideal

variable {R : Type u} [CommRing R] (J : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

/-- The extension of scalars of an `R`-module `M` along `R → R ⧸ J` is `M ⧸ J • M`, as
`R ⧸ J`-modules. -/
noncomputable def extendScalarsMkEquivQuotSMul :
    (ModuleCat.extendScalars.{u, u, v} (Ideal.Quotient.mk J)).obj (ModuleCat.of R M) ≃ₗ[R ⧸ J]
      M ⧸ (J • ⊤ : Submodule R M) :=
  -- Identify the extension of scalars with `(R ⧸ J) ⊗[R] M`
  -- (`ModuleCat.extendScalarsAlgebraMapIso`), then apply `TensorProduct.quotTensorEquivQuotSMul`,
  -- which is `R ⧸ J`-linear because `R → R ⧸ J` is surjective.
  (ModuleCat.extendScalarsAlgebraMapIso (S := R ⧸ J) (ModuleCat.of R M)).toLinearEquiv ≪≫ₗ
    (TensorProduct.quotTensorEquivQuotSMul M J).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective

/-- `Ideal.extendScalarsMkEquivQuotSMul` sends `Ideal.Quotient.mk J r ⊗ₜ m` to the class of
`r • m`. -/
@[simp]
theorem extendScalarsMkEquivQuotSMul_mk_tmul (r : R) (m : M) :
    extendScalarsMkEquivQuotSMul J M
        (Ideal.Quotient.mk J r ⊗ₜ[R] m :
          (ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj (ModuleCat.of R M)) =
      Submodule.Quotient.mk (r • m) :=
  -- The first factor sends `r ⊗ m` to `r ⊗ m`, and the second sends that to the class of `r • m`.
  (congrArg (TensorProduct.quotTensorEquivQuotSMul M J)
    (ModuleCat.extendScalarsAlgebraMapIso_hom_tmul (S := R ⧸ J) (ModuleCat.of R M)
      (Ideal.Quotient.mk J r) m)).trans (TensorProduct.quotTensorEquivQuotSMul_mk_tmul J r m)

end Ideal
