/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Extension of scalars to the quotient by an ideal

For an ideal `J` of a commutative ring `R` and an `R`-module `M`, extending scalars of `M` along
the quotient map `R → R ⧸ J` gives `(R ⧸ J) ⊗[R] M ≃ M ⧸ J • M`, as `R ⧸ J`-modules. For `M = J`
this is the conormal module `J ⧸ J² = J.Cotangent`: the algebraic form of the fact that pulling
the ideal sheaf of a closed subscheme back to the subscheme gives its conormal sheaf.

## Main declarations

* `Ideal.extendScalarsMkEquivQuotSMul J M`: the `R ⧸ J`-linear isomorphism between the extension
  of scalars of `M` along `Ideal.Quotient.mk J` and `M ⧸ J • M`.
* `Ideal.extendScalarsMkEquivCotangent J`: its case `M = J`, with values in the conormal module
  `J.Cotangent`.
-/

public section

open CategoryTheory

universe u v

namespace Ideal

variable {R : Type u} [CommRing R] (J : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

/-- The extension of scalars of an `R`-module `M` along `R → R ⧸ J` is `M ⧸ J • M`: the
`R`-linear isomorphism `(R ⧸ J) ⊗[R] M ≃ M ⧸ J • M` of `TensorProduct.quotTensorEquivQuotSMul` is
`R ⧸ J`-linear. -/
noncomputable def extendScalarsMkEquivQuotSMul :
    (ModuleCat.extendScalars.{u, u, v} (Ideal.Quotient.mk J)).obj (ModuleCat.of R M) ≃ₗ[R ⧸ J]
      M ⧸ (J • ⊤ : Submodule R M) :=
  -- The extension of scalars is `A ⊗[R] M` for `A` the ring `R ⧸ J` with the `R`-module structure
  -- obtained by restriction of scalars, which agrees with the usual one up to a non-definitional
  -- identification.
  let A := (ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj (ModuleCat.of (R ⧸ J) (R ⧸ J))
  let eA : A ≃ₗ[R] R ⧸ J :=
    { toFun := fun x ↦ x, invFun := fun x ↦ x, map_add' := fun _ _ ↦ rfl,
      map_smul' := fun r x ↦ (Algebra.smul_def r (show R ⧸ J from x)).symm,
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }
  let e : TensorProduct R A M ≃ₗ[R] M ⧸ (J • ⊤ : Submodule R M) :=
    TensorProduct.congr eA (LinearEquiv.refl R M) ≪≫ₗ TensorProduct.quotTensorEquivQuotSMul M J
  letI : Module R ((ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj (ModuleCat.of R M)) :=
    inferInstanceAs (Module R (TensorProduct R A M))
  { toFun := e, invFun := e.symm, map_add' := e.map_add, left_inv := e.left_inv,
    right_inv := e.right_inv
    map_smul' := by
      intro s t
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
      -- On the tensor product, `Ideal.Quotient.mk J r` acts as `r`.
      have : Ideal.Quotient.mk J r • t = r • t := by
        induction t using TensorProduct.inductionOn with
        | tmul a m => rfl
        | add x y hx hy =>
          exact (smul_add (A := (ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj
            (ModuleCat.of R M)) (Ideal.Quotient.mk J r) x y).trans
            ((congrArg₂ (· + ·) hx hy).trans (smul_add (A := (ModuleCat.extendScalars
              (Ideal.Quotient.mk J)).obj (ModuleCat.of R M)) r x y).symm)
      simp only [RingHom.id_apply]
      rw [this]
      exact e.map_smul r t }

/-- `Ideal.extendScalarsMkEquivQuotSMul` sends `Ideal.Quotient.mk J r ⊗ₜ m` to the class of
`r • m`. -/
@[simp]
theorem extendScalarsMkEquivQuotSMul_mk_tmul (r : R) (m : M) :
    extendScalarsMkEquivQuotSMul J M
        (Ideal.Quotient.mk J r ⊗ₜ[R] m :
          (ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj (ModuleCat.of R M)) =
      Submodule.Quotient.mk (r • m) :=
  TensorProduct.quotTensorEquivQuotSMul_mk_tmul (M := M) J r m

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
      J.toCotangent (r • m) :=
  extendScalarsMkEquivQuotSMul_mk_tmul J J r m

end Ideal
