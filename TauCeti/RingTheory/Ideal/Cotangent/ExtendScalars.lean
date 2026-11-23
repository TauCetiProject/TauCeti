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
# Extension of scalars of an ideal to the quotient ring

For an ideal `J` of a commutative ring `R`, extending scalars of the `R`-module `J` along the
quotient map `R → R ⧸ J` gives the conormal module: `(R ⧸ J) ⊗[R] J ≃ J ⧸ J² = J.Cotangent`, as
`R ⧸ J`-modules. This is the algebraic form of the fact that pulling the ideal sheaf of a closed
subscheme back to the subscheme gives its conormal sheaf.

## Main declarations

* `Ideal.extendScalarsMkEquivCotangent J`: the `R ⧸ J`-linear isomorphism between the extension of
  scalars of `J` along `Ideal.Quotient.mk J` and the conormal module `J.Cotangent`.
-/

public section

open CategoryTheory

universe u

namespace Ideal

variable {R : Type u} [CommRing R] (J : Ideal R)

/-- The extension of scalars of the `R`-module `J` along `R → R ⧸ J` is the conormal module
`J ⧸ J²`: the `R`-linear isomorphism `(R ⧸ J) ⊗[R] J ≃ J ⧸ J • J` of
`TensorProduct.quotTensorEquivQuotSMul` is `R ⧸ J`-linear. -/
noncomputable def extendScalarsMkEquivCotangent :
    (ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj (ModuleCat.of R J) ≃ₗ[R ⧸ J]
      J.Cotangent :=
  -- The extension of scalars is `A ⊗[R] J` for `A` the ring `R ⧸ J` with the `R`-module structure
  -- obtained by restriction of scalars, which agrees with the usual one up to a non-definitional
  -- identification.
  let A := (ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj (ModuleCat.of (R ⧸ J) (R ⧸ J))
  let eA : A ≃ₗ[R] R ⧸ J :=
    { toFun := fun x ↦ x, invFun := fun x ↦ x, map_add' := fun _ _ ↦ rfl,
      map_smul' := fun r x ↦ (Algebra.smul_def r (show R ⧸ J from x)).symm,
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }
  let e : TensorProduct R A J ≃ₗ[R] J.Cotangent :=
    TensorProduct.congr eA (LinearEquiv.refl R J) ≪≫ₗ TensorProduct.quotTensorEquivQuotSMul J J
  letI : Module R ((ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj (ModuleCat.of R J)) :=
    inferInstanceAs (Module R (TensorProduct R A J))
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
            (ModuleCat.of R J)) (Ideal.Quotient.mk J r) x y).trans
            ((congrArg₂ (· + ·) hx hy).trans (smul_add (A := (ModuleCat.extendScalars
              (Ideal.Quotient.mk J)).obj (ModuleCat.of R J)) r x y).symm)
      simp only [RingHom.id_apply]
      rw [this]
      exact e.map_smul r t }

/-- `Ideal.extendScalarsMkEquivCotangent` sends `Ideal.Quotient.mk J r ⊗ₜ m` to the class of
`r • m` in `J.Cotangent`. -/
theorem extendScalarsMkEquivCotangent_tmul (r : R) (m : J) :
    extendScalarsMkEquivCotangent J
        (Ideal.Quotient.mk J r ⊗ₜ[R] m :
          (ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj (ModuleCat.of R J)) =
      J.toCotangent (r • m) :=
  TensorProduct.quotTensorEquivQuotSMul_mk_tmul (M := J) J r m

end Ideal
