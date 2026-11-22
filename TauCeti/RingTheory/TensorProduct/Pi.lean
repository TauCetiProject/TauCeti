/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Pi
public import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Tensor products of algebras and products

Mathlib's `Algebra.TensorProduct.prodRight` distributes `A ⊗[R] (B × C)` over the product in the
right factor. This file gives the algebra equivalence for a product in the left factor,
`(A₁ × A₂) ⊗[R] B ≃ₐ[S] (A₁ ⊗[R] B) × (A₂ ⊗[R] B)` for an `R`-algebra `S` whose algebra
structures on `A₁` and `A₂` restrict to their given `R`-algebra structures
(`IsScalarTower R S A₁` and `IsScalarTower R S A₂`): the algebra form of Mathlib's linear
`TensorProduct.prodLeft`. It also evaluates the inverse of Mathlib's
`Algebra.TensorProduct.piScalarRight : A ⊗[R] (ι → R) ≃ₐ[S] (ι → A)` on `Pi.single i x`, so that
`simp` computes the matrix entries of a base change of an algebra map between function algebras.
Finally, for a section `s` of one factor `B k` of a finite product, base-changing the composite of
`s` with the projection onto `B k` agrees with applying Mathlib's `Algebra.TensorProduct.piRight`
decomposition, projecting to coordinate `k`, and then applying the base change of `s`
(`AlgHom.sectionBaseChange_comp_evalAlgHom`).

## Main declarations

* `TauCeti.Algebra.TensorProduct.prodLeft`: the algebra equivalence above.
* `TauCeti.Algebra.TensorProduct.piScalarRight_symm_single`: the inverse of Mathlib's
  `Algebra.TensorProduct.piScalarRight` on `Pi.single i x`.
* `AlgHom.sectionBaseChange_comp_evalAlgHom`: base change of a section through a coordinate
  projection.
-/

public section

open scoped TensorProduct

namespace TauCeti.Algebra.TensorProduct

variable (R S A₁ A₂ B : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [Semiring A₁]
  [Semiring A₂] [Semiring B] [Algebra R A₁] [Algebra S A₁] [IsScalarTower R S A₁] [Algebra R A₂]
  [Algebra S A₂] [IsScalarTower R S A₂] [Algebra R B]

/-- The tensor product of algebras distributes over a product in the left factor:
`(A₁ × A₂) ⊗[R] B ≃ₐ[S] (A₁ ⊗[R] B) × (A₂ ⊗[R] B)`, linear over an `R`-algebra `S` whose algebra
structures on `A₁` and `A₂` restrict to their given `R`-algebra structures. -/
def prodLeft : (A₁ × A₂) ⊗[R] B ≃ₐ[S] (A₁ ⊗[R] B) × (A₂ ⊗[R] B) :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
    (_root_.TensorProduct.prodLeft R S A₁ A₂ B) (fun ⟨_, _⟩ ⟨_, _⟩ _ _ ↦ by simp)
    -- `(1, 1)` is `1` and `1 ⊗ₜ 1` is `1` (`Prod.mk_one_one`, `Algebra.TensorProduct.one_def`),
    -- both by `rfl`.
    (_root_.TensorProduct.prodLeft_tmul R S A₁ A₂ B 1 1 1)

variable {R S A₁ A₂ B}

/-- The linear equivalence underlying `prodLeft` is Mathlib's `TensorProduct.prodLeft`. -/
@[simp]
theorem prodLeft_toLinearEquiv :
    (prodLeft R S A₁ A₂ B).toLinearEquiv = _root_.TensorProduct.prodLeft R S A₁ A₂ B := by
  rw [prodLeft]
  rfl

/-- `prodLeft` sends a pure tensor `a ⊗ₜ b` to the pair `(a.1 ⊗ₜ b, a.2 ⊗ₜ b)`. -/
@[simp]
theorem prodLeft_tmul (a : A₁ × A₂) (b : B) :
    prodLeft R S A₁ A₂ B (a ⊗ₜ b) = (a.1 ⊗ₜ b, a.2 ⊗ₜ b) := by
  obtain ⟨a₁, a₂⟩ := a
  rw [prodLeft, Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply,
    _root_.TensorProduct.prodLeft_tmul]

/-- The inverse of `prodLeft` sends `(a₁ ⊗ₜ b, a₂ ⊗ₜ b)` to `(a₁, a₂) ⊗ₜ b`. -/
@[simp]
theorem prodLeft_symm_tmul (a₁ : A₁) (a₂ : A₂) (b : B) :
    (prodLeft R S A₁ A₂ B).symm (a₁ ⊗ₜ b, a₂ ⊗ₜ b) = (a₁, a₂) ⊗ₜ b :=
  (AlgEquiv.symm_apply_eq _).2 (prodLeft_tmul (a₁, a₂) b).symm

/-- The inverse of `piScalarRight` sends `Pi.single i x` to `x ⊗ₜ Pi.single i 1`: the algebra form
of Mathlib's `TensorProduct.piScalarRight_symm_single`. -/
@[simp]
theorem piScalarRight_symm_single (R S A : Type*) {ι : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Fintype ι]
    [DecidableEq ι] (x : A) (i : ι) :
    (Algebra.TensorProduct.piScalarRight R S A ι).symm (Pi.single i x) =
      x ⊗ₜ Pi.single i 1 := by
  rw [AlgEquiv.symm_apply_eq]
  ext k
  simp [Pi.single_apply]

end TauCeti.Algebra.TensorProduct

namespace AlgHom

/-- Base change of a section factoring through one coordinate of a product agrees with the
base-changed section on that coordinate of the base-changed product. -/
@[simp]
theorem sectionBaseChange_comp_evalAlgHom {A : Type*} [CommSemiring A]
    {κ : Type*} [Fintype κ] [DecidableEq κ] {B : κ → Type*}
    [∀ k, Semiring (B k)] [∀ k, Algebra A (B k)] {k : κ} (s : B k →ₐ[A] A)
    (T : Type*) [CommSemiring T] [Algebra A T] (x : T ⊗[A] (∀ k, B k)) :
    (s.comp (Pi.evalAlgHom A B k)).sectionBaseChange T x =
      s.sectionBaseChange T (Algebra.TensorProduct.piRight A T T B x k) := by
  induction x using TensorProduct.inductionOn with
  | tmul t b => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end AlgHom
