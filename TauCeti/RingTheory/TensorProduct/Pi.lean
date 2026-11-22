/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.TensorProduct.Pi
public import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Tensor products of algebras and products

Mathlib's `Algebra.TensorProduct.prodRight` distributes `A ⊗[R] (B × C)` over the product in the
right factor. This file gives the algebra equivalence for a product in the left factor,
`(A₁ × A₂) ⊗[R] B ≃ₐ[R] (A₁ ⊗[R] B) × (A₂ ⊗[R] B)`: the algebra form of Mathlib's linear
`TensorProduct.prodLeft`. It also evaluates the inverse of Mathlib's
`Algebra.TensorProduct.piScalarRight : A ⊗[R] (ι → R) ≃ₐ[S] (ι → A)` on `Pi.single i x`, so that
`simp` computes the matrix entries of a base change of an algebra map between function algebras.
Base-changing a section factoring through a coordinate projection commutes with the same
product decomposition (`AlgHom.sectionBaseChange_comp_evalAlgHom`).

For a finite family the left distribution is `piLeft`. Matrix splittings
`A i ⊗[R] B ≃ₐ[A i] Matrix n n (A i)` of the factors assemble into one splitting
`(∀ i, A i) ⊗[R] B ≃ₐ[∀ i, A i] Matrix n n (∀ i, A i)` over the product
(`Algebra.TensorProduct.piLeftMatrixEquiv`).
This is how a split algebra over finitely many affine charts becomes split over one faithfully
flat algebra, as in `IsAzumaya.etale_matrix_splitting_of_finite_cover`.

## Main declarations

* `TauCeti.Algebra.TensorProduct.prodLeft`: the algebra equivalence above.
* `TauCeti.Algebra.TensorProduct.piScalarRight_symm_single`: the inverse of Mathlib's
  `Algebra.TensorProduct.piScalarRight` on `Pi.single i x`.
* `TauCeti.Algebra.TensorProduct.piLeft`: `(∀ i, A i) ⊗[R] B ≃ₐ[R] ∀ i, A i ⊗[R] B` for finite `ι`.
* `Algebra.TensorProduct.piLeftMatrixEquiv`: matrix splittings of the factors give a
  matrix splitting over the product.
-/

public section

open scoped TensorProduct

namespace TauCeti.Algebra.TensorProduct

variable (R A₁ A₂ B : Type*) [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring B]
  [Algebra R A₁] [Algebra R A₂] [Algebra R B]

/-- The tensor product of algebras distributes over a product in the left factor:
`(A₁ × A₂) ⊗[R] B ≃ₐ[R] (A₁ ⊗[R] B) × (A₂ ⊗[R] B)`. -/
def prodLeft : (A₁ × A₂) ⊗[R] B ≃ₐ[R] (A₁ ⊗[R] B) × (A₂ ⊗[R] B) :=
  (Algebra.TensorProduct.comm R _ _).trans <|
    (Algebra.TensorProduct.prodRight R R B A₁ A₂).trans <|
    AlgEquiv.prodCongr (Algebra.TensorProduct.comm R B A₁) (Algebra.TensorProduct.comm R B A₂)

variable {R A₁ A₂ B}

/-- `prodLeft` sends a pure tensor `(a₁, a₂) ⊗ₜ b` to the pair `(a₁ ⊗ₜ b, a₂ ⊗ₜ b)`. -/
@[simp]
theorem prodLeft_tmul (a₁ : A₁) (a₂ : A₂) (b : B) :
    prodLeft R A₁ A₂ B ((a₁, a₂) ⊗ₜ b) = (a₁ ⊗ₜ b, a₂ ⊗ₜ b) := by
  simp only [prodLeft, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.prodRight_tmul, AlgEquiv.prodCongr_apply, Equiv.prodCongr_apply,
    EquivLike.coe_coe, Prod.map_apply]

/-- The inverse of `prodLeft` sends `(a₁ ⊗ₜ b, a₂ ⊗ₜ b)` to `(a₁, a₂) ⊗ₜ b`. -/
@[simp]
theorem prodLeft_symm_tmul (a₁ : A₁) (a₂ : A₂) (b : B) :
    (prodLeft R A₁ A₂ B).symm (a₁ ⊗ₜ b, a₂ ⊗ₜ b) = (a₁, a₂) ⊗ₜ b :=
  (AlgEquiv.symm_apply_eq _).2 (prodLeft_tmul a₁ a₂ b).symm

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

section piLeft

variable (R : Type*) {ι : Type*} (A : ι → Type*) (B : Type*) [CommSemiring R]
  [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] [Semiring B] [Algebra R B]
  [Fintype ι] [DecidableEq ι]

/-- The tensor product of algebras distributes over a finite product in the left factor:
`(∀ i, A i) ⊗[R] B ≃ₐ[R] ∀ i, A i ⊗[R] B`. This is the algebra form of Mathlib's linear
`TensorProduct.piLeft`, and the left counterpart of `Algebra.TensorProduct.piRight`. -/
def piLeft : (∀ i, A i) ⊗[R] B ≃ₐ[R] ∀ i, A i ⊗[R] B :=
  (Algebra.TensorProduct.comm R _ _).trans <| (Algebra.TensorProduct.piRight R R B A).trans <|
    AlgEquiv.piCongrRight fun i ↦ Algebra.TensorProduct.comm R B (A i)

variable {R A B}

/-- `piLeft` sends a pure tensor `a ⊗ₜ b` to the family `fun i ↦ a i ⊗ₜ b`. -/
@[simp]
theorem piLeft_tmul (a : ∀ i, A i) (b : B) :
    piLeft R A B (a ⊗ₜ b) = fun i ↦ a i ⊗ₜ b := by
  ext i
  simp [piLeft]

/-- The inverse of `piLeft` sends `fun i ↦ a i ⊗ₜ b` to `a ⊗ₜ b`. -/
@[simp]
theorem piLeft_symm_tmul (a : ∀ i, A i) (b : B) :
    (piLeft R A B).symm (fun i ↦ a i ⊗ₜ b) = a ⊗ₜ b :=
  (AlgEquiv.symm_apply_eq _).2 (piLeft_tmul a b).symm

end piLeft

section piLeftMatrixEquiv

variable {R : Type*} {ι : Type*} {A : ι → Type*} {B : Type*} [CommSemiring R]
  [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)] [Semiring B] [Algebra R B]
  [Fintype ι] [DecidableEq ι] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Matrix splittings over the factors of a finite product assemble to one over the product.**
Given `A i`-algebra isomorphisms `A i ⊗[R] B ≃ₐ[A i] Matrix n n (A i)`, this is the
`(∀ i, A i)`-algebra isomorphism `(∀ i, A i) ⊗[R] B ≃ₐ[∀ i, A i] Matrix n n (∀ i, A i)`
whose entry `(j, k)` in coordinate `i` is that of `e i` (`piLeftMatrixEquiv_apply`). -/
def _root_.Algebra.TensorProduct.piLeftMatrixEquiv (e : ∀ i, A i ⊗[R] B ≃ₐ[A i] Matrix n n (A i)) :
    (∀ i, A i) ⊗[R] B ≃ₐ[∀ i, A i] Matrix n n (∀ i, A i) :=
  AlgEquiv.ofRingEquiv (f := ((TauCeti.Algebra.TensorProduct.piLeft R A B).toRingEquiv.trans
      (RingEquiv.piCongrRight fun i ↦ (e i).toRingEquiv)).trans Matrix.piRingEquiv.symm)
    fun a ↦ by
      ext j k i
      have h := (e i).commutes (a i)
      simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply] at h
      simp [Algebra.TensorProduct.algebraMap_apply, h, Matrix.algebraMap_matrix_apply,
        apply_ite (fun f : ∀ i, A i ↦ f i)]

/-- Entry `(j, k)` of `piLeftMatrixEquiv e x` in coordinate `i` is entry `(j, k)` of the image
under `e i` of the `i`-th component of `x`. -/
theorem _root_.Algebra.TensorProduct.piLeftMatrixEquiv_apply
    (e : ∀ i, A i ⊗[R] B ≃ₐ[A i] Matrix n n (A i)) (x : (∀ i, A i) ⊗[R] B) (j k : n) (i : ι) :
    Algebra.TensorProduct.piLeftMatrixEquiv e x j k i =
      e i (TauCeti.Algebra.TensorProduct.piLeft R A B x i) j k := by
  simp [Algebra.TensorProduct.piLeftMatrixEquiv]

end piLeftMatrixEquiv

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
