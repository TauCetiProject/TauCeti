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
Finally, let `s : B k →ₐ[A] A` be an `A`-algebra map from one factor `B k` of a finite product
`∀ k, B k` of `A`-algebras back to the base `A`; it splits the structure map `A → B k` (so, when
`A` and `B k` are commutative rings, it gives a section of `Spec (B k) → Spec A`). Base-changing
the composite of `s` with the projection onto `B k` agrees with applying Mathlib's
`Algebra.TensorProduct.piRight` decomposition, projecting to coordinate `k`, and then applying the
base change of `s` (`AlgHom.sectionBaseChange_comp_evalAlgHom`).

For a finite family the left distribution is `piLeft`.

## Main declarations

* `Algebra.TensorProduct.prodLeft`: the algebra equivalence above.
* `Algebra.TensorProduct.piScalarRight_symm_single`: the inverse of Mathlib's
  `Algebra.TensorProduct.piScalarRight` on `Pi.single i x`.
* `Algebra.TensorProduct.piLeft`: `(∀ i, A i) ⊗[R] B ≃ₐ[R] ∀ i, A i ⊗[R] B` for finite `ι`.
* `AlgHom.sectionBaseChange_comp_evalAlgHom`: the base change of an `A`-algebra map
  `s : B k →ₐ[A] A`, composed with the projection onto `B k`, through Mathlib's
  `Algebra.TensorProduct.piRight`.
-/

public section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable (R S A₁ A₂ B : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [Semiring A₁]
  [Semiring A₂] [Semiring B] [Algebra R A₁] [Algebra S A₁] [IsScalarTower R S A₁] [Algebra R A₂]
  [Algebra S A₂] [IsScalarTower R S A₂] [Algebra R B]

/-- The tensor product of algebras distributes over a product in the left factor:
`(A₁ × A₂) ⊗[R] B ≃ₐ[S] (A₁ ⊗[R] B) × (A₂ ⊗[R] B)`, linear over an `R`-algebra `S` whose algebra
structures on `A₁` and `A₂` restrict to their given `R`-algebra structures. -/
def prodLeft : (A₁ × A₂) ⊗[R] B ≃ₐ[S] (A₁ ⊗[R] B) × (A₂ ⊗[R] B) :=
  algEquivOfLinearEquivTensorProduct
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
  rw [prodLeft, algEquivOfLinearEquivTensorProduct_apply, _root_.TensorProduct.prodLeft_tmul]

/-- The first component of `prodLeft z` is the tensor product of the first projection
`A₁ × A₂ → A₁` with the identity on `B`, applied to `z`. -/
@[simp]
theorem prodLeft_apply_fst (z : (A₁ × A₂) ⊗[R] B) :
    (prodLeft R S A₁ A₂ B z).1 = map (AlgHom.fst S A₁ A₂) (AlgHom.id R B) z := by
  induction z using _root_.TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

/-- The second component of `prodLeft z` is the tensor product of the second projection
`A₁ × A₂ → A₂` with the identity on `B`, applied to `z`. -/
@[simp]
theorem prodLeft_apply_snd (z : (A₁ × A₂) ⊗[R] B) :
    (prodLeft R S A₁ A₂ B z).2 = map (AlgHom.snd S A₁ A₂) (AlgHom.id R B) z := by
  induction z using _root_.TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

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
    (piScalarRight R S A ι).symm (Pi.single i x) = x ⊗ₜ Pi.single i 1 := by
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

/-- The inverse of `piLeft` sends `Pi.single i (a ⊗ₜ b)` to `Pi.single i a ⊗ₜ b`. -/
@[simp]
theorem piLeft_symm_single (i : ι) (a : A i) (b : B) :
    (piLeft R A B).symm (Pi.single i (a ⊗ₜ b)) = Pi.single i a ⊗ₜ b := by
  rw [AlgEquiv.symm_apply_eq, piLeft_tmul]
  ext j
  exact (Pi.apply_single (fun j (x : A j) ↦ x ⊗ₜ[R] b)
    (fun _ ↦ _root_.TensorProduct.zero_tmul _ _) i a j).symm

/-- The `i`-th coordinate of `piLeft R A B x` is the image of `x` under the coordinate projection
`∀ i, A i → A i` tensored with the identity of `B`. -/
@[simp]
theorem piLeft_apply (x : (∀ i, A i) ⊗[R] B) (i : ι) :
    piLeft R A B x i = map (Pi.evalAlgHom R A i) (AlgHom.id R B) x := by
  induction x with
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

/-- The inverse of `piLeft` sends `Pi.single i x` to the image of `x` under the inclusion
`A i → ∀ i, A i` tensored with the identity of `B`. -/
theorem piLeft_symm_single_eq_map (i : ι) (x : A i ⊗[R] B) :
    (piLeft R A B).symm (Pi.single i x) =
      _root_.TensorProduct.map (LinearMap.single R A i) LinearMap.id x := by
  induction x with
  | tmul a b => simp
  | add x y hx hy => simp [Pi.single_add, hx, hy]

end piLeft

end Algebra.TensorProduct

namespace AlgHom

/-- For an `A`-algebra map `s : B k →ₐ[A] A` from one factor of a finite product back to the
base `A` (it splits the structure map `A → B k`; when `A` and `B k` are commutative rings, it gives
a section of `Spec (B k) → Spec A`), the base change to `T` of `s` composed with the projection
`Pi.evalAlgHom A B k` is Mathlib's `Algebra.TensorProduct.piRight`, followed by the projection to
coordinate `k` and the base change of `s`. -/
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
