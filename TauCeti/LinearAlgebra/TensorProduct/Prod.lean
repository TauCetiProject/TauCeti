/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Tensor products with binary products

Mathlib's `TensorProduct.prodRight` distributes a tensor product over a binary product. When the
second factor of the product is the base ring `R` itself, composing with the right unitor
`TensorProduct.AlgebraTensorModule.rid` gives the identification
`M₁ ⊗[R] (M₂ × R) ≃ (M₁ ⊗[R] M₂) × M₁`, `m₁ ⊗ (m₂, r) ↦ (m₁ ⊗ m₂, r • m₁)`. It is linear over
any `R`-algebra `S` acting on `M₁`. For `M₁ = S` this describes the scalar extension of `M₂ × R`
to `S`: adjoining one direction to `M₂` and then extending scalars adjoins one direction to the
scalar extension of `M₂`.

When the structure maps of two `R`-algebras `A` and `B` make `R → A × B` bijective, so that `R`
is the product ring `A × B`, an `A`-module and a `B`-module have trivial tensor product over `R`.
Hence every `R`-module is the product of its base changes to `A` and to `B`, and base change to
`A` of the product `P × Q` of an `A`-module and a `B`-module recovers `P` (and similarly for `B`).

## Main declarations

* `TensorProduct.prodRightRid`: the identification `M₁ ⊗[R] (M₂ × R) ≃ (M₁ ⊗[R] M₂) × M₁`.
* `TensorProduct.prodRightRid_tmul` and `TensorProduct.prodRightRid_symm_apply`: its values on
  pure tensors and its inverse.
* `TensorProduct.subsingleton_of_bijective_prod`: if `R → A × B` is bijective, then
  `P ⊗[R] Q` is trivial for an `A`-module `P` and a `B`-module `Q`.
* `TensorProduct.equivProdOfBijective`: if `R → A × B` is bijective, then
  `M ≃ (A ⊗[R] M) × (B ⊗[R] M)` for every `R`-module `M`.
* `TensorProduct.prodRightEquivFstOfBijective` and
  `TensorProduct.prodRightEquivSndOfBijective`: if `R → A × B` is bijective, then
  `A ⊗[R] (P × Q) ≃ P` and `B ⊗[R] (P × Q) ≃ Q`.
-/

public section

open scoped TensorProduct

namespace TensorProduct

variable (R S M₁ M₂ : Type*)
variable [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Module R M₁] [Module S M₁] [IsScalarTower R S M₁] [Module R M₂]

/-- The `S`-linear equivalence `M₁ ⊗[R] (M₂ × R) ≃ (M₁ ⊗[R] M₂) × M₁`,
`m₁ ⊗ (m₂, r) ↦ (m₁ ⊗ m₂, r • m₁)`, obtained from `TensorProduct.prodRight` and the right
unitor. -/
noncomputable def prodRightRid : M₁ ⊗[R] (M₂ × R) ≃ₗ[S] (M₁ ⊗[R] M₂) × M₁ :=
  prodRight R S M₁ M₂ R ≪≫ₗ (LinearEquiv.refl S _).prodCongr (AlgebraTensorModule.rid R S M₁)

variable {R S M₁ M₂}

/-- `TensorProduct.prodRightRid` sends `m₁ ⊗ (m₂, r)` to `(m₁ ⊗ m₂, r • m₁)`. -/
@[simp]
theorem prodRightRid_tmul (m₁ : M₁) (m : M₂ × R) :
    prodRightRid R S M₁ M₂ (m₁ ⊗ₜ m) = (m₁ ⊗ₜ m.1, m.2 • m₁) := by
  simp [prodRightRid]

/-- The inverse of `TensorProduct.prodRightRid` sends `(x, m₁)` to the image of `x` under the
inclusion `M₂ → M₂ × R`, plus `m₁ ⊗ (0, 1)`. -/
@[simp]
theorem prodRightRid_symm_apply (x : M₁ ⊗[R] M₂) (m₁ : M₁) :
    (prodRightRid R S M₁ M₂).symm (x, m₁) =
      (LinearMap.inl R M₂ R).lTensor M₁ x + m₁ ⊗ₜ (0, 1) := by
  simp [prodRightRid, prodRight]

section Bijective

/-! ### Tensor products over a product of rings

If the structure maps of two `R`-algebras `A` and `B` make `R → A × B` bijective, then an
`A`-module and a `B`-module have trivial tensor product over `R`, and every `R`-module is the
product of its base changes to `A` and to `B`. -/

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B] [Algebra R A]
  [Algebra R B] (h : Function.Bijective ((algebraMap R A).prod (algebraMap R B)))

include h

/-- If `R → A × B` is bijective, an `A`-module and a `B`-module have trivial tensor product
over `R`. -/
theorem subsingleton_of_bijective_prod {P Q : Type*} [AddCommMonoid P] [Module R P] [Module A P]
    [IsScalarTower R A P] [AddCommMonoid Q] [Module R Q] [Module B Q] [IsScalarTower R B Q] :
    Subsingleton (P ⊗[R] Q) := by
  obtain ⟨e, he⟩ := h.2 (1, 0)
  have hA : algebraMap R A e = 1 := congr_arg Prod.fst he
  have hB : algebraMap R B e = 0 := congr_arg Prod.snd he
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul p q =>
    rw [← one_smul A p, ← hA, algebraMap_smul, smul_tmul, ← algebraMap_smul B, hB, zero_smul,
      tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- The bijectivity hypothesis, read for the bundled `R`-linear structure maps. -/
private theorem bijective_linearMap_prod :
    Function.Bijective ((Algebra.linearMap R A).prod (Algebra.linearMap R B)) := by
  have hf : ⇑((Algebra.linearMap R A).prod (Algebra.linearMap R B)) =
      ⇑((algebraMap R A).prod (algebraMap R B)) :=
    funext fun r ↦ by simp [RingHom.prod_apply]
  rwa [hf]

variable (M : Type*) [AddCommMonoid M] [Module R M]

/-- If `R → A × B` is bijective, every `R`-module `M` is the product of its base changes to `A`
and to `B`, by `m ↦ (1 ⊗ m, 1 ⊗ m)`. -/
noncomputable def equivProdOfBijective : M ≃ₗ[R] (A ⊗[R] M) × (B ⊗[R] M) :=
  (TensorProduct.lid R M).symm ≪≫ₗ
    (LinearEquiv.ofBijective _ (bijective_linearMap_prod h)).rTensor M
    ≪≫ₗ prodLeft R R A B M

@[simp]
theorem equivProdOfBijective_apply (m : M) :
    equivProdOfBijective h M m = (1 ⊗ₜ m, 1 ⊗ₜ m) := by
  simp [equivProdOfBijective, LinearEquiv.ofBijective_apply]

variable (P Q : Type*) [AddCommMonoid P] [Module R P] [Module A P] [IsScalarTower R A P]
  [AddCommMonoid Q] [Module R Q] [Module B Q] [IsScalarTower R B Q]

/-- If `R → A × B` is bijective, the base change to `A` of the product of an `A`-module `P` and a
`B`-module `Q` is `P`. -/
noncomputable def prodRightEquivFstOfBijective : A ⊗[R] (P × Q) ≃ₗ[A] P :=
  haveI := subsingleton_of_bijective_prod h (P := A) (Q := Q)
  letI : Unique (A ⊗[R] Q) := uniqueOfSubsingleton 0
  haveI : CompatibleSMul R A A P :=
    .of_algebraMap_surjective _ _ (Prod.fst_surjective.comp h.surjective)
  prodRight R A A P Q ≪≫ₗ LinearEquiv.prodUnique ≪≫ₗ lidOfCompatibleSMul R A P

@[simp]
theorem prodRightEquivFstOfBijective_tmul (a : A) (x : P × Q) :
    prodRightEquivFstOfBijective h P Q (a ⊗ₜ x) = a • x.1 := by
  simp [prodRightEquivFstOfBijective, lidOfCompatibleSMul_tmul]

/-- If `R → A × B` is bijective, the base change to `B` of the product of an `A`-module `P` and a
`B`-module `Q` is `Q`. -/
noncomputable def prodRightEquivSndOfBijective : B ⊗[R] (P × Q) ≃ₗ[B] Q :=
  haveI := subsingleton_of_bijective_prod h (P := P) (Q := B)
  haveI : Subsingleton (B ⊗[R] P) := (TensorProduct.comm R B P).toEquiv.subsingleton
  letI : Unique (B ⊗[R] P) := uniqueOfSubsingleton 0
  haveI : CompatibleSMul R B B Q :=
    .of_algebraMap_surjective _ _ (Prod.snd_surjective.comp h.surjective)
  prodRight R B B P Q ≪≫ₗ LinearEquiv.uniqueProd ≪≫ₗ lidOfCompatibleSMul R B Q

@[simp]
theorem prodRightEquivSndOfBijective_tmul (b : B) (x : P × Q) :
    prodRightEquivSndOfBijective h P Q (b ⊗ₜ x) = b • x.2 := by
  simp [prodRightEquivSndOfBijective, lidOfCompatibleSMul_tmul]

end Bijective

end TensorProduct
