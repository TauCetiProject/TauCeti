/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.RingTheory.Norm.Defs
public import TauCeti.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Complex.Conjugation
import TauCeti.RingTheory.NormTrace.Prod

/-!
# Complexifying a complex algebra over the reals

For a complex algebra `A` with a compatible real algebra structure, the real tensor product
`ℂ ⊗[ℝ] A` splits as a product: the real algebra map

`ℂ ⊗[ℝ] A → A × A`, `a ⊗ x ↦ (a • x, conj a • x)`

is an isomorphism (`TauCeti.complexTensorProductEquivProd`). Its components are the
multiplication map and its twist by complex conjugation. For `A = ℂ` this is the splitting of the
étale `ℝ`-algebra `ℂ` over `ℂ` along its two points `id` and `conj`; on points of the Weil
restriction `Res_{ℂ/ℝ} 𝔾ₘ` it gives the splitting of the Deligne torus over `ℂ`. The splitting is
natural in `A` (`TauCeti.complexTensorProductEquivProd_lTensor`), and for `A = ℂ` conjugation of
the second factor exchanges the two components up to conjugation
(`TauCeti.complexTensorProductEquivProd_lTensor_conjAe`).

When `A` is commutative, commuting the tensor factors gives the `A`-algebra isomorphism
`A ⊗[ℝ] ℂ ≃ₐ[A] A × A` (`TauCeti.tensorProductComplexAlgEquiv`), so the `A`-algebra norm of an
element of `A ⊗[ℝ] ℂ` is the product of its two components (`TauCeti.norm_tensorProduct_complex`).

In particular, for nontrivial `A` the tensor product `ℂ ⊗[ℝ] A` has zero divisors. Explicit
factors are `I ⊗ 1 - 1 ⊗ I` and `I ⊗ 1 + 1 ⊗ I`, where the second occurrence of `I` is mapped into
`A`. So extending real scalars to `ℂ` never yields a domain when the algebra already contains `ℂ`.
This is distinct from the nonreduced tensor products caused by inseparability.
-/

public section

open TensorProduct

namespace TauCeti

-- Use the given real algebra's module rather than restriction of the complex module.
attribute [local instance high] Algebra.toModule

/-- Complexifying a nontrivial complex algebra over the reals produces two nonzero elements
whose product is zero. The factors are `I ⊗ 1 - 1 ⊗ I` and `I ⊗ 1 + 1 ⊗ I`. -/
theorem exists_ne_zero_mul_eq_zero_complex_tensorProduct (A : Type*) [Ring A]
    [Nontrivial A] [Algebra ℝ A] [Algebra ℂ A] [IsScalarTower ℝ ℂ A] :
    ∃ x y : ℂ ⊗[ℝ] A, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0 := by
  -- Tensor multiplication and Mathlib's `Complex.conjAe` detect the nonvanishing
  -- of the two factors.
  let μ : ℂ ⊗[ℝ] A →ₐ[ℝ] A := Algebra.TensorProduct.mulLeft.restrictScalars ℝ
  let ν : ℂ ⊗[ℝ] A →ₐ[ℝ] A :=
    μ.comp (Algebra.TensorProduct.map Complex.conjAe.toAlgHom (AlgHom.id ℝ A))
  let a : ℂ ⊗[ℝ] A := Complex.I ⊗ₜ[ℝ] (1 : A)
  let b : ℂ ⊗[ℝ] A := (1 : ℂ) ⊗ₜ[ℝ] algebraMap ℂ A Complex.I
  have htwoI : (2 : A) * algebraMap ℂ A Complex.I ≠ 0 := by
    rw [← map_ofNat (algebraMap ℂ A) 2, ← map_mul]
    exact (map_ne_zero (algebraMap ℂ A)).mpr (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hminus : a - b ≠ 0 := by
    intro h
    have : -algebraMap ℂ A Complex.I - algebraMap ℂ A Complex.I = 0 := by
      simpa [ν, μ, a, b, Complex.conjAe_coe] using congrArg ν h
    apply htwoI
    simpa [two_mul, sub_eq_add_neg] using congrArg Neg.neg this
  have hplus : a + b ≠ 0 := by
    intro h
    have : algebraMap ℂ A Complex.I + algebraMap ℂ A Complex.I = 0 := by
      simpa [μ, a, b] using congrArg μ h
    apply htwoI
    simpa [two_mul] using this
  refine ⟨a - b, a + b, hminus, hplus, ?_⟩
  have ha : a * a = -1 := by
    simp [a, Complex.I_mul_I, neg_tmul, ← Algebra.TensorProduct.one_def]
  have hb : b * b = -1 := by
    simp [b, ← map_mul, Complex.I_mul_I, tmul_neg, ← Algebra.TensorProduct.one_def]
  have hab : Commute a b := (Commute.one_right _).tmul (Commute.one_left _)
  calc
    (a - b) * (a + b) = a * a - b * b := hab.mul_self_sub_mul_self_eq'.symm
    _ = 0 := by rw [ha, hb, sub_self]

/-- A nontrivial complex algebra does not become a domain when tensored with `ℂ` over `ℝ`. -/
theorem not_isDomain_complex_tensorProduct (A : Type*) [Ring A] [Nontrivial A]
    [Algebra ℝ A] [Algebra ℂ A] [IsScalarTower ℝ ℂ A] : ¬ IsDomain (ℂ ⊗[ℝ] A) := by
  intro h
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_ne_zero_mul_eq_zero_complex_tensorProduct A
  exact (mul_eq_zero.mp hxy).elim hx hy

/-! ### The splitting of `ℂ ⊗[ℝ] A` -/

section Splitting

variable (A : Type*) [Ring A] [Algebra ℝ A] [Algebra ℂ A] [IsScalarTower ℝ ℂ A]

/-- The real algebra map `ℂ ⊗[ℝ] A → A × A`, `a ⊗ x ↦ (a • x, conj a • x)`, underlying
`TauCeti.complexTensorProductEquivProd`. -/
private noncomputable def complexTensorProductToProd : ℂ ⊗[ℝ] A →ₐ[ℝ] A × A :=
  (Algebra.TensorProduct.mulLeft.restrictScalars ℝ).prod
    ((Algebra.TensorProduct.mulLeft.restrictScalars ℝ).comp
      (Algebra.TensorProduct.map Complex.conjAe.toAlgHom (AlgHom.id ℝ A)))

private theorem complexTensorProductToProd_tmul (a : ℂ) (x : A) :
    complexTensorProductToProd A (a ⊗ₜ x) = (a • x, (starRingEnd ℂ a) • x) := by
  simp [complexTensorProductToProd, Algebra.smul_def, Complex.conjAe_coe]

/-- The inverse of `complexTensorProductToProd`, `(u, v) ↦ 1 ⊗ (u + v) / 2 + I ⊗ (u - v) / 2i`. -/
private noncomputable def prodToComplexTensorProduct (p : A × A) : ℂ ⊗[ℝ] A :=
  1 ⊗ₜ ((1 / 2 : ℂ) • (p.1 + p.2)) + Complex.I ⊗ₜ ((-Complex.I / 2) • (p.1 - p.2))

private theorem prodToComplexTensorProduct_complexTensorProductToProd (t : ℂ ⊗[ℝ] A) :
    prodToComplexTensorProduct A (complexTensorProductToProd A t) = t := by
  obtain ⟨x, y, rfl⟩ := exists_one_tmul_add_I_tmul t
  simp only [map_add, complexTensorProductToProd_tmul, prodToComplexTensorProduct, Prod.fst_add,
    Prod.snd_add, map_one, Complex.conj_I, one_smul]
  congr 2
  · match_scalars <;> ring
  · match_scalars
    · ring
    · linear_combination -Complex.I_sq

private theorem complexTensorProductToProd_prodToComplexTensorProduct (p : A × A) :
    complexTensorProductToProd A (prodToComplexTensorProduct A p) = p := by
  simp only [prodToComplexTensorProduct, map_add, complexTensorProductToProd_tmul, map_one,
    Complex.conj_I, one_smul]
  ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> match_scalars
  · linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  · linear_combination (1 / 2 : ℂ) * Complex.I_sq
  · linear_combination (1 / 2 : ℂ) * Complex.I_sq
  · linear_combination (-1 / 2 : ℂ) * Complex.I_sq

/-- **The splitting of `ℂ ⊗[ℝ] A`.** For a complex algebra `A`, the real algebra map
`ℂ ⊗[ℝ] A → A × A`, `a ⊗ x ↦ (a • x, conj a • x)`, is an isomorphism. Its two components are the
multiplication map and its twist by complex conjugation; for `A = ℂ` they are the two points
`id, conj : ℂ → ℂ` of the étale `ℝ`-algebra `ℂ`. -/
noncomputable def complexTensorProductEquivProd : ℂ ⊗[ℝ] A ≃ₐ[ℝ] A × A :=
  { complexTensorProductToProd A with
    invFun := prodToComplexTensorProduct A
    left_inv := prodToComplexTensorProduct_complexTensorProductToProd A
    right_inv := complexTensorProductToProd_prodToComplexTensorProduct A }

variable {A}

@[simp]
theorem complexTensorProductEquivProd_tmul (a : ℂ) (x : A) :
    complexTensorProductEquivProd A (a ⊗ₜ x) = (a • x, (starRingEnd ℂ a) • x) :=
  complexTensorProductToProd_tmul A a x

/-- The inverse of the splitting is `(u, v) ↦ 1 ⊗ (u + v) / 2 + I ⊗ (u - v) / 2i`. -/
theorem complexTensorProductEquivProd_symm_apply (p : A × A) :
    (complexTensorProductEquivProd A).symm p =
      1 ⊗ₜ ((1 / 2 : ℂ) • (p.1 + p.2)) + Complex.I ⊗ₜ ((-Complex.I / 2) • (p.1 - p.2)) :=
  (rfl)

/-- **Naturality of the splitting**: for a complex algebra map `h : A → B`, the splitting of
`ℂ ⊗[ℝ] B` after `ℂ ⊗ h` is `h` applied to both components of the splitting of `ℂ ⊗[ℝ] A`. -/
theorem complexTensorProductEquivProd_lTensor {B : Type*} [Ring B] [Algebra ℝ B] [Algebra ℂ B]
    [IsScalarTower ℝ ℂ B] (h : A →ₐ[ℂ] B) (t : ℂ ⊗[ℝ] A) :
    complexTensorProductEquivProd B
        (Algebra.TensorProduct.lTensor (S := ℂ) ℂ (h.restrictScalars ℝ) t) =
      (h (complexTensorProductEquivProd A t).1, h (complexTensorProductEquivProd A t).2) := by
  induction t using TensorProduct.inductionOn with
  | tmul a x => simp
  | add t u ht hu => simp only [map_add, ht, hu, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

/-- **Complex conjugation exchanges the two components**: on `ℂ ⊗[ℝ] ℂ`, conjugating the second
factor turns a pair `(u, v)` into `(conj v, conj u)`. -/
theorem complexTensorProductEquivProd_lTensor_conjAe (t : ℂ ⊗[ℝ] ℂ) :
    complexTensorProductEquivProd ℂ
        (Algebra.TensorProduct.lTensor (S := ℂ) ℂ Complex.conjAe.toAlgHom t) =
      (starRingEnd ℂ (complexTensorProductEquivProd ℂ t).2,
        starRingEnd ℂ (complexTensorProductEquivProd ℂ t).1) := by
  induction t using TensorProduct.inductionOn with
  | tmul a x => simp [Complex.conjAe_coe, mul_comm]
  | add t u ht hu => simp only [map_add, ht, hu, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

end Splitting

section CommRing

variable (A : Type*) [CommRing A] [Algebra ℝ A] [Algebra ℂ A] [IsScalarTower ℝ ℂ A]

/-- **Splitting of `A ⊗[ℝ] ℂ` as an `A`-algebra.** For a commutative complex algebra `A` with a
compatible real algebra structure, `A ⊗[ℝ] ℂ ≃ₐ[A] A × A` sends `a ⊗ z` to
`(a * algebraMap ℂ A z, a * algebraMap ℂ A (starRingEnd ℂ z))`. -/
noncomputable def tensorProductComplexAlgEquiv : A ⊗[ℝ] ℂ ≃ₐ[A] A × A :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.comm ℝ A ℂ).toRingEquiv.trans
      (complexTensorProductEquivProd A).toRingEquiv)
    fun a ↦ by
      rw [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_toRingEquiv,
        Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.comm_tmul,
        complexTensorProductEquivProd_tmul]
      simp [Algebra.smul_def]

variable {A}

/-- Applying `tensorProductComplexAlgEquiv A` commutes the tensor factors `A ⊗[ℝ] ℂ` to `ℂ ⊗[ℝ] A`
and applies `TauCeti.complexTensorProductEquivProd A`. -/
theorem tensorProductComplexAlgEquiv_apply (x : A ⊗[ℝ] ℂ) :
    tensorProductComplexAlgEquiv A x =
      complexTensorProductEquivProd A (Algebra.TensorProduct.comm ℝ A ℂ x) :=
  (rfl)

/-- On a pure tensor `a ⊗ₜ z`, `tensorProductComplexAlgEquiv A` evaluates to the pair
`(a * algebraMap ℂ A z, a * algebraMap ℂ A (conj z))`. -/
@[simp]
theorem tensorProductComplexAlgEquiv_tmul (a : A) (z : ℂ) :
    tensorProductComplexAlgEquiv A (a ⊗ₜ[ℝ] z) =
      (a * algebraMap ℂ A z, a * algebraMap ℂ A (starRingEnd ℂ z)) := by
  simp [tensorProductComplexAlgEquiv_apply, Algebra.smul_def, mul_comm]

/-- **The `A`-algebra norm on `A ⊗[ℝ] ℂ` is the product of the two components.** -/
theorem norm_tensorProduct_complex (x : A ⊗[ℝ] ℂ) :
    Algebra.norm A x =
      (tensorProductComplexAlgEquiv A x).1 * (tensorProductComplexAlgEquiv A x).2 := by
  rw [← Algebra.norm_eq_of_algEquiv (tensorProductComplexAlgEquiv A), Algebra.norm_prod,
    Algebra.norm_self, MonoidHom.id_apply, MonoidHom.id_apply]

end CommRing

end TauCeti

