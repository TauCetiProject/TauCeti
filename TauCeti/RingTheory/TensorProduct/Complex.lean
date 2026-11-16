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
import TauCeti.RingTheory.NormTrace.Prod

/-!
# Complexifying a complex algebra over the reals

Let `A` be a ring equipped with a complex algebra structure and a compatible real algebra
structure (`[Algebra ℝ A] [Algebra ℂ A] [IsScalarTower ℝ ℂ A]`). Extending real scalars of `A` to
`ℂ` splits into two copies of `A`:

```text
ℂ ⊗[ℝ] A ≃ₐ[ℝ] A × A,   z ⊗ a ↦ (z • a, conj z • a).
```

The first factor multiplies through the given complex structure of `A`, and the second through its
conjugate complex structure. The inverse sends `(u, v)` to
`2⁻¹ • (1 ⊗ (u + v) - I ⊗ (I • (u - v)))`.

When `A` is commutative, commuting the tensor factors gives the `A`-algebra isomorphism
`A ⊗[ℝ] ℂ ≃ₐ[A] A × A` (`TauCeti.tensorProductComplexAlgEquiv`), so the `A`-algebra norm of an
element of `A ⊗[ℝ] ℂ` is the product of its two components (`TauCeti.norm_tensorProduct_complex`).
When `A` is nontrivial, the two orthogonal idempotents `(1, 0)` and `(0, 1)` witness zero divisors
in `ℂ ⊗[ℝ] A` (`TauCeti.exists_ne_zero_mul_eq_zero_complex_tensorProduct`), so `ℂ ⊗[ℝ] A` is never
a domain (`TauCeti.not_isDomain_complex_tensorProduct`).

## Main definitions

* `TauCeti.complexTensorProductEquiv`: the `ℝ`-algebra isomorphism `ℂ ⊗[ℝ] A ≃ₐ[ℝ] A × A` sending
  `z ⊗ a` to `(algebraMap ℂ A z * a, algebraMap ℂ A (starRingEnd ℂ z) * a)`.
* `TauCeti.tensorProductComplexAlgEquiv`: for commutative `A`, the `A`-algebra isomorphism
  `A ⊗[ℝ] ℂ ≃ₐ[A] A × A` sending `a ⊗ z` to
  `(a * algebraMap ℂ A z, a * algebraMap ℂ A (starRingEnd ℂ z))`.

## Main results

* `TauCeti.complexTensorProductEquiv_tmul` and `TauCeti.complexTensorProductEquiv_symm_apply`:
  explicit formulas on pure tensors and on pairs.
* `TauCeti.complexTensorProductEquiv_map_of_algHom` and
  `TauCeti.complexTensorProductEquiv_map_of_conj`: `ℂ`-algebra maps act componentwise, while
  conjugate-linear `ℝ`-algebra maps apply the map and swap the two components.
* `TauCeti.norm_tensorProduct_complex`: the `A`-algebra norm on `A ⊗[ℝ] ℂ` is the product of the
  two components.
* `TauCeti.exists_ne_zero_mul_eq_zero_complex_tensorProduct` and
  `TauCeti.not_isDomain_complex_tensorProduct`: `ℂ ⊗[ℝ] A` has zero divisors whenever `A` is
  nontrivial.
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

section Ring

variable (A : Type*) [Ring A] [Algebra ℝ A] [Algebra ℂ A] [IsScalarTower ℝ ℂ A]

/-- The forward `ℝ`-algebra homomorphism `ℂ ⊗[ℝ] A →ₐ[ℝ] A × A` sending `z ⊗ a` to
`(z • a, conj z • a)`. -/
private noncomputable def complexTensorProductHom : ℂ ⊗[ℝ] A →ₐ[ℝ] A × A :=
  let μ : ℂ ⊗[ℝ] A →ₐ[ℝ] A := Algebra.TensorProduct.mulLeft.restrictScalars ℝ
  μ.prod (μ.comp (Algebra.TensorProduct.map Complex.conjAe.toAlgHom (AlgHom.id ℝ A)))

/-- The inverse `ℝ`-linear map `A × A →ₗ[ℝ] ℂ ⊗[ℝ] A` sending `(u, v)` to
`2⁻¹ • (1 ⊗ (u + v) - I ⊗ (I • (u - v)))`. -/
private noncomputable def complexTensorProductInv : A × A →ₗ[ℝ] ℂ ⊗[ℝ] A :=
  (2⁻¹ : ℝ) •
    ((TensorProduct.mk ℝ ℂ A 1).comp (LinearMap.fst ℝ A A + LinearMap.snd ℝ A A) -
      (TensorProduct.mk ℝ ℂ A Complex.I).comp
        ((Algebra.lmul ℝ A (algebraMap ℂ A Complex.I)).comp
          (LinearMap.fst ℝ A A - LinearMap.snd ℝ A A)))

private lemma complexTensorProductHom_tmul (z : ℂ) (a : A) :
    complexTensorProductHom A (z ⊗ₜ[ℝ] a) =
      (algebraMap ℂ A z * a, algebraMap ℂ A (starRingEnd ℂ z) * a) := by
  simp [complexTensorProductHom, Complex.conjAe_coe]

omit [IsScalarTower ℝ ℂ A] in
private lemma complexTensorProductInv_apply (p : A × A) :
    complexTensorProductInv A p =
      (2⁻¹ : ℝ) • ((1 : ℂ) ⊗ₜ[ℝ] (p.1 + p.2) -
        Complex.I ⊗ₜ[ℝ] (algebraMap ℂ A Complex.I * (p.1 - p.2))) :=
  (rfl)

private lemma complexTensorProductInv_comp_hom :
    (complexTensorProductInv A).comp (complexTensorProductHom A).toLinearMap = LinearMap.id := by
  have hI2 : algebraMap ℂ A Complex.I * algebraMap ℂ A Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  refine TensorProduct.ext' fun z a ↦ ?_
  -- Decompose `z = z.re + z.im * I` so linearity reduces the check to `1` and `I`.
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simp [Complex.real_smul]
  rw [hz, add_tmul, smul_tmul, smul_tmul, tmul_smul, tmul_smul, map_add, map_smul, map_smul]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply,
    complexTensorProductHom_tmul, complexTensorProductInv_apply, map_one, one_mul, Complex.conj_I,
    map_neg, neg_mul]
  have h1 : (1 : ℂ) ⊗ₜ[ℝ] (a + a) = (2 : ℝ) • ((1 : ℂ) ⊗ₜ[ℝ] a) := by
    rw [← tmul_smul, two_smul]
  have h2 : algebraMap ℂ A Complex.I * (algebraMap ℂ A Complex.I * a -
      -(algebraMap ℂ A Complex.I * a)) = -((2 : ℝ) • a) := by
    rw [sub_neg_eq_add, ← two_smul ℝ (algebraMap ℂ A Complex.I * a), mul_smul_comm, ← mul_assoc,
      hI2, neg_one_mul, smul_neg]
  rw [sub_self, mul_zero, tmul_zero, sub_zero, h1, add_neg_cancel, tmul_zero, h2, tmul_neg,
    tmul_smul, zero_sub, neg_neg, inv_smul_smul₀ two_ne_zero, inv_smul_smul₀ two_ne_zero]

private lemma complexTensorProductHom_inv (p : A × A) :
    complexTensorProductHom A (complexTensorProductInv A p) = p := by
  have hI2 : algebraMap ℂ A Complex.I * algebraMap ℂ A Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  rcases p with ⟨u, v⟩
  rw [complexTensorProductInv_apply, AlgHom.map_smul_of_tower, map_sub,
    complexTensorProductHom_tmul, complexTensorProductHom_tmul]
  simp only [map_one, one_mul, Complex.conj_I, map_neg, neg_mul, ← mul_assoc, hI2, neg_neg]
  ext <;> dsimp
  · rw [sub_neg_eq_add, add_add_sub_cancel, ← two_smul ℝ u, inv_smul_smul₀ two_ne_zero]
  · rw [add_sub_sub_cancel, ← two_smul ℝ v, inv_smul_smul₀ two_ne_zero]

/-- **Splitting of the complexification of a complex algebra.** For every complex algebra `A` with
a compatible real algebra structure, `ℂ ⊗[ℝ] A` is isomorphic as an `ℝ`-algebra to `A × A` via
`z ⊗ a ↦ (z • a, conj z • a)`. -/
noncomputable def complexTensorProductEquiv : ℂ ⊗[ℝ] A ≃ₐ[ℝ] A × A :=
  AlgEquiv.ofLinearEquiv
    (LinearEquiv.ofLinearMap (complexTensorProductHom A).toLinearMap (complexTensorProductInv A)
      (LinearMap.ext <| complexTensorProductHom_inv A) (complexTensorProductInv_comp_hom A))
    (map_one (complexTensorProductHom A)) (map_mul (complexTensorProductHom A))

variable {A}

/-- On a pure tensor `z ⊗ a`, the components of `complexTensorProductEquiv` multiply `a` by `z` and
by `conj z` through `algebraMap ℂ A`. -/
@[simp]
theorem complexTensorProductEquiv_tmul (z : ℂ) (a : A) :
    complexTensorProductEquiv A (z ⊗ₜ[ℝ] a) =
      (algebraMap ℂ A z * a, algebraMap ℂ A (starRingEnd ℂ z) * a) :=
  complexTensorProductHom_tmul A z a

/-- The inverse of `complexTensorProductEquiv` sends `(u, v)` to
`2⁻¹ • (1 ⊗ (u + v) - I ⊗ (I • (u - v)))`. -/
theorem complexTensorProductEquiv_symm_apply (p : A × A) :
    (complexTensorProductEquiv A).symm p =
      (2⁻¹ : ℝ) • ((1 : ℂ) ⊗ₜ[ℝ] (p.1 + p.2) -
        Complex.I ⊗ₜ[ℝ] (algebraMap ℂ A Complex.I * (p.1 - p.2))) :=
  (complexTensorProductEquiv A).injective <| by
    rw [AlgEquiv.apply_symm_apply, ← complexTensorProductInv_apply]
    exact (complexTensorProductHom_inv A p).symm

/-- **Naturality of `complexTensorProductEquiv` for `ℂ`-algebra maps.** Extending a `ℂ`-algebra
homomorphism `h : A →ₐ[ℂ] B` along `ℂ ⊗[ℝ] ·` acts componentwise on `A × A`. -/
theorem complexTensorProductEquiv_map_of_algHom {B : Type*} [Ring B] [Algebra ℝ B] [Algebra ℂ B]
    [IsScalarTower ℝ ℂ B] (h : A →ₐ[ℂ] B) (x : ℂ ⊗[ℝ] A) :
    complexTensorProductEquiv B
        (Algebra.TensorProduct.map (AlgHom.id ℝ ℂ) (h.restrictScalars ℝ) x) =
      (h (complexTensorProductEquiv A x).1, h (complexTensorProductEquiv A x).2) := by
  induction x using TensorProduct.inductionOn with
  | tmul z a => simp [AlgHom.commutes]
  | add x y hx hy => ext <;> simp [map_add, hx, hy]

/-- **Conjugate-linear naturality of `complexTensorProductEquiv`.** An `ℝ`-algebra homomorphism
`h : A →ₐ[ℝ] B` that intertwines the `ℂ`-algebra structures through complex conjugation acts on
`A × A` by applying `h` to both factors and swapping them. -/
theorem complexTensorProductEquiv_map_of_conj {B : Type*} [Ring B] [Algebra ℝ B] [Algebra ℂ B]
    [IsScalarTower ℝ ℂ B] (h : A →ₐ[ℝ] B)
    (hh : ∀ z : ℂ, h (algebraMap ℂ A z) = algebraMap ℂ B (starRingEnd ℂ z)) (x : ℂ ⊗[ℝ] A) :
    complexTensorProductEquiv B (Algebra.TensorProduct.map (AlgHom.id ℝ ℂ) h x) =
      (h (complexTensorProductEquiv A x).2, h (complexTensorProductEquiv A x).1) := by
  induction x using TensorProduct.inductionOn with
  | tmul z a => simp [map_mul, hh]
  | add x y hx hy => ext <;> simp [map_add, hx, hy]

end Ring

section CommRing

variable (A : Type*) [CommRing A] [Algebra ℝ A] [Algebra ℂ A] [IsScalarTower ℝ ℂ A]

/-- **Splitting of `A ⊗[ℝ] ℂ` as an `A`-algebra.** For a commutative complex algebra `A` with a
compatible real algebra structure, `A ⊗[ℝ] ℂ ≃ₐ[A] A × A` sends `a ⊗ z` to
`(a * algebraMap ℂ A z, a * algebraMap ℂ A (starRingEnd ℂ z))`. -/
noncomputable def tensorProductComplexAlgEquiv : A ⊗[ℝ] ℂ ≃ₐ[A] A × A :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.comm ℝ A ℂ).toRingEquiv.trans
      (complexTensorProductEquiv A).toRingEquiv)
    fun a ↦ by
      rw [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_toRingEquiv,
        Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.comm_tmul,
        complexTensorProductEquiv_tmul]
      simp

variable {A}

theorem tensorProductComplexAlgEquiv_apply (x : A ⊗[ℝ] ℂ) :
    tensorProductComplexAlgEquiv A x =
      complexTensorProductEquiv A (Algebra.TensorProduct.comm ℝ A ℂ x) :=
  (rfl)

@[simp]
theorem tensorProductComplexAlgEquiv_tmul (a : A) (z : ℂ) :
    tensorProductComplexAlgEquiv A (a ⊗ₜ[ℝ] z) =
      (a * algebraMap ℂ A z, a * algebraMap ℂ A (starRingEnd ℂ z)) := by
  simp [tensorProductComplexAlgEquiv_apply, mul_comm]

/-- **The `A`-algebra norm on `A ⊗[ℝ] ℂ` is the product of the two components.** -/
theorem norm_tensorProduct_complex (x : A ⊗[ℝ] ℂ) :
    Algebra.norm A x =
      (tensorProductComplexAlgEquiv A x).1 * (tensorProductComplexAlgEquiv A x).2 := by
  rw [← Algebra.norm_eq_of_algEquiv (tensorProductComplexAlgEquiv A), Algebra.norm_prod,
    Algebra.norm_self, MonoidHom.id_apply, MonoidHom.id_apply]

end CommRing

end TauCeti

