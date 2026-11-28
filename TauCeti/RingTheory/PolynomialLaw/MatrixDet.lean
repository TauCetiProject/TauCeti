/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.Algebra.Matrix.BaseChange
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut
public import TauCeti.RingTheory.PolynomialLaw.Basic
public import TauCeti.RingTheory.PolynomialLaw.Homogeneous
public import TauCeti.RingTheory.PolynomialLaw.Multiplicative

/-!
# The determinant polynomial law

For a commutative ring `A`, the determinant of `n × n` matrices is a polynomial law
`PolynomialLaw.det n A : Matrix n n A →ₚₗ[A] A`. After scalar extension to a commutative `A`-algebra
`S`, it is the determinant over `S`, read through the identification
`S ⊗[A] Matrix n n A ≃ Matrix n n S` (`TauCeti.Algebra.matrixBaseChangeAlgEquiv`). This law is
homogeneous of degree `card n` and multiplicative, and it is invariant under conjugation by an
invertible matrix. Composed with an algebra map `R → Matrix n n A`, it gives the determinant of a
matrix representation in the sense of Chenevier (`TauCeti.Determinant.algHomDet`).

## Main declarations

* `PolynomialLaw.det`: the determinant of `n × n` matrices as a polynomial law.
* `PolynomialLaw.det_toFun`, `PolynomialLaw.ground_det`: after scalar extension to a commutative
  ring `S`, it is the determinant over `S`; its ground map is `Matrix.det`.
* `PolynomialLaw.det_toFun_eq_leibniz`: after scalar extension to any commutative `A`-algebra `S`,
  it is the Leibniz formula with the signs acting through `A`.
* `PolynomialLaw.isHomogeneousOfDegree_det`, `PolynomialLaw.isMultiplicative_det`: it is
  homogeneous of degree `card n` and multiplicative.
* `PolynomialLaw.det_comp_innerAut`: it is invariant under conjugation by an invertible matrix.

## Implementation notes

A polynomial law has a component at every commutative `A`-algebra `S`, but `Matrix.det` needs `S`
to be a ring. Since `A` is a ring, every commutative `A`-algebra is one, so the component is given
by the Leibniz formula with the signs acting through `A`; on commutative rings this is
`Matrix.det`, and multiplicativity is checked on `S` with the ring structure induced by
`algebraMap A S`.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, §1.5](https://arxiv.org/abs/0809.0415)
-/

public noncomputable section

open TensorProduct Equiv TauCeti.Algebra

universe u

namespace PolynomialLaw

variable (n : Type*) [Fintype n] [DecidableEq n] (A : Type u) [CommRing A]

section Leibniz

variable {n} {S S' : Type*} [CommSemiring S] [Algebra A S] [CommSemiring S'] [Algebra A S']

/-- The Leibniz formula `∑_σ sign σ ∏ᵢ M (σ i) i` for a matrix over a commutative `A`-algebra, with
the signs acting through `A`. -/
private def leibniz (M : Matrix n n S) : S :=
  ∑ σ : Perm n, ((Perm.sign σ : ℤ) : A) • ∏ i, M (σ i) i

private theorem leibniz_eq_det {S : Type*} [CommRing S] [Algebra A S] (M : Matrix n n S) :
    leibniz A M = M.det := by
  rw [leibniz, Matrix.det_apply']
  exact Finset.sum_congr rfl fun σ _ ↦ by rw [Algebra.smul_def, map_intCast]

private theorem map_leibniz (φ : S →ₐ[A] S') (M : Matrix n n S) :
    φ (leibniz A M) = leibniz A (M.map φ) := by
  simp [leibniz, map_sum, map_prod]

private theorem leibniz_smul (s : S) (M : Matrix n n S) :
    leibniz A (s • M) = s ^ Fintype.card n * leibniz A M := by
  simp only [leibniz, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Finset.mul_sum, mul_smul_comm]

private theorem leibniz_one : leibniz A (1 : Matrix n n S) = 1 := by
  let : CommRing S := (algebraMap A S).commSemiringToCommRing
  rw [leibniz_eq_det, Matrix.det_one]

private theorem leibniz_mul (M N : Matrix n n S) :
    leibniz A (M * N) = leibniz A M * leibniz A N := by
  let : CommRing S := (algebraMap A S).commSemiringToCommRing
  rw [leibniz_eq_det, leibniz_eq_det, leibniz_eq_det, Matrix.det_mul]

private theorem leibniz_conj {G G' : Matrix n n S} (h : G * G' = 1) (M : Matrix n n S) :
    leibniz A (G * M * G') = leibniz A M := by
  let : CommRing S := (algebraMap A S).commSemiringToCommRing
  rw [leibniz_eq_det, leibniz_eq_det, Matrix.det_mul_right_comm, h, one_mul]

end Leibniz

/-- The determinant of `n × n` matrices over `A`, as a polynomial law. After scalar extension to a
commutative `A`-algebra `S`, it is the determinant of the corresponding matrix over `S`
(`PolynomialLaw.det_toFun`). -/
def det : Matrix n n A →ₚₗ[A] A where
  toFun' S _ _ x :=
    (Algebra.TensorProduct.rid A S S).symm (leibniz A (matrixBaseChangeAlgEquiv A S n x))
  isCompat' φ := funext fun x ↦ by
    simp [matrixBaseChangeAlgEquiv_rTensor, ← map_leibniz]

variable {n A}

private theorem det_toFun'_def (S : Type u) [CommSemiring S] [Algebra A S]
    (x : S ⊗[A] Matrix n n A) :
    (det n A).toFun' S x = leibniz A (matrixBaseChangeAlgEquiv A S n x) ⊗ₜ 1 :=
  (rfl)

/-- After scalar extension to any commutative `A`-algebra `S`, the determinant law is given by the
Leibniz formula for the corresponding matrix over `S`, with the signs acting through `A`. Over a
commutative ring this is `PolynomialLaw.det_toFun`. -/
theorem det_toFun_eq_leibniz (S : Type*) [CommSemiring S] [Algebra A S]
    (x : S ⊗[A] Matrix n n A) :
    (det n A).toFun S x = (∑ σ : Perm n,
      ((Perm.sign σ : ℤ) : A) • ∏ i, matrixBaseChangeAlgEquiv A S n x (σ i) i) ⊗ₜ 1 := by
  obtain ⟨k, ψ, p, rfl⟩ := exists_lift x
  rw [← isCompat_apply, ← toFun'_eq_toFun, det_toFun'_def]
  simp [matrixBaseChangeAlgEquiv_rTensor, leibniz]

/-- After scalar extension to a commutative ring `S`, the determinant law is the determinant of the
corresponding matrix over `S`. -/
@[simp]
theorem det_toFun (S : Type*) [CommRing S] [Algebra A S] (x : S ⊗[A] Matrix n n A) :
    (det n A).toFun S x = (matrixBaseChangeAlgEquiv A S n x).det ⊗ₜ 1 := by
  rw [det_toFun_eq_leibniz]
  exact congrArg (· ⊗ₜ 1) (leibniz_eq_det A _)

/-- The ground map of the determinant law is the determinant. -/
@[simp]
theorem ground_det : (det n A).ground = Matrix.det := by
  ext M
  simp [ground_apply]

/-- The determinant law of `n × n` matrices is homogeneous of degree `card n`. -/
theorem isHomogeneousOfDegree_det : (det n A).IsHomogeneousOfDegree (Fintype.card n) :=
  isHomogeneousOfDegree_iff.mpr fun S _ _ s x ↦ by
    rw [det_toFun'_def, det_toFun'_def, map_smul, leibniz_smul, ← smul_eq_mul, smul_tmul']

/-- The determinant law is multiplicative. -/
theorem isMultiplicative_det : (det n A).IsMultiplicative where
  toFun'_one S _ _ := by
    rw [det_toFun'_def, map_one, leibniz_one, Algebra.TensorProduct.one_def]
  toFun'_mul x y := by
    rw [det_toFun'_def, det_toFun'_def, det_toFun'_def, map_mul, leibniz_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The determinant law is invariant under conjugation by an invertible matrix, after every scalar
extension. -/
@[simp]
theorem det_comp_innerAut (g : GL n A) :
    (det n A).comp (Matrix.GeneralLinearGroup.innerAut g).toLinearMap.toPolynomialLaw =
      det n A := by
  ext S _ _ x
  set G : Matrix n n S := (g : Matrix n n A).map (algebraMap A S)
  set G' : Matrix n n S := ((g⁻¹ : GL n A) : Matrix n n A).map (algebraMap A S)
  have hconj : matrixBaseChangeAlgEquiv A S n
      ((Matrix.GeneralLinearGroup.innerAut g).toLinearMap.baseChange S x) =
        G * matrixBaseChangeAlgEquiv A S n x * G' := by
    induction x using TensorProduct.inductionOn with
    | tmul s M =>
      simp [G, G', Matrix.map_mul]
    | add x y hx hy => simp [hx, hy, Matrix.mul_add, Matrix.add_mul]
  have hG : G * G' = 1 := by simp [G, G', ← Matrix.map_mul]
  rw [comp_toFun', Function.comp_apply, LinearMap.toPolynomialLaw_toFun', det_toFun'_def,
    det_toFun'_def, hconj, leibniz_conj A hG]

end PolynomialLaw
