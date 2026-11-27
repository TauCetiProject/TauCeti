/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import TauCeti.RingTheory.PolynomialLaw.Determinant
public import TauCeti.RingTheory.PolynomialLaw.Kernel

/-!
# Determinants of triangular representations are not faithful

Let `ρ : R →ₐ[A] Matrix n n A` be a matrix representation with upper-triangular image, for a
linear order on `n`. After every scalar extension `S`, the matrices `ρ_S(m)` are again upper
triangular, so their determinant is the product of the diagonal entries. Adding `b ⊗ x` for an
element `x` with `ρ x` zero on the diagonal does not change any diagonal entry, so such an `x`
lies in the kernel of the determinant law `det ∘ ρ`
(`TauCeti.Determinant.mem_ker_algHomDet_of_isUpperTriangular`). In particular the determinant on
the upper-triangular matrices kills the strictly upper-triangular ones, so it is not faithful
when `card n ≥ 2` and `A` is nontrivial.

## Main declarations

* `TauCeti.Determinant.isUpperTriangular_matrixBaseChangeAlgEquiv_map`: an upper-triangular
  representation stays upper triangular after every scalar extension.
* `TauCeti.Determinant.mem_ker_algHomDet_of_isUpperTriangular`: an element whose image is zero on
  the diagonal lies in the kernel of `det ∘ ρ`.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, §1.17](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

universe u

open TensorProduct

namespace TauCeti.Determinant

variable {A : Type u} [CommRing A] {R : Type*} [Semiring R] [Algebra A R] {n : Type*} [Fintype n]
  [DecidableEq n] [LinearOrder n]

/-- If a matrix representation `ρ` has upper-triangular image, so does its extension to every
commutative `A`-algebra `S`. -/
theorem isUpperTriangular_matrixBaseChangeAlgEquiv_map (ρ : R →ₐ[A] Matrix n n A)
    (hρ : ∀ x, (ρ x).IsUpperTriangular) (S : Type*) [CommSemiring S] [Algebra A S]
    (m : S ⊗[A] R) :
    (TauCeti.Algebra.matrixBaseChangeAlgEquiv A S n
      (Algebra.TensorProduct.map (AlgHom.id A S) ρ m)).IsUpperTriangular := by
  induction m using TensorProduct.inductionOn with
  | tmul s x =>
    intro i j hij
    simp [hρ x hij]
  | add y z hy hz => simpa using hy.add hz

/-- **The determinant of an upper-triangular representation is not faithful.** If `ρ` has
upper-triangular image and `ρ x` is zero on the diagonal, then `x` lies in the kernel of the
determinant law `det ∘ ρ`: after every scalar extension, adding `b ⊗ x` changes no diagonal entry
of an upper-triangular matrix, hence not its determinant. -/
theorem mem_ker_algHomDet_of_isUpperTriangular (ρ : R →ₐ[A] Matrix n n A)
    (hρ : ∀ x, (ρ x).IsUpperTriangular) {x : R} (hx : ∀ i, ρ x i i = 0) :
    x ∈ (algHomDet ρ).toLaw.ker := by
  refine PolynomialLaw.mem_ker.2 fun S _ _ b m ↦ ?_
  let : CommRing S := (algebraMap A S).commSemiringToCommRing
  rw [PolynomialLaw.toFun'_eq_toFun, algHomDet_toFun,
    algHomDet_toFun, Matrix.det_of_isUpperTriangular
      (isUpperTriangular_matrixBaseChangeAlgEquiv_map ρ hρ S _),
    Matrix.det_of_isUpperTriangular (isUpperTriangular_matrixBaseChangeAlgEquiv_map ρ hρ S _)]
  congr 2
  funext i
  simp [hx i]

end TauCeti.Determinant
