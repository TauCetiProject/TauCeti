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
# The kernel of the determinant of a triangular representation

Let `ρ : R →ₐ[A] Matrix n n A` be a matrix representation with upper-triangular image, for a
linear order on `n`. If `ρ x` is zero on the diagonal, then `x` lies in the kernel of the
determinant law `det ∘ ρ` (`TauCeti.Determinant.mem_ker_algHomDet_of_isUpperTriangular`). In
particular the determinant on the upper-triangular matrices kills the strictly upper-triangular
ones, so it is not faithful when `card n ≥ 2` and `A` is nontrivial.

## Main declarations

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

/-- **Elements with zero diagonal lie in the determinant kernel.** If `ρ` has upper-triangular
image and `ρ x` is zero on the diagonal, then `x` lies in the kernel of the determinant law
`det ∘ ρ`: for every commutative `A`-algebra `S`, every `b : S` and every `m : S ⊗[A] R`, the
determinant of `ρ` extended to `S` takes the same value at `b ⊗ x + m` as at `m`. -/
theorem mem_ker_algHomDet_of_isUpperTriangular (ρ : R →ₐ[A] Matrix n n A)
    (hρ : ∀ x, (ρ x).IsUpperTriangular) {x : R} (hx : ∀ i, ρ x i i = 0) :
    x ∈ (algHomDet ρ).toLaw.ker := by
  refine PolynomialLaw.mem_ker.2 fun S _ _ b m ↦ ?_
  -- `mem_ker` quantifies over commutative semirings `S`, while `algHomDet_toFun` needs a
  -- commutative ring; an `A`-algebra over the ring `A` is one.
  let : CommRing S := (algebraMap A S).commSemiringToCommRing
  rw [PolynomialLaw.toFun'_eq_toFun, algHomDet_toFun, algHomDet_toFun,
    Matrix.det_of_isUpperTriangular (Algebra.blockTriangular_matrixBaseChangeAlgEquiv_map ρ hρ _),
    Matrix.det_of_isUpperTriangular (Algebra.blockTriangular_matrixBaseChangeAlgEquiv_map ρ hρ _)]
  congr 2
  funext i
  simp [hx i]

end TauCeti.Determinant
