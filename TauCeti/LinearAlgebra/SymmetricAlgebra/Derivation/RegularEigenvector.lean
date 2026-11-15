/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.Jacobian

/-!
# Invariant differentials at a regular eigenvector

For an endomorphism `g` of `M`, a point of `Sym M` is a linear form `x : M → R`.
Suppose `x ∘ g = c x`, and `g` fixes homogeneous polynomials `f i` of degrees `d i`.
The chain rule makes their differentials at `x` eigenvectors with eigenvalues
`c⁻¹ ^ (d i - 1)`. If the Jacobian is nonzero at `x`, these differentials give the
whole characteristic polynomial of `g`, including multiplicities.

This is the linear-algebra step relating invariant degrees to eigenvalues at a regular
point. It does not assert existence of a regular eigenvector or identify a Coxeter element.
The coefficient ring may be any domain, and `c` is required to be a unit.

## References

* T. A. Springer, *Regular elements of finite reflection groups*, Invent. Math. 25 (1974),
  159–198, §4.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), §3.17.
-/

public section

open TauCeti.SymmetricAlgebra

namespace LinearMap

open SymmetricAlgebra Polynomial

variable {R M n : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Fintype n] [DecidableEq n] [Module.Free R M] [Module.Finite R M]

/-- Homogeneous fixed polynomials whose Jacobian is nonzero at an eigenpoint determine the
characteristic polynomial. Repeated degrees give repeated factors; the empty basis is allowed. -/
theorem charpoly_eq_prod_of_map_eq_self_of_jacobian_ne_zero (g : M →ₗ[R] M)
    (b : Module.Basis n R M) {f : n → SymmetricAlgebra R M} (d : n → ℕ)
    (hf : ∀ i, f i ∈ homogeneousSubmodule R M (d i))
    (hg : ∀ i, SymmetricAlgebra.map R g (f i) = f i)
    (x : Module.Dual R M) (c : Rˣ) (hx : x ∘ₗ g = (c : R) • x)
    (hJ : SymmetricAlgebra.lift x (jacobian b f) ≠ 0) :
    g.charpoly = ∏ i, (X - C ((↑(c⁻¹) : R) ^ (d i - 1))) := by
  let J := (SymmetricAlgebra.lift x).mapMatrix (jacobianMatrix b f)
  have hdet : J.det ≠ 0 := by
    simpa only [J, ← AlgHom.map_det, ← jacobian_def] using hJ
  have hchain : J = Matrix.diagonal (fun i ↦ (c : R) ^ (d i - 1)) *
      (J * (toMatrix b b g).transpose) := by
    ext i j
    rw [Matrix.diagonal_mul]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, toMatrix_apply,
      J, AlgHom.mapMatrix_apply, Matrix.map_apply, jacobianMatrix_apply]
    rw [lift_pderiv_comp_of_map_eq_self (f i) (hf i) (hg i) x hx (b.coord j),
      pderiv_eq_sum b]
    simp [mul_comm]
  have hconj : Matrix.diagonal (fun i ↦ (↑(c⁻¹) : R) ^ (d i - 1)) * J =
      J * (toMatrix b b g).transpose := by
    conv_lhs => rw [hchain]
    simp [← Matrix.mul_assoc, ← mul_pow]
  rw [← g.charpoly_toMatrix b, ← Matrix.charpoly_transpose,
    ← Matrix.charpoly_eq_of_mul_eq_mul hdet hconj, Matrix.charpoly_diagonal]

end LinearMap
