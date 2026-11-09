/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.RingTheory.MvPolynomial.Harmonic
public import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# Orthogonal invariance of harmonic polynomials

Under the linear change of variables `Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ` (`MvPolynomial.linearSubst M`), which
turns a polynomial `p` into `x ↦ p (M x)`, the chain rule transforms the Laplacian
`Δ = ∑ᵢ ∂²/∂Xᵢ²` into the constant-coefficient operator with coefficient matrix `M Mᵀ`:

`Δ (p ∘ M) = ∑ᵢₖ (M Mᵀ)ᵢₖ (∂ₖ ∂ᵢ p) ∘ M`.

So an orthogonal substitution commutes with the Laplacian, and it fixes the squared norm
`r² = ∑ᵢ Xᵢ²`. It preserves homogeneity, hence maps the harmonic homogeneous polynomials `H_d` of
degree `d` to themselves. The orthogonal group `O(n)` therefore acts linearly on `H_d` by

`(g • p)(x) = p (g⁻¹ x)`,

which is the substitution along `g⁻¹ = gᵀ`. Over `ℝ`, restricting polynomials to the unit sphere
turns this into the action of `O(n)` on spherical harmonics of degree `d`; that restriction is not
treated here.

The identities for a single matrix hold over any commutative semiring, and the representation
over any commutative ring, so complex harmonic polynomials under the complex orthogonal group
`Mᵀ M = 1` are included. As in `Mathlib.LinearAlgebra.UnitaryGroup`, `Matrix.orthogonalGroup` is
read through the trivial star structure `starRingOfComm`.

## Main definitions

* `MvPolynomial.harmonicRep σ R d`: the representation of `Matrix.orthogonalGroup σ R` on the
  harmonic homogeneous polynomials of degree `d`.

## Main results

* `MvPolynomial.laplacian_linearSubst`: the chain rule
  `Δ (p ∘ M) = ∑ᵢₖ (M Mᵀ)ᵢₖ (∂ₖ ∂ᵢ p) ∘ M`.
* `MvPolynomial.laplacian_linearSubst_of_mul_transpose_eq_one`: if `M Mᵀ = 1`, then
  `Δ (p ∘ M) = (Δ p) ∘ M`.
* `MvPolynomial.linearSubst_normSq_of_transpose_mul_eq_one`: if `Mᵀ M = 1`, then `r² ∘ M = r²`.
* `MvPolynomial.linearSubst_mem_harmonicSubmodule`: if `M Mᵀ = 1`, the substitution along `M`
  maps `H_d` to itself.
* `MvPolynomial.eval_harmonicRep_apply`: `(g • p)(x) = p (g⁻¹ x)`.

## References

* S. Axler, P. Bourdon and W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer GTM 137
  (2001), Chapter 1 (orthogonal invariance of the Laplacian) and Chapter 5.
* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Princeton
  University Press (1971), Chapter IV, Section 2 (the action of rotations on spherical harmonics).
-/

public section

open Matrix

namespace MvPolynomial

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

/-- **The chain rule for the Laplacian** under a linear change of variables:
`Δ (p ∘ M) = ∑ᵢₖ (M Mᵀ)ᵢₖ (∂ₖ ∂ᵢ p) ∘ M`. -/
theorem laplacian_linearSubst (M : Matrix σ σ R) (p : MvPolynomial σ R) :
    laplacian (linearSubst M p) =
      ∑ i, ∑ k, C ((M * Mᵀ) i k) * linearSubst M (pderiv k (pderiv i p)) := by
  simp only [laplacian_apply, pderiv_linearSubst, map_sum, pderiv_C_mul, Finset.mul_sum,
    Matrix.mul_apply, transpose_apply, map_mul, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

/-- A substitution along a matrix with `M Mᵀ = 1` commutes with the Laplacian:
`Δ (p ∘ M) = (Δ p) ∘ M`. -/
theorem laplacian_linearSubst_of_mul_transpose_eq_one [DecidableEq σ] {M : Matrix σ σ R}
    (hM : M * Mᵀ = 1) (p : MvPolynomial σ R) :
    laplacian (linearSubst M p) = linearSubst M (laplacian p) := by
  rw [laplacian_linearSubst, hM]
  simp [Matrix.one_apply, laplacian_apply]

/-- A substitution along a matrix with `Mᵀ M = 1` fixes the squared norm `r² = ∑ᵢ Xᵢ²`. -/
theorem linearSubst_normSq_of_transpose_mul_eq_one [DecidableEq σ] {M : Matrix σ σ R}
    (hM : Mᵀ * M = 1) : linearSubst M (normSq σ R) = normSq σ R := by
  have hMjk (j k : σ) : ∑ i, M i j * M i k = if j = k then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hM j) k
  -- Expanding `∑ᵢ (∑ⱼ Mᵢⱼ Xⱼ)²` gives `∑ⱼₖ (Mᵀ M)ⱼₖ Xⱼ Xₖ`.
  have hsum (j k : σ) : ∑ i, C (M i j) * X j * (C (M i k) * X k) =
      C (∑ i, M i j * M i k) * (X j * X k : MvPolynomial σ R) := by
    rw [map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_mul]; ring
  simp only [normSq_def, map_sum, sq, map_mul, linearSubst_X, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]
  simp [hsum, hMjk]

/-- A substitution along a matrix with `M Mᵀ = 1` maps the harmonic homogeneous polynomials of
degree `d` to themselves. -/
theorem linearSubst_mem_harmonicSubmodule [DecidableEq σ] {M : Matrix σ σ R}
    (hM : M * Mᵀ = 1) {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ harmonicSubmodule σ R d) : linearSubst M p ∈ harmonicSubmodule σ R d := by
  rw [mem_harmonicSubmodule_iff] at hp ⊢
  exact ⟨hp.1.linearSubst M, by rw [laplacian_linearSubst_of_mul_transpose_eq_one hM, hp.2,
    map_zero]⟩

section OrthogonalGroup

-- `Matrix.orthogonalGroup` reads the transpose as a `star`, through the trivial star structure
-- on the commutative coefficient ring, exactly as in `Mathlib.LinearAlgebra.UnitaryGroup`.
attribute [local instance] starRingOfComm

variable (σ) (R : Type*) [CommRing R] [DecidableEq σ]

/-- The orthogonal group acts on the harmonic homogeneous polynomials of degree `d` by
`(g • p)(x) = p (g⁻¹ x)` (`MvPolynomial.eval_harmonicRep_apply`). Since `g⁻¹ = gᵀ`, the element
`g` acts by the substitution `linearSubst gᵀ`. -/
noncomputable def harmonicRep (d : ℕ) :
    Representation R (Matrix.orthogonalGroup σ R) (harmonicSubmodule σ R d) where
  toFun g := (linearSubst (g : Matrix σ σ R)ᵀ).toLinearMap.restrict fun _ hp ↦
    linearSubst_mem_harmonicSubmodule
      (by rw [transpose_transpose, ← mem_orthogonalGroup_iff']; exact g.2) hp
  map_one' := LinearMap.ext fun p ↦ Subtype.ext <| by simp
  map_mul' g h := LinearMap.ext fun p ↦ Subtype.ext <|
    (congrArg (linearSubst · (p : MvPolynomial σ R))
      (transpose_mul (g : Matrix σ σ R) (h : Matrix σ σ R))).trans (linearSubst_mul_apply _ _ _)

variable {σ R}

@[simp]
theorem coe_harmonicRep_apply {d : ℕ} (g : Matrix.orthogonalGroup σ R)
    (p : harmonicSubmodule σ R d) :
    (harmonicRep σ R d g p : MvPolynomial σ R) = linearSubst (g : Matrix σ σ R)ᵀ p :=
  (rfl)

/-- The orthogonal group acts on harmonic polynomials by `(g • p)(x) = p (g⁻¹ x)`. -/
theorem eval_harmonicRep_apply {d : ℕ} (g : Matrix.orthogonalGroup σ R)
    (p : harmonicSubmodule σ R d) (x : σ → R) :
    eval x (harmonicRep σ R d g p : MvPolynomial σ R) =
      eval ((g⁻¹ : Matrix.orthogonalGroup σ R) *ᵥ x) (p : MvPolynomial σ R) := by
  rw [coe_harmonicRep_apply, eval_linearSubst, Matrix.UnitaryGroup.inv_val,
    Matrix.star_eq_conjTranspose]
  -- Under `starRingOfComm` the star on `R` is the identity by definition, so the conjugate
  -- transpose of a matrix is its transpose.
  rfl

end OrthogonalGroup

end MvPolynomial
