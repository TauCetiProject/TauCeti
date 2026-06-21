/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hadamard

/-!
# Positive-definite kernels

A *positive-definite kernel* on a type `α` is a function `K : α → α → ℂ` such that every finite
Gram matrix `(K (v i) (v j))ᵢⱼ` is positive semidefinite. Equivalently, for every finite family
`v` of points and every coefficient vector `x`, the Hermitian form `∑ᵢⱼ conj(xᵢ) · xⱼ · K (vᵢ) (vⱼ)`
is nonnegative.

This is the two-variable companion of a positive-definite function: the roadmap's
`K(a, b) = F(a + b⋆)` construction turns a positive-definite function on an involutive monoid
into a positive-definite kernel, and conversely the kernel form is the object underlying the
GNS / Kolmogorov decomposition. Stating it via Mathlib's `Matrix.PosSemidef` lets the positive
semidefinite matrix calculus do the work: closure under (Schur / entrywise) products is exactly
the Schur product theorem `Matrix.PosSemidef.hadamard`, and the rank-one kernels
`(a, b) ↦ conj(g a) · g b` come from `Matrix.posSemidef_vecMulVec_star_self`.

This advances the `OneParameterSemigroups` roadmap, Part C ("Positive-definite functions and
Bochner's theorem") in `TauCetiRoadmap/OneParameterSemigroups/README.md`: the `API to develop`
bullet "the PD-function ↔ PD-kernel equivalence (`K(a, b) = F(a + b⋆)` ...), pullbacks, and the
GNS/Kolmogorov decomposition". Mathlib has positive definiteness only for matrices and quadratic
forms, with no positive-definite-kernel notion, so this is new; no code is vendored.

## Main definitions

* `TauCeti.IsPositiveDefiniteKernel`: the predicate that every finite Gram matrix of `K` is
  positive semidefinite.

## Main statements

* `IsPositiveDefiniteKernel.conj_symm`, `IsPositiveDefiniteKernel.apply_self_nonneg`: the basic
  pointwise consequences (conjugate symmetry and nonnegative diagonal).
* `IsPositiveDefiniteKernel.posSemidef_gram`, `IsPositiveDefiniteKernel.sum_conj_mul_mul_nonneg`:
  restatements for arbitrary finite Gram matrices and their quadratic forms.
* `IsPositiveDefiniteKernel.add`, `IsPositiveDefiniteKernel.smul`, `IsPositiveDefiniteKernel.mul`:
  closure under sums, nonnegative real scalar multiples, and (Schur / entrywise) products.
* `IsPositiveDefiniteKernel.comp`: pullback along an arbitrary map.
* `TauCeti.isPositiveDefiniteKernel_conj_mul`: the rank-one kernels `(a, b) ↦ conj(g a) · g b`.
-/

open Matrix
open scoped ComplexConjugate ComplexOrder

namespace TauCeti

variable {α β : Type*}

/-- A kernel `K : α → α → ℂ` is *positive definite* when every finite Gram matrix
`(K (v i) (v j))ᵢⱼ` is positive semidefinite. Finite families are indexed by `Fin n`; every
finite family reindexes to this form. -/
def IsPositiveDefiniteKernel (K : α → α → ℂ) : Prop :=
  ∀ (n : ℕ) (v : Fin n → α), (Matrix.of fun i j => K (v i) (v j)).PosSemidef

/-- The rank-one kernels `(a, b) ↦ conj (g a) · g b` are positive definite. With `g ≡ 1` this gives
the constant kernel `1`; with general `g` these are the building blocks whose nonnegative mixtures
and Schur products generate further positive-definite kernels. -/
theorem isPositiveDefiniteKernel_conj_mul (g : α → ℂ) :
    IsPositiveDefiniteKernel (fun a b => conj (g a) * g b) := by
  intro n v
  have e : (Matrix.of fun i j => conj (g (v i)) * g (v j))
      = Matrix.vecMulVec (star fun i => g (v i)) (fun i => g (v i)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply, starRingEnd_apply]
  rw [e]
  exact Matrix.posSemidef_vecMulVec_star_self _

namespace IsPositiveDefiniteKernel

variable {K K₁ K₂ : α → α → ℂ}

/-- A positive-definite kernel gives a positive semidefinite Gram matrix for any finite index
type. This is the arbitrary-finite-family form of the `Fin n` definition. -/
theorem posSemidef_gram (hK : IsPositiveDefiniteKernel K) {ι : Type*} [Finite ι]
    (v : ι → α) : (Matrix.of fun i j => K (v i) (v j)).PosSemidef := by
  classical
  letI := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  have h := (hK (Fintype.card ι) (fun i : Fin (Fintype.card ι) => v (e.symm i))).submatrix e
  simpa [Matrix.submatrix, e] using h

/-- The quadratic-form characterization of a positive-definite kernel on `Fin n`-indexed
families. -/
theorem sum_conj_mul_mul_nonneg (hK : IsPositiveDefiniteKernel K) (n : ℕ) (v : Fin n → α)
    (x : Fin n → ℂ) : 0 ≤ ∑ i, ∑ j, conj (x i) * x j * K (v i) (v j) := by
  classical
  have h := (hK n v).2 (Finsupp.equivFunOnFinite.symm x)
  simpa [Finsupp.sum_fintype, mul_assoc, mul_left_comm, mul_comm] using h

/-- A positive-definite kernel is conjugate-symmetric: `conj (K a b) = K b a`. -/
theorem conj_symm (hK : IsPositiveDefiniteKernel K) (a b : α) : conj (K a b) = K b a := by
  have h := (hK 2 ![a, b]).isHermitian.apply 1 0
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [starRingEnd_apply]
  exact h

/-- The diagonal values of a positive-definite kernel are nonnegative reals. -/
theorem apply_self_nonneg (hK : IsPositiveDefiniteKernel K) (a : α) : 0 ≤ K a a := by
  simpa using (hK 1 (fun _ => a)).diag_nonneg (i := 0)

/-- Positive-definite kernels are closed under addition. -/
theorem add (h₁ : IsPositiveDefiniteKernel K₁) (h₂ : IsPositiveDefiniteKernel K₂) :
    IsPositiveDefiniteKernel (fun a b => K₁ a b + K₂ a b) := by
  intro n v
  have e : (Matrix.of fun i j => K₁ (v i) (v j) + K₂ (v i) (v j))
      = (Matrix.of fun i j => K₁ (v i) (v j)) + (Matrix.of fun i j => K₂ (v i) (v j)) := by
    ext i j; simp
  rw [e]
  exact (h₁ n v).add (h₂ n v)

/-- Positive-definite kernels are closed under the Schur (entrywise) product. This is the kernel
form of the Schur product theorem `Matrix.PosSemidef.hadamard`. -/
theorem mul (h₁ : IsPositiveDefiniteKernel K₁) (h₂ : IsPositiveDefiniteKernel K₂) :
    IsPositiveDefiniteKernel (fun a b => K₁ a b * K₂ a b) := by
  intro n v
  have e : (Matrix.of fun i j => K₁ (v i) (v j) * K₂ (v i) (v j))
      = (Matrix.of fun i j => K₁ (v i) (v j)) ⊙ (Matrix.of fun i j => K₂ (v i) (v j)) := by
    ext i j; simp [Matrix.hadamard_apply]
  rw [e]
  exact (h₁ n v).hadamard (h₂ n v)

/-- Positive-definite kernels are closed under multiplication by a nonnegative real scalar. -/
theorem smul (hK : IsPositiveDefiniteKernel K) {c : ℝ} (hc : 0 ≤ c) :
    IsPositiveDefiniteKernel (fun a b => (c : ℂ) * K a b) := by
  have hconst : IsPositiveDefiniteKernel (fun _ _ : α => (c : ℂ)) := by
    have h := isPositiveDefiniteKernel_conj_mul (fun _ : α => ((Real.sqrt c : ℝ) : ℂ))
    have hc' : ((Real.sqrt c : ℝ) : ℂ) * ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
    simpa [Complex.conj_ofReal, hc'] using h
  exact hconst.mul hK

/-- The pullback of a positive-definite kernel along an arbitrary map is positive definite. -/
theorem comp (hK : IsPositiveDefiniteKernel K) (f : β → α) :
    IsPositiveDefiniteKernel (fun a b => K (f a) (f b)) := by
  intro n v
  exact hK n (fun i => f (v i))

end IsPositiveDefiniteKernel

end TauCeti
