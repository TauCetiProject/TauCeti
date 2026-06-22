/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hadamard

/-!
# Positive-definite kernels

A *positive-definite kernel* on a type `α` is a function `K : α → α → 𝕜`, valued in an `RCLike`
field `𝕜` (so `ℝ` or `ℂ`), such that every finite Gram matrix `(K (v i) (v j))ᵢⱼ` is positive
semidefinite. Equivalently, for every finite family `v` of points and every coefficient vector
`x`, the Hermitian form `∑ᵢⱼ conj(xᵢ) · xⱼ · K (vᵢ) (vⱼ)` is nonnegative.

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

## Main predicate

Positive-definite kernels are represented directly by Mathlib's arbitrary-index predicate
`(Matrix.of fun a b => K a b).PosSemidef`.

## Main statements

* `Matrix.PosSemidef.kernel_conj_symm`, `Matrix.PosSemidef.kernel_apply_self_nonneg`: the basic
  pointwise consequences (conjugate symmetry and nonnegative diagonal).
* `Matrix.PosSemidef.kernel_gram`, `Matrix.PosSemidef.kernel_sum_conj_mul_mul_nonneg`:
  restatements for arbitrary finite Gram matrices and their quadratic forms.
* `TauCeti.posSemidef_kernel_iff`: the quadratic-form characterization, whose reverse direction
  builds the positive semidefinite kernel matrix directly from the quadratic-form condition.
* `TauCeti.posSemidef_kernel_add`, `TauCeti.posSemidef_kernel_smul`,
  `TauCeti.posSemidef_kernel_mul`: closure under sums, nonnegative real scalar multiples, and
  (Schur / entrywise) products.
* `TauCeti.posSemidef_kernel_comp`: pullback along an arbitrary map.
* `TauCeti.posSemidef_kernel_conj_mul`: the rank-one kernels `(a, b) ↦ conj(g a) · g b`.
-/

open Matrix
open scoped ComplexConjugate ComplexOrder

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {α β : Type*}

namespace Matrix.PosSemidef

variable {K K₁ K₂ : α → α → 𝕜}

/-- A positive-definite kernel gives a positive semidefinite Gram matrix for any finite index
type. This is the arbitrary-finite-family form of the `Fin n` definition. -/
theorem kernel_gram (hK : (Matrix.of fun a b => K a b).PosSemidef) {ι : Type*} [Finite ι]
    (v : ι → α) : (Matrix.of fun i j => K (v i) (v j)).PosSemidef := by
  simpa [Matrix.submatrix, Function.comp_def] using hK.submatrix v

/-- The quadratic-form nonnegativity satisfied by a positive-definite kernel on `Fin n`-indexed
families: `0 ≤ ∑ᵢⱼ conj(xᵢ) · xⱼ · K (vᵢ) (vⱼ)`. The full iff characterization is
`posSemidef_kernel_iff`. -/
theorem kernel_sum_conj_mul_mul_nonneg (hK : (Matrix.of fun a b => K a b).PosSemidef)
    (n : ℕ) (v : Fin n → α)
    (x : Fin n → 𝕜) : 0 ≤ ∑ i, ∑ j, conj (x i) * x j * K (v i) (v j) := by
  classical
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (hK.submatrix v)).2 x
  simpa [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum,
    RCLike.star_def, mul_assoc, mul_left_comm, mul_comm] using h

/-- A positive-definite kernel is conjugate-symmetric: `conj (K a b) = K b a`. -/
theorem kernel_conj_symm (hK : (Matrix.of fun a b => K a b).PosSemidef) (a b : α) :
    conj (K a b) = K b a := by
  have h := hK.isHermitian.apply b a
  simp only [Matrix.of_apply] at h
  rw [starRingEnd_apply]
  exact h

/-- The diagonal values of a positive-definite kernel are nonnegative reals. -/
theorem kernel_apply_self_nonneg (hK : (Matrix.of fun a b => K a b).PosSemidef) (a : α) :
    0 ≤ K a a := by
  simpa using hK.diag_nonneg (i := a)

end Matrix.PosSemidef

variable {K K₁ K₂ : α → α → 𝕜}

/-- Positive-definite kernels are closed under addition. -/
theorem posSemidef_kernel_add (h₁ : (Matrix.of fun a b => K₁ a b).PosSemidef)
    (h₂ : (Matrix.of fun a b => K₂ a b).PosSemidef) :
    (Matrix.of fun a b => K₁ a b + K₂ a b).PosSemidef := by
  have e : (Matrix.of fun a b => K₁ a b + K₂ a b)
      = (Matrix.of fun a b => K₁ a b) + (Matrix.of fun a b => K₂ a b) := by
    ext i j; simp
  rw [e]
  exact h₁.add h₂

/-- Positive-definite kernels are closed under the Schur (entrywise) product. This is the kernel
form of the Schur product theorem `Matrix.PosSemidef.hadamard`. -/
theorem posSemidef_kernel_mul (h₁ : (Matrix.of fun a b => K₁ a b).PosSemidef)
    (h₂ : (Matrix.of fun a b => K₂ a b).PosSemidef) :
    (Matrix.of fun a b => K₁ a b * K₂ a b).PosSemidef := by
  have e : (Matrix.of fun a b => K₁ a b * K₂ a b)
      = (Matrix.of fun a b => K₁ a b) ⊙ (Matrix.of fun a b => K₂ a b) := by
    ext i j; simp [Matrix.hadamard_apply]
  rw [e]
  exact h₁.hadamard h₂

/-- The pullback of a positive-definite kernel along an arbitrary map is positive definite. -/
theorem posSemidef_kernel_comp (hK : (Matrix.of fun a b => K a b).PosSemidef) (f : β → α) :
    (Matrix.of fun a b => K (f a) (f b)).PosSemidef := by
  simpa [Matrix.submatrix, Function.comp_def] using hK.submatrix f

/-- The quadratic-form characterization of a positive-definite kernel: `K` is positive definite if
and only if it is conjugate-symmetric and every Hermitian form
`∑ᵢⱼ conj (x i) · x j · K (v i) (v j)` is nonnegative. The reverse direction is the introduction
rule that builds the positive semidefinite kernel matrix directly from the quadratic-form
condition (for instance for the `K(a, b) = F(a + b⋆)` construction). -/
theorem posSemidef_kernel_iff {K : α → α → 𝕜} :
    (Matrix.of fun a b => K a b).PosSemidef ↔
      (∀ a b, conj (K a b) = K b a) ∧
        ∀ (n : ℕ) (v : Fin n → α) (x : Fin n → 𝕜),
          0 ≤ ∑ i, ∑ j, conj (x i) * x j * K (v i) (v j) := by
  classical
  refine ⟨fun hK =>
    ⟨Matrix.PosSemidef.kernel_conj_symm hK,
      Matrix.PosSemidef.kernel_sum_conj_mul_mul_nonneg hK⟩, fun ⟨hsymm, hpos⟩ => ?_⟩
  have hfin : ∀ (n : ℕ) (v : Fin n → α),
      (Matrix.of fun i j => K (v i) (v j)).PosSemidef := by
    intro n v
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · ext i j
      rw [Matrix.conjTranspose_apply, ← starRingEnd_apply]
      exact hsymm (v j) (v i)
    · refine (hpos n v x).trans_eq ?_
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [starRingEnd_apply]
      ring
  refine ⟨?_, fun x => ?_⟩
  · ext a b
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, ← starRingEnd_apply]
    exact hsymm b a
  · let v : x.support → α := fun i => i
    let y : x.support → 𝕜 := fun i => x i
    have hgram : (Matrix.of fun i j : x.support => K (i : α) (j : α)).PosSemidef := by
      let e := Fintype.equivFin x.support
      rw [← Matrix.posSemidef_submatrix_equiv e.symm]
      exact hfin (Fintype.card x.support) (fun i => v (e.symm i))
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hgram).2 y
    have h' :
        0 ≤ ∑ i : x.support, ∑ j : x.support,
          star (x (i : α)) * (K (i : α) (j : α) * x (j : α)) := by
      simpa only [v, y, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
        Finset.mul_sum, RCLike.star_def, mul_assoc] using h
    have h'' :
        0 ≤ ∑ i ∈ x.support, ∑ j ∈ x.support,
          star (x i) * (K i j * x j) := by
      convert h' using 1
      rw [Finset.sum_subtype x.support (by intro a; rfl)]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_subtype x.support (by intro a; rfl)]
    simpa only [Matrix.of_apply, Finsupp.sum, mul_assoc] using h''

/-- The rank-one kernels `(a, b) ↦ conj (g a) · g b` are positive definite. With `g ≡ 1` this gives
the constant kernel `1`; with general `g` these are the building blocks whose nonnegative mixtures
and Schur products generate further positive-definite kernels. -/
theorem posSemidef_kernel_conj_mul (g : α → 𝕜) :
    (Matrix.of fun a b => conj (g a) * g b).PosSemidef := by
  rw [posSemidef_kernel_iff]
  refine ⟨?_, fun n v x => ?_⟩
  · intro a b
    simp [mul_comm]
  · have e : (Matrix.of fun i j => conj (g (v i)) * g (v j))
        = Matrix.vecMulVec (star fun i => g (v i)) (fun i => g (v i)) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply, starRingEnd_apply]
    have h : (Matrix.of fun i j => conj (g (v i)) * g (v j)).PosSemidef := by
      rw [e]
      exact Matrix.posSemidef_vecMulVec_star_self _
    have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2 x
    simpa [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum,
      RCLike.star_def, mul_assoc, mul_left_comm, mul_comm] using hq

/-- Positive-definite kernels are closed under multiplication by a nonnegative real scalar. -/
theorem posSemidef_kernel_smul (hK : (Matrix.of fun a b => K a b).PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) :
    (Matrix.of fun a b => (c : 𝕜) * K a b).PosSemidef := by
  have hconst : (Matrix.of fun _ _ : α => (c : 𝕜)).PosSemidef := by
    have h := posSemidef_kernel_conj_mul (fun _ : α => ((Real.sqrt c : ℝ) : 𝕜))
    have hc' : ((Real.sqrt c : ℝ) : 𝕜) * ((Real.sqrt c : ℝ) : 𝕜) = (c : 𝕜) := by
      rw [← RCLike.ofReal_mul, Real.mul_self_sqrt hc]
    simpa [RCLike.conj_ofReal, hc'] using h
  exact posSemidef_kernel_mul hconst hK

end TauCeti
