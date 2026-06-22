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
semidefinite. Equivalently, `K` is conjugate-symmetric and, for every finite family `v` of
points and every coefficient vector `x`, the Hermitian form
`∑ᵢⱼ conj(xᵢ) · xⱼ · K (vᵢ) (vⱼ)` is nonnegative.

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

* `TauCeti.IsPositiveDefiniteKernel`: the predicate that the full kernel matrix is positive
  semidefinite.

## Main statements

* `IsPositiveDefiniteKernel.conj_symm`, `IsPositiveDefiniteKernel.apply_self_nonneg`: the basic
  pointwise consequences (conjugate symmetry and nonnegative diagonal).
* `IsPositiveDefiniteKernel.posSemidef_gram`, `IsPositiveDefiniteKernel.sum_conj_mul_mul_nonneg`:
  restatements for arbitrary finite Gram matrices and their quadratic forms.
* `TauCeti.isPositiveDefiniteKernel_def`: the bridge to Mathlib's arbitrary-index
  `Matrix.PosSemidef` predicate on `Matrix.of K`.
* `TauCeti.isPositiveDefiniteKernel_iff`: the quadratic-form characterization, whose reverse
  direction builds a positive-definite kernel from conjugate symmetry and form nonnegativity.
* `IsPositiveDefiniteKernel.add`, `IsPositiveDefiniteKernel.smul`, `IsPositiveDefiniteKernel.mul`:
  closure under sums, nonnegative real scalar multiples, and (Schur / entrywise) products.
* `IsPositiveDefiniteKernel.comp`: pullback along an arbitrary map.
* `TauCeti.isPositiveDefiniteKernel_conj_mul`: the rank-one kernels
  `(a, b) ↦ conj(g a) · g b`.
-/

open Matrix
open scoped ComplexConjugate ComplexOrder

namespace TauCeti

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {α : Type v} {β : Type w}

/-- A kernel `K : α → α → 𝕜` is *positive definite* when the matrix indexed by all points of `α`
is positive semidefinite. Finite Gram matrices and their quadratic forms are exposed by
`IsPositiveDefiniteKernel.posSemidef_gram` and
`IsPositiveDefiniteKernel.sum_conj_mul_mul_nonneg`. -/
abbrev IsPositiveDefiniteKernel (K : α → α → 𝕜) : Prop :=
  (Matrix.of fun a b => K a b).PosSemidef

/-- The named kernel predicate is definitionally Mathlib's positive semidefinite predicate on the
full kernel matrix. -/
theorem isPositiveDefiniteKernel_def (K : α → α → 𝕜) :
    IsPositiveDefiniteKernel K ↔ (Matrix.of fun a b => K a b).PosSemidef := by
  rfl

/-- The rank-one kernels `(a, b) ↦ conj (g a) · g b` are positive definite. With `g ≡ 1` this gives
the constant kernel `1`; with general `g` these are building blocks whose nonnegative mixtures
and Schur products generate further positive-definite kernels. -/
theorem isPositiveDefiniteKernel_conj_mul (g : α → 𝕜) :
    IsPositiveDefiniteKernel (fun a b => conj (g a) * g b) := by
  classical
  change (Matrix.of fun a b => conj (g a) * g b).PosSemidef
  refine ⟨?_, fun x => ?_⟩
  · ext a b
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, ← starRingEnd_apply]
    simp [mul_comm]
  · let v : x.support → α := fun i => i
    let y : x.support → 𝕜 := fun i => x i
    have hgram : (Matrix.of fun i j : x.support => conj (g (i : α)) * g (j : α)).PosSemidef := by
      have e : (Matrix.of fun i j : x.support => conj (g (i : α)) * g (j : α))
          = Matrix.vecMulVec (star fun i : x.support => g (i : α))
              (fun i : x.support => g (i : α)) := by
        ext i j
        simp only [Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply, starRingEnd_apply]
      rw [e]
      exact Matrix.posSemidef_vecMulVec_star_self _
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hgram).2 y
    have h' :
        0 ≤ ∑ i : x.support, ∑ j : x.support,
          star (x (i : α)) * ((conj (g (i : α)) * g (j : α)) * x (j : α)) := by
      simpa only [v, y, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
        Finset.mul_sum, RCLike.star_def, mul_assoc] using h
    have h'' :
        0 ≤ ∑ i ∈ x.support, ∑ j ∈ x.support,
          star (x i) * ((conj (g i) * g j) * x j) := by
      convert h' using 1
      rw [Finset.sum_subtype x.support (by intro a; rfl)]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_subtype x.support (by intro a; rfl)]
    simpa only [Matrix.of_apply, Finsupp.sum, mul_assoc] using h''

namespace IsPositiveDefiniteKernel

variable {K K₁ K₂ : α → α → 𝕜}

/-- A positive-definite kernel gives a positive semidefinite Gram matrix for any finite index
type. -/
theorem posSemidef_gram (hK : IsPositiveDefiniteKernel K) {ι : Type*} [Finite ι]
    (v : ι → α) : (Matrix.of fun i j => K (v i) (v j)).PosSemidef := by
  simpa [Matrix.submatrix, Function.comp_def] using hK.submatrix v

/-- The quadratic-form nonnegativity satisfied by a positive-definite kernel on any finite index
type: `0 ≤ ∑ᵢⱼ conj(xᵢ) · xⱼ · K (vᵢ) (vⱼ)`. The full iff characterization is
`isPositiveDefiniteKernel_iff`. -/
theorem sum_conj_mul_mul_nonneg (hK : IsPositiveDefiniteKernel K) {ι : Type*} [Fintype ι]
    (v : ι → α) (x : ι → 𝕜) : 0 ≤ ∑ i, ∑ j, conj (x i) * x j * K (v i) (v j) := by
  classical
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (hK.posSemidef_gram v)).2 x
  simpa [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum,
    RCLike.star_def, mul_assoc, mul_left_comm, mul_comm] using h

/-- A positive-definite kernel is conjugate-symmetric: `conj (K a b) = K b a`. -/
theorem conj_symm (hK : IsPositiveDefiniteKernel K) (a b : α) : conj (K a b) = K b a := by
  have h := hK.isHermitian.apply b a
  simp only [Matrix.of_apply] at h
  rw [starRingEnd_apply]
  exact h

/-- The diagonal values of a positive-definite kernel are nonnegative. -/
theorem apply_self_nonneg (hK : IsPositiveDefiniteKernel K) (a : α) : 0 ≤ K a a := by
  simpa using hK.diag_nonneg (i := a)

/-- Positive-definite kernels are closed under addition. -/
theorem add (h₁ : IsPositiveDefiniteKernel K₁) (h₂ : IsPositiveDefiniteKernel K₂) :
    IsPositiveDefiniteKernel (fun a b => K₁ a b + K₂ a b) := by
  have e : (Matrix.of fun a b => K₁ a b + K₂ a b)
      = (Matrix.of fun a b => K₁ a b) + (Matrix.of fun a b => K₂ a b) := by
    ext i j
    simp
  change (Matrix.of fun a b => K₁ a b + K₂ a b).PosSemidef
  rw [e]
  exact Matrix.PosSemidef.add h₁ h₂

/-- Positive-definite kernels are closed under the Schur (entrywise) product. This is the kernel
form of the Schur product theorem `Matrix.PosSemidef.hadamard`. -/
theorem mul (h₁ : IsPositiveDefiniteKernel K₁) (h₂ : IsPositiveDefiniteKernel K₂) :
    IsPositiveDefiniteKernel (fun a b => K₁ a b * K₂ a b) := by
  have e : (Matrix.of fun a b => K₁ a b * K₂ a b)
      = (Matrix.of fun a b => K₁ a b) ⊙ (Matrix.of fun a b => K₂ a b) := by
    ext i j
    simp [Matrix.hadamard_apply]
  change (Matrix.of fun a b => K₁ a b * K₂ a b).PosSemidef
  rw [e]
  exact Matrix.PosSemidef.hadamard h₁ h₂

/-- Positive-definite kernels are closed under multiplication by a nonnegative real scalar. -/
theorem smul (hK : IsPositiveDefiniteKernel K) {c : ℝ} (hc : 0 ≤ c) :
    IsPositiveDefiniteKernel (fun a b => (c : 𝕜) * K a b) := by
  have hconst : IsPositiveDefiniteKernel (fun _ _ : α => (c : 𝕜)) := by
    have h := isPositiveDefiniteKernel_conj_mul (fun _ : α => ((Real.sqrt c : ℝ) : 𝕜))
    have hc' : ((Real.sqrt c : ℝ) : 𝕜) * ((Real.sqrt c : ℝ) : 𝕜) = (c : 𝕜) := by
      rw [← RCLike.ofReal_mul, Real.mul_self_sqrt hc]
    simpa [RCLike.conj_ofReal, hc'] using h
  exact hconst.mul hK

/-- The pullback of a positive-definite kernel along an arbitrary map is positive definite. -/
theorem comp (hK : IsPositiveDefiniteKernel K) (f : β → α) :
    IsPositiveDefiniteKernel (fun a b => K (f a) (f b)) := by
  simpa [Matrix.submatrix, Function.comp_def] using hK.submatrix f

end IsPositiveDefiniteKernel

/-- The quadratic-form characterization of a positive-definite kernel: `K` is positive definite if
and only if it is conjugate-symmetric and every Hermitian form
`∑ᵢⱼ conj (x i) · x j · K (v i) (v j)` is nonnegative. The reverse direction is the introduction
rule that builds a positive-definite kernel directly from the quadratic-form condition (for
instance for the `K(a, b) = F(a + b⋆)` construction), without unfolding `Matrix.PosSemidef`. -/
theorem isPositiveDefiniteKernel_iff {K : α → α → 𝕜} :
    IsPositiveDefiniteKernel K ↔
      (∀ a b, conj (K a b) = K b a) ∧
        ∀ {ι : Type v} [Fintype ι] (v : ι → α) (x : ι → 𝕜),
          0 ≤ ∑ i, ∑ j, conj (x i) * x j * K (v i) (v j) := by
  classical
  refine ⟨fun hK => ⟨hK.conj_symm, hK.sum_conj_mul_mul_nonneg⟩, fun ⟨hsymm, hpos⟩ => ?_⟩
  refine ⟨?_, fun x => ?_⟩
  · ext a b
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, ← starRingEnd_apply]
    exact hsymm b a
  · let v : x.support → α := fun i => i
    let y : x.support → 𝕜 := fun i => x i
    have hgram : (Matrix.of fun i j : x.support => K (i : α) (j : α)).PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨?_, fun z => ?_⟩
      · ext i j
        rw [Matrix.conjTranspose_apply, ← starRingEnd_apply]
        exact hsymm (j : α) (i : α)
      · refine (hpos (ι := ↥x.support) v z).trans_eq ?_
        simp only [v, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [starRingEnd_apply]
        ring
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

end TauCeti
