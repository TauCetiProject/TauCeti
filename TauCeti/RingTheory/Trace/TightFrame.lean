/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Resolutions of the identity from embedded tight frames

A tight frame at the complex embeddings with frame bound `b²` yields a resolution of
identity on any finite collection of coordinates. Divide each frame member by `b * k`,
place it in a single coordinate, and use multiplicity `k²`. These are the linear forms
used to pull back theta functions on products of complex lines.

The normalization is that of `New.IsTightFrame.isResolution` in
`grh/src/New/Derivatives/Vacuum/StandardDataProducts.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open Matrix
open scoped ComplexConjugate Kronecker

namespace Algebra

variable {K E ι : Type*} [CommRing K] [Field E] [Algebra K E] [Algebra K ℂ] [Fintype ι]
  [DecidableEq (E →ₐ[K] ℂ)]

/-- A family with frame bound `b²`, divided by `b * k`, has frame bound `1/k²`.
Equivalently, its frame operator with multiplicity `k²` is the identity. -/
theorem sq_smul_conjTranspose_mul_self_embeddingsMatrix_div
    (w : ι → E) {b k : ℕ} (hb : b ≠ 0) (hk : k ≠ 0)
    (hframe : (embeddingsMatrix K ℂ w)ᴴ * embeddingsMatrix K ℂ w =
      (b : ℂ) ^ 2 • (1 : Matrix (E →ₐ[K] ℂ) (E →ₐ[K] ℂ) ℂ)) :
    let A := embeddingsMatrix K ℂ (fun i ↦ w i / ((b : E) * (k : E)))
    (k : ℂ) ^ 2 • (Aᴴ * A) = 1 := by
  let B := embeddingsMatrix K ℂ w
  let c : ℂ := ((b : ℂ) * k)⁻¹
  have hA : embeddingsMatrix K ℂ (fun i ↦ w i / ((b : E) * (k : E))) = c • B := by
    ext i σ
    simp [c, B, div_eq_inv_mul]
  have hc : star c = c := by simp [c]
  have hscale : (k : ℂ) ^ 2 * (c * (c * (b : ℂ) ^ 2)) = 1 := by
    dsimp only [c]
    field_simp [Nat.cast_ne_zero.mpr hb, Nat.cast_ne_zero.mpr hk]
  dsimp only
  have hB : Bᴴ * B = (b : ℂ) ^ 2 • 1 := hframe
  simp only [hA, conjTranspose_smul, hc, Matrix.smul_mul, Matrix.mul_smul, hB,
    smul_smul, hscale, one_smul]

/-- Embed each `w i / (b * k)` in each coordinate separately. The resulting vectors, with
multiplicity `k²`, reconstruct every vector indexed by a complex embedding and a coordinate.
The inner sum is the Hermitian pairing with the embedded vector in coordinate `j`. -/
theorem sum_mul_sum_conj_div_single_eq_of_embeddingsMatrix
    (w : ι → E) {b k : ℕ} (hb : b ≠ 0) (hk : k ≠ 0)
    (hframe : (embeddingsMatrix K ℂ w)ᴴ * embeddingsMatrix K ℂ w =
      (b : ℂ) ^ 2 • (1 : Matrix (E →ₐ[K] ℂ) (E →ₐ[K] ℂ) ℂ))
    {n : Type*} [Fintype n] [DecidableEq n] [Fintype (E →ₐ[K] ℂ)] (z : (E →ₐ[K] ℂ) × n → ℂ) :
    let u (i : ι) (j : n) : n → E := Pi.single j (w i / ((b : E) * (k : E)))
    ∀ (σ : E →ₐ[K] ℂ) (a : n),
      (∑ i, ∑ j, (k : ℂ) ^ 2 * σ (u i j a) *
        (∑ τ : E →ₐ[K] ℂ, ∑ t : n, conj (τ (u i j t)) * z (τ, t))) = z (σ, a) := by
  let A := embeddingsMatrix K ℂ (fun i ↦ w i / ((b : E) * (k : E)))
  let B := A ⊗ₖ (1 : Matrix n n ℂ)
  have hA : (k : ℂ) ^ 2 • (Aᴴ * A) = 1 :=
    sq_smul_conjTranspose_mul_self_embeddingsMatrix_div w hb hk hframe
  -- The identity on the coordinate index leaves the weighted frame bound unchanged.
  have hB : (k : ℂ) ^ 2 • (Bᴴ * B) = 1 := by
    dsimp only [B]
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, mul_one,
      ← smul_kronecker, hA, one_kronecker_one]
  have hreconstruct : (k : ℂ) ^ 2 • (Bᵀ *ᵥ ((Bᴴ)ᵀ *ᵥ z)) = z := by
    rw [mulVec_mulVec, ← transpose_mul, ← smul_mulVec, ← transpose_smul, hB, transpose_one,
      one_mulVec]
  have hentry (i : ι) (j : n) (σ : E →ₐ[K] ℂ) (a : n) :
      B (i, j) (σ, a) = σ ((Pi.single j (w i / ((b : E) * (k : E))) : n → E) a) := by
    by_cases h : j = a <;> simp [B, A, h]
  dsimp only
  intro σ a
  simpa only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.conjTranspose_apply, Complex.star_def, Fintype.sum_prod_type, hentry,
    Finset.mul_sum, mul_assoc] using congr_fun hreconstruct (σ, a)

end Algebra
