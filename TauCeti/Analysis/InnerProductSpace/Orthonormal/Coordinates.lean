/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Coordinates in a complex orthonormal basis

Let `b` be an orthonormal basis, indexed by a finite type `ι`, of a complex inner product space
`E`, so that every `v : E` has the complex coordinates `⟪b j, v⟫`.

* Each holomorphic quadratic form `∑ⱼ c j ⟪b j, v⟫²` in these coordinates is `v ↦ Q v v` for a
  continuous complex bilinear form `Q`.
* For units `ω j`, the real and imaginary parts of the rotated coordinates `conj (ω j) ⟪b j, v⟫`
  are real coordinates on `E`: they form a real linear equivalence `E ≃ₗ[ℝ] (ι ⊕ ι → ℝ)`.
  Rotating each coordinate so that `c j ω j²` is real diagonalizes the real quadratic form
  `Re (∑ⱼ c j ⟪b j, v⟫²)` in these real coordinates.

## Main definitions

* `OrthonormalBasis.rotatedRealCoords`: the real and imaginary parts of the rotated coordinates
  `conj (ω j) ⟪b j, v⟫`, as a real linear equivalence `E ≃ₗ[ℝ] (ι ⊕ ι → ℝ)`.

## Main statements

* `OrthonormalBasis.exists_apply_self_eq_sum_mul_inner_sq`: `∑ⱼ c j ⟪b j, v⟫²` is `Q v v` for a
  continuous complex bilinear form `Q`.
-/

public section

open Complex ComplexConjugate
open scoped InnerProductSpace

namespace OrthonormalBasis

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]

/-- The holomorphic quadratic form `∑ⱼ c j ⟪b j, z⟫²` is `z ↦ Q z z` for a continuous complex
bilinear form `Q`. -/
theorem exists_apply_self_eq_sum_mul_inner_sq (b : OrthonormalBasis ι ℂ E) (c : ι → ℂ) :
    ∃ Q : E →L[ℂ] E →L[ℂ] ℂ, ∀ v, Q v v = ∑ j, c j * ⟪b j, v⟫_ℂ ^ 2 :=
  ⟨∑ j, c j • (ContinuousLinearMap.mul ℂ ℂ).bilinearComp (innerSL ℂ (b j)) (innerSL ℂ (b j)),
    fun v ↦ by simp [sq]⟩

/-- The real and imaginary parts of the coordinates `conj (ω j) ⟪b j, v⟫` in an orthonormal
basis `b`, rotated by units `ω j`, as a real linear equivalence. -/
noncomputable def rotatedRealCoords (b : OrthonormalBasis ι ℂ E) (ω : ι → ℂ)
    (hω : ∀ j, ω j * conj (ω j) = 1) : E ≃ₗ[ℝ] (ι ⊕ ι → ℝ) where
  toFun v := Sum.elim (fun j ↦ (conj (ω j) * ⟪b j, v⟫_ℂ).re) (fun j ↦ (conj (ω j) * ⟪b j, v⟫_ℂ).im)
  invFun u := ∑ j, (ω j * ⟨u (Sum.inl j), u (Sum.inr j)⟩) • b j
  map_add' v w := by ext (j | j) <;> simp [inner_add_right, mul_add]
  map_smul' r v := by
    ext (j | j) <;> simp [← coe_smul, inner_smul_right, mul_left_comm _ (r : ℂ)]
  left_inv v := by
    conv_rhs => rw [← b.sum_repr' v]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Sum.elim_inl, Sum.elim_inr, Complex.eta, ← mul_assoc, hω, one_mul]
  right_inv u := by
    have hk (k : ι) : conj (ω k) * ⟪b k, ∑ j, (ω j * ⟨u (Sum.inl j), u (Sum.inr j)⟩) • b j⟫_ℂ =
        ⟨u (Sum.inl k), u (Sum.inr k)⟩ := by
      rw [b.orthonormal.inner_right_fintype, ← mul_assoc, mul_comm (conj _), hω, one_mul]
    ext (j | j) <;> simp only [hk, Sum.elim_inl, Sum.elim_inr]

/-- The `Sum.inl j` coordinate of `rotatedRealCoords` is the real part of
`conj (ω j) ⟪b j, v⟫`. -/
@[simp]
theorem rotatedRealCoords_apply_inl (b : OrthonormalBasis ι ℂ E) (ω : ι → ℂ)
    (hω : ∀ j, ω j * conj (ω j) = 1) (v : E) (j : ι) :
    b.rotatedRealCoords ω hω v (Sum.inl j) = (conj (ω j) * ⟪b j, v⟫_ℂ).re := by
  rfl

/-- The `Sum.inr j` coordinate of `rotatedRealCoords` is the imaginary part of
`conj (ω j) ⟪b j, v⟫`. -/
@[simp]
theorem rotatedRealCoords_apply_inr (b : OrthonormalBasis ι ℂ E) (ω : ι → ℂ)
    (hω : ∀ j, ω j * conj (ω j) = 1) (v : E) (j : ι) :
    b.rotatedRealCoords ω hω v (Sum.inr j) = (conj (ω j) * ⟪b j, v⟫_ℂ).im := by
  rfl

/-- The inverse of `rotatedRealCoords` sends real coordinates `u` to the vector whose rotated
coordinate `conj (ω j) ⟪b j, v⟫` is `u (Sum.inl j) + u (Sum.inr j) i`. -/
@[simp]
theorem rotatedRealCoords_symm_apply (b : OrthonormalBasis ι ℂ E) (ω : ι → ℂ)
    (hω : ∀ j, ω j * conj (ω j) = 1) (u : ι ⊕ ι → ℝ) :
    (b.rotatedRealCoords ω hω).symm u = ∑ j, (ω j * ⟨u (Sum.inl j), u (Sum.inr j)⟩) • b j := by
  rfl

end OrthonormalBasis
