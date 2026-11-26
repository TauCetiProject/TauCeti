/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Transvection
public import TauCeti.Analysis.PDE.Ellipticity.Basic
import TauCeti.Analysis.InnerProductSpace.Reflection

/-!
# The conormal shear vector of a matrix

For a matrix `A` and a normal `ν` with `⟪ν, A ν⟫ ≠ 0`, the conormal shear vector
`s = A ν / ⟪ν, A ν⟫ - ν / ‖ν‖²` is orthogonal to `ν`, and the shear `x ↦ x - ⟪s, x⟫ ν` makes
the form `(ξ, η) ↦ ξᵀ A η` of a symmetric `A` invariant under the reflection in `ν⊥`. For an
elliptic matrix with constants `λ, Λ`, `‖ν‖ ‖s‖ ≤ Λ / λ`.

This is the change of variables that reduces boundary estimates for a constant symmetric matrix
at a flat boundary to the case of a matrix compatible with the odd reflection.

## Main declarations

* `TauCeti.PDE.conormalShearVector`: the conormal shear vector `A ν / ⟪ν, A ν⟫ - ν / ‖ν‖²`.
* `TauCeti.PDE.inner_conormalShearVector_self`: it is orthogonal to `ν`.
* `TauCeti.PDE.norm_mul_norm_conormalShearVector_le`: for elliptic `A`, `‖ν‖ ‖s‖ ≤ Λ / λ`.
* `TauCeti.PDE.matrixBilinearForm_transvectionL_conormalShearVector_reflection`: for symmetric
  `A`, the sheared form is invariant under the reflection in `ν⊥`.
-/

public section

noncomputable section

open InnerProductSpace Matrix

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **conormal shear vector** of a matrix `A` and a normal `ν`:
`s = A ν / ⟪ν, A ν⟫ - ν / ‖ν‖²`. It is orthogonal to `ν`, and the shear along it carries the
conormal direction `A ν` to a multiple of `ν`. -/
def conormalShearVector (A : Matrix ι ι ℝ) (ν : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (matrixBilinearForm A ν ν)⁻¹ • toEuclideanCLM (𝕜 := ℝ) A ν - (‖ν‖ ^ 2)⁻¹ • ν

/-- The inner product with the conormal shear vector:
`⟪s, x⟫ = xᵀ A ν / νᵀ A ν - ⟪ν, x⟫ / ‖ν‖²`. -/
theorem inner_conormalShearVector (A : Matrix ι ι ℝ) (ν x : EuclideanSpace ℝ ι) :
    ⟪conormalShearVector A ν, x⟫_ℝ =
      (matrixBilinearForm A ν ν)⁻¹ * matrixBilinearForm A x ν - (‖ν‖ ^ 2)⁻¹ * ⟪ν, x⟫_ℝ := by
  rw [conormalShearVector, inner_sub_left, inner_smul_left, inner_smul_left, RCLike.conj_to_real,
    RCLike.conj_to_real, real_inner_comm, inner_toEuclideanCLM, matrixBilinearForm_apply,
    matrixBilinearForm_apply]

/-- For `ν ≠ 0` and `νᵀ A ν ≠ 0`, the conormal shear vector is orthogonal to `ν`. -/
theorem inner_conormalShearVector_self {A : Matrix ι ι ℝ} {ν : EuclideanSpace ℝ ι}
    (hν : ν ≠ 0) (hq : matrixBilinearForm A ν ν ≠ 0) :
    ⟪ν, conormalShearVector A ν⟫_ℝ = 0 := by
  rw [real_inner_comm, inner_conormalShearVector, real_inner_self_eq_norm_sq,
    inv_mul_cancel₀ hq, inv_mul_cancel₀ (by positivity), sub_self]

/-- For `λ ‖ξ‖² ≤ ξᵀ A ξ` and `|ηᵀ A ξ| ≤ Λ ‖η‖ ‖ξ‖` with `λ > 0`, the conormal shear vector
`s` of `A` and `ν ≠ 0` satisfies `‖ν‖ ‖s‖ ≤ Λ / λ`. -/
theorem norm_mul_norm_conormalShearVector_le {A : Matrix ι ι ℝ} {ν : EuclideanSpace ℝ ι}
    {lam Lam : ℝ} (hlam : 0 < lam) (hν : ν ≠ 0)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ η ξ : EuclideanSpace ℝ ι, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖) :
    ‖ν‖ * ‖conormalShearVector A ν‖ ≤ Lam / lam := by
  set s := conormalShearVector A ν
  have hν' : 0 < ‖ν‖ := norm_pos_iff.2 hν
  have hq : lam * ‖ν‖ ^ 2 ≤ matrixBilinearForm A ν ν := by
    simpa [matrixBilinearForm_apply, toQuadraticForm'_apply] using hA ν
  have hq0 : 0 < matrixBilinearForm A ν ν := lt_of_lt_of_le (by positivity) hq
  -- `‖s‖² β(ν, ν) = β(s, ν)`, since `s ⊥ ν`.
  have hss : ‖s‖ ^ 2 * matrixBilinearForm A ν ν = matrixBilinearForm A s ν := by
    have hsν : ⟪ν, s⟫_ℝ = 0 := inner_conormalShearVector_self hν hq0.ne'
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => rw [inner_conormalShearVector]
    rw [hsν, mul_zero, sub_zero]
    field_simp
  have hβ : matrixBilinearForm A s ν ≤ Lam * ‖s‖ * ‖ν‖ := by
    rw [matrixBilinearForm_apply]
    exact (le_abs_self _).trans (hA' s ν)
  have h1 : ‖s‖ * (‖s‖ * (lam * ‖ν‖ ^ 2)) ≤ ‖s‖ * (Lam * ‖ν‖) := by
    calc ‖s‖ * (‖s‖ * (lam * ‖ν‖ ^ 2)) ≤ ‖s‖ ^ 2 * matrixBilinearForm A ν ν := by
          rw [← mul_assoc, ← sq]; exact mul_le_mul_of_nonneg_left hq (sq_nonneg _)
      _ ≤ ‖s‖ * (Lam * ‖ν‖) := by rw [hss]; linarith
  have hLam : 0 ≤ Lam := by nlinarith [(abs_nonneg _).trans (hA' ν ν), mul_pos hν' hν']
  rcases eq_or_lt_of_le (norm_nonneg s) with hs | hs
  · rw [← hs, mul_zero]; exact div_nonneg hLam hlam.le
  have h2 : ‖s‖ * (lam * ‖ν‖ ^ 2) ≤ Lam * ‖ν‖ := le_of_mul_le_mul_left h1 hs
  rw [le_div_iff₀ hlam]
  nlinarith [h2, hν']

/-- **The sheared form is invariant under the reflection.** For symmetric `A` with `⟪ν, A ν⟫ ≠ 0`
and `M x = x - ⟪s, x⟫ ν`, `s` the conormal shear vector, the form `(ξ, η) ↦ ⟪M ξ, A M η⟫` is
invariant under the reflection `R` in `ν⊥`. -/
theorem matrixBilinearForm_transvectionL_conormalShearVector_reflection {A : Matrix ι ι ℝ}
    {ν : EuclideanSpace ℝ ι} (hν : ν ≠ 0) (hq : matrixBilinearForm A ν ν ≠ 0)
    (hAs : ∀ η ξ : EuclideanSpace ℝ ι, matrixBilinearForm A η ξ = matrixBilinearForm A ξ η)
    (ξ η : EuclideanSpace ℝ ι) :
    matrixBilinearForm A (transvectionL (conormalShearVector A ν) (-ν) ((ℝ ∙ ν)ᗮ.reflection ξ))
        (transvectionL (conormalShearVector A ν) (-ν) ((ℝ ∙ ν)ᗮ.reflection η)) =
      matrixBilinearForm A (transvectionL (conormalShearVector A ν) (-ν) ξ)
        (transvectionL (conormalShearVector A ν) (-ν) η) := by
  have hsν : ⟪conormalShearVector A ν, ν⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact inner_conormalShearVector_self hν hq
  have : ‖ν‖ ^ 2 ≠ 0 := by positivity
  have hM : ∀ x, transvectionL (conormalShearVector A ν) (-ν) x =
      x - ⟪conormalShearVector A ν, x⟫_ℝ • ν := fun x => by
    rw [transvectionL_apply, smul_neg, sub_eq_add_neg]
  simp only [hM, reflection_orthogonal_singleton_apply_div_norm_sq, map_sub, map_smul,
    sub_apply, smul_apply, inner_sub_right,
    inner_smul_right, hsν, smul_eq_mul, inner_conormalShearVector]
  rw [hAs ν η]
  field_simp
  ring

end PDE

end TauCeti
