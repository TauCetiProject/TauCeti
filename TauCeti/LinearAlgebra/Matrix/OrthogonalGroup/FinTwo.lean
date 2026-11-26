/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Unitary

/-!
# Orthogonal `2 × 2` matrices

The first column `(a, b)` of an orthogonal `2 × 2` matrix is a unit vector orthogonal to the
second column. A rotation, of determinant `1`, is `!![a, -b; b, a]`, and a reflection, of
determinant `-1`, is `!![a, b; b, -a]`.

For `g ∈ O(2)` over `ℝ`, the **phase** `z(g) = a - i b` is a complex number of absolute value one
and the **sign** `ε(g) = det g = ±1` is an integer. The rotation `r_θ = exp(θJ)`,
`J = !![0, 1; -1, 0]`, has phase `e^{iθ}`, and the phase of a product is
`z(gh) = z(g) z(h) ^ ε(g)`. The complex matrix of a rotation of phase `a - i b` is
`!![a, -b; b, a]`.

## Main definitions

* `TauCeti.orthogonalPhase g`: the phase `z(g) = g₀₀ - i g₁₀` of `g ∈ O(2)`.
* `TauCeti.orthogonalSign g`: `det g = ±1`, as an integer.
* `TauCeti.orthogonalRotation θ`: the rotation `r_θ = exp(θJ)`, of phase `e^{iθ}`.

## Main results

* `Matrix.apply_one_one_of_mem_orthogonalGroup_fin_two_of_det_eq_one` and its siblings: the
  entry relations of rotations and reflections.
* `Matrix.eq_of_mem_orthogonalGroup_fin_two_of_det_eq_one`,
  `Matrix.eq_of_mem_orthogonalGroup_fin_two_of_det_eq_neg_one`: the normal forms of rotations and
  reflections.
* `TauCeti.orthogonalRotation_zero`, `TauCeti.orthogonalRotation_add`,
  `TauCeti.orthogonalRotation_inv`: the rotations form a one-parameter subgroup of `O(2)`.
* `TauCeti.orthogonalPhase_mul`: `z(gh) = z(g) z(h) ^ (det g)`.
* `TauCeti.orthogonalComplexMatrix_eq_of_det_eq_one`: the complex matrix of a rotation.
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R] {A : Matrix (Fin 2) (Fin 2) R}

/-- The first column of an orthogonal `2 × 2` matrix is a unit vector. -/
theorem sq_add_sq_of_mem_orthogonalGroup_fin_two (hA : A ∈ orthogonalGroup (Fin 2) R) :
    A 0 0 ^ 2 + A 1 0 ^ 2 = 1 := by
  simpa [dotProduct, Fin.sum_univ_two, sq] using col_dotProduct_col_of_mem_orthogonalGroup hA 0 0

/-- The first column of a real orthogonal `2 × 2` matrix is a unit vector, as complex numbers. -/
theorem ofReal_sq_add_ofReal_sq_of_mem_orthogonalGroup_fin_two {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A ∈ orthogonalGroup (Fin 2) ℝ) : (A 0 0 : ℂ) ^ 2 + (A 1 0 : ℂ) ^ 2 = 1 := by
  exact_mod_cast sq_add_sq_of_mem_orthogonalGroup_fin_two hA

/-- The two columns of an orthogonal `2 × 2` matrix are orthogonal. -/
theorem mul_add_mul_of_mem_orthogonalGroup_fin_two (hA : A ∈ orthogonalGroup (Fin 2) R) :
    A 0 0 * A 0 1 + A 1 0 * A 1 1 = 0 := by
  simpa [dotProduct, Fin.sum_univ_two] using col_dotProduct_col_of_mem_orthogonalGroup hA 0 1

/-- The `(1, 1)` entry of an orthogonal `2 × 2` matrix of determinant `1` is its `(0, 0)` entry. -/
theorem apply_one_one_of_mem_orthogonalGroup_fin_two_of_det_eq_one
    (hA : A ∈ orthogonalGroup (Fin 2) R) (hdet : A.det = 1) : A 1 1 = A 0 0 :=
  (mem_specialOrthogonalGroup_fin_two_iff.1 ((mem_specialOrthogonalGroup_iff).2 ⟨hA, hdet⟩)).1.symm

/-- The `(0, 1)` entry of an orthogonal `2 × 2` matrix of determinant `1` is minus its `(1, 0)`
entry. -/
theorem apply_zero_one_of_mem_orthogonalGroup_fin_two_of_det_eq_one
    (hA : A ∈ orthogonalGroup (Fin 2) R) (hdet : A.det = 1) : A 0 1 = -A 1 0 :=
  (mem_specialOrthogonalGroup_fin_two_iff.1 ((mem_specialOrthogonalGroup_iff).2 ⟨hA, hdet⟩)).2.1

/-- The `(1, 1)` entry of an orthogonal `2 × 2` matrix of determinant `-1` is minus its `(0, 0)`
entry. -/
theorem apply_one_one_of_mem_orthogonalGroup_fin_two_of_det_eq_neg_one
    (hA : A ∈ orthogonalGroup (Fin 2) R) (hdet : A.det = -1) : A 1 1 = -A 0 0 := by
  have h₀ := sq_add_sq_of_mem_orthogonalGroup_fin_two hA
  have h₁ := mul_add_mul_of_mem_orthogonalGroup_fin_two hA
  rw [det_fin_two] at hdet
  linear_combination A 1 0 * h₁ + A 0 0 * hdet - A 1 1 * h₀

/-- The `(0, 1)` entry of an orthogonal `2 × 2` matrix of determinant `-1` is its `(1, 0)`
entry. -/
theorem apply_zero_one_of_mem_orthogonalGroup_fin_two_of_det_eq_neg_one
    (hA : A ∈ orthogonalGroup (Fin 2) R) (hdet : A.det = -1) : A 0 1 = A 1 0 := by
  have h₀ := sq_add_sq_of_mem_orthogonalGroup_fin_two hA
  have h₁ := mul_add_mul_of_mem_orthogonalGroup_fin_two hA
  rw [det_fin_two] at hdet
  linear_combination A 0 0 * h₁ - A 1 0 * hdet - A 0 1 * h₀

/-- An orthogonal `2 × 2` matrix of determinant `1` is a rotation `!![a, -b; b, a]`. -/
theorem eq_of_mem_orthogonalGroup_fin_two_of_det_eq_one (hA : A ∈ orthogonalGroup (Fin 2) R)
    (hdet : A.det = 1) : A = !![A 0 0, -A 1 0; A 1 0, A 0 0] :=
  (eta_fin_two A).trans (by
    rw [apply_one_one_of_mem_orthogonalGroup_fin_two_of_det_eq_one hA hdet,
      apply_zero_one_of_mem_orthogonalGroup_fin_two_of_det_eq_one hA hdet])

/-- An orthogonal `2 × 2` matrix of determinant `-1` is a reflection `!![a, b; b, -a]`. -/
theorem eq_of_mem_orthogonalGroup_fin_two_of_det_eq_neg_one (hA : A ∈ orthogonalGroup (Fin 2) R)
    (hdet : A.det = -1) : A = !![A 0 0, A 1 0; A 1 0, -A 0 0] :=
  (eta_fin_two A).trans (by
    rw [apply_one_one_of_mem_orthogonalGroup_fin_two_of_det_eq_neg_one hA hdet,
      apply_zero_one_of_mem_orthogonalGroup_fin_two_of_det_eq_neg_one hA hdet])

end Matrix

noncomputable section

open Complex Matrix

namespace TauCeti

/-- The **phase** `z(g) = g₀₀ - i g₁₀` of `g ∈ O(2)`: a rotation `!![a, -b; b, a]` has phase
`a - i b`, so the rotation `r_θ = exp(θJ)` has phase `e^{iθ}`; a reflection `r_θ A` has the phase
of `r_θ`. -/
def orthogonalPhase (g : orthogonalGroup (Fin 2) ℝ) : ℂ :=
  ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) - I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ)

/-- The phase in matrix entries. -/
theorem orthogonalPhase_def (g : orthogonalGroup (Fin 2) ℝ) :
    orthogonalPhase g =
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) - I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) :=
  (rfl)

/-- The complex matrix of a rotation `g ∈ O(2)`, `det g = 1`, is `!![a, -b; b, a]`. -/
theorem orthogonalComplexMatrix_eq_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) :
    (orthogonalComplexMatrix g : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ), -((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ);
        ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ), ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [apply_zero_one_of_mem_orthogonalGroup_fin_two_of_det_eq_one g.property hg,
      apply_one_one_of_mem_orthogonalGroup_fin_two_of_det_eq_one g.property hg]

/-- The phase of the identity is `1`. -/
@[simp]
theorem orthogonalPhase_one : orthogonalPhase 1 = 1 := by
  simp [orthogonalPhase_def]

/-- The complex conjugate of the phase is `g₀₀ + i g₁₀`. -/
theorem conj_orthogonalPhase (g : orthogonalGroup (Fin 2) ℝ) :
    starRingEnd ℂ (orthogonalPhase g) =
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) + I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) := by
  simp [orthogonalPhase_def]

/-- The phase has absolute value one: its product with its complex conjugate is `1`. -/
theorem orthogonalPhase_mul_conj (g : orthogonalGroup (Fin 2) ℝ) :
    orthogonalPhase g * starRingEnd ℂ (orthogonalPhase g) = 1 := by
  have h := ofReal_sq_add_ofReal_sq_of_mem_orthogonalGroup_fin_two g.property
  rw [conj_orthogonalPhase, orthogonalPhase_def]
  linear_combination h - ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) ^ 2 * I_sq

/-- The phase is nonzero. -/
theorem orthogonalPhase_ne_zero (g : orthogonalGroup (Fin 2) ℝ) : orthogonalPhase g ≠ 0 :=
  left_ne_zero_of_mul_eq_one (orthogonalPhase_mul_conj g)

/-- The inverse of the phase is `g₀₀ + i g₁₀`. -/
theorem inv_orthogonalPhase (g : orthogonalGroup (Fin 2) ℝ) :
    (orthogonalPhase g)⁻¹ =
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) + I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) := by
  rw [← conj_orthogonalPhase]
  exact inv_eq_of_mul_eq_one_right (orthogonalPhase_mul_conj g)

/-- The **sign** `det g = ±1` of `g ∈ O(2)`, as an integer: `1` for a rotation, `-1` for a
reflection. -/
def orthogonalSign (g : orthogonalGroup (Fin 2) ℝ) : ℤ :=
  if (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1 then 1 else -1

/-- The sign of a rotation is `1`. -/
theorem orthogonalSign_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) : orthogonalSign g = 1 := by
  simp [orthogonalSign, hg]

/-- The sign of a reflection is `-1`. -/
theorem orthogonalSign_of_det_eq_neg_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = -1) : orthogonalSign g = -1 := by
  norm_num [orthogonalSign, hg]

/-- The sign is `1` or `-1`. -/
theorem orthogonalSign_eq_one_or_neg_one (g : orthogonalGroup (Fin 2) ℝ) :
    orthogonalSign g = 1 ∨ orthogonalSign g = -1 := by
  unfold orthogonalSign
  split_ifs <;> simp

/-- The sign is the determinant. -/
theorem orthogonalSign_eq_det (g : orthogonalGroup (Fin 2) ℝ) :
    (orthogonalSign g : ℝ) = (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup g.property with hg | hg
  · rw [orthogonalSign_of_det_eq_one hg, hg, Int.cast_one]
  · rw [orthogonalSign_of_det_eq_neg_one hg, hg, Int.cast_neg, Int.cast_one]

/-- The sign squares to `1`. -/
theorem orthogonalSign_mul_self (g : orthogonalGroup (Fin 2) ℝ) :
    orthogonalSign g * orthogonalSign g = 1 := by
  unfold orthogonalSign
  split_ifs <;> norm_num

/-- Multiplying twice by the sign is the identity. -/
@[simp]
theorem orthogonalSign_mul_orthogonalSign_mul (g : orthogonalGroup (Fin 2) ℝ) (x : ℤ) :
    orthogonalSign g * (orthogonalSign g * x) = x := by
  rw [← mul_assoc, orthogonalSign_mul_self, one_mul]

/-- The sign is multiplicative. -/
theorem orthogonalSign_mul (g h : orthogonalGroup (Fin 2) ℝ) :
    orthogonalSign (g * h) = orthogonalSign g * orthogonalSign h := by
  have : ((orthogonalSign (g * h) : ℤ) : ℝ) = ((orthogonalSign g * orthogonalSign h : ℤ) : ℝ) := by
    rw [Int.cast_mul, orthogonalSign_eq_det, orthogonalSign_eq_det, orthogonalSign_eq_det,
      Submonoid.coe_mul, det_mul]
  exact_mod_cast this

/-- The sign of the identity is `1`. -/
@[simp]
theorem orthogonalSign_one : orthogonalSign 1 = 1 :=
  orthogonalSign_of_det_eq_one (by simp)

/-- The reflection `A = diag(1, -1)` has phase `1`. -/
@[simp]
theorem orthogonalPhase_orthogonalDiagonalReflection :
    orthogonalPhase (orthogonalDiagonalReflection ℝ 1) = 1 := by
  simp [orthogonalPhase_def]

/-- The reflection `A = diag(1, -1)` has sign `-1`. -/
@[simp]
theorem orthogonalSign_orthogonalDiagonalReflection :
    orthogonalSign (orthogonalDiagonalReflection ℝ 1) = -1 :=
  orthogonalSign_of_det_eq_neg_one (det_orthogonalDiagonalReflection ℝ 1)

/-- The **rotation** `r_θ = exp(θJ) = !![cos θ, sin θ; -sin θ, cos θ]` in `O(2)`, with
`J = !![0, 1; -1, 0]`. -/
def orthogonalRotation (θ : ℝ) : orthogonalGroup (Fin 2) ℝ :=
  ⟨!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ], by
    rw [mem_orthogonalGroup_iff]
    have h := Real.cos_sq_add_sin_sq θ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith⟩

/-- The matrix of the rotation `r_θ`. -/
@[simp]
theorem coe_orthogonalRotation (θ : ℝ) :
    (orthogonalRotation θ : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] :=
  (rfl)

/-- The rotation `r_θ` has determinant `1`. -/
theorem det_orthogonalRotation (θ : ℝ) :
    (orthogonalRotation θ : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  simp [det_fin_two, ← sq, Real.cos_sq_add_sin_sq]

/-- The rotation `r_θ` has sign `1`. -/
@[simp]
theorem orthogonalSign_orthogonalRotation (θ : ℝ) : orthogonalSign (orthogonalRotation θ) = 1 :=
  orthogonalSign_of_det_eq_one (det_orthogonalRotation θ)

/-- The rotation `r_θ` has phase `e^{iθ}`. -/
@[simp]
theorem orthogonalPhase_orthogonalRotation (θ : ℝ) :
    orthogonalPhase (orthogonalRotation θ) = exp (θ * I) := by
  simp [orthogonalPhase_def, exp_mul_I, mul_comm I]

/-- The rotation by the angle `0` is the identity. -/
@[simp]
theorem orthogonalRotation_zero : orthogonalRotation 0 = 1 :=
  Subtype.ext <| by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

-- Not `@[simp]`: the family form `orthogonalRotation θ` is the simp normal form, as for
-- `Matrix.SpecialLinearGroup.rotation_add`.
/-- The rotations form a one-parameter subgroup: `r_{θ + φ} = r_θ r_φ`. -/
theorem orthogonalRotation_add (θ φ : ℝ) :
    orthogonalRotation (θ + φ) = orthogonalRotation θ * orthogonalRotation φ :=
  Subtype.ext <| by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Real.cos_add, Real.sin_add, Matrix.mul_apply] <;> ring

/-- The inverse of `r_θ` is `r_{-θ}`. -/
@[simp]
theorem orthogonalRotation_inv (θ : ℝ) : (orthogonalRotation θ)⁻¹ = orthogonalRotation (-θ) :=
  inv_eq_of_mul_eq_one_right (by rw [← orthogonalRotation_add, add_neg_cancel,
    orthogonalRotation_zero])

/-- **The phase of a product**: `z(gh) = z(g) z(h) ^ (det g)`. Composing with a reflection
conjugates the phase of the second factor. -/
theorem orthogonalPhase_mul (g h : orthogonalGroup (Fin 2) ℝ) :
    orthogonalPhase (g * h) = orthogonalPhase g * orthogonalPhase h ^ orthogonalSign g := by
  have hgh : ∀ i, ((g * h : orthogonalGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i 0 =
      (g : Matrix (Fin 2) (Fin 2) ℝ) i 0 * (h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 +
        (g : Matrix (Fin 2) (Fin 2) ℝ) i 1 * (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := fun i ↦ by
    simp [Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup g.property with hg | hg
  · rw [orthogonalSign_of_det_eq_one hg, zpow_one, orthogonalPhase_def, orthogonalPhase_def,
      orthogonalPhase_def, hgh, hgh,
      apply_one_one_of_mem_orthogonalGroup_fin_two_of_det_eq_one g.property hg,
      apply_zero_one_of_mem_orthogonalGroup_fin_two_of_det_eq_one g.property hg]
    push_cast
    linear_combination -((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 :
      ℂ) * I_sq
  · rw [orthogonalSign_of_det_eq_neg_one hg, _root_.zpow_neg_one, inv_orthogonalPhase,
      orthogonalPhase_def, orthogonalPhase_def, hgh, hgh,
      apply_one_one_of_mem_orthogonalGroup_fin_two_of_det_eq_neg_one g.property hg,
      apply_zero_one_of_mem_orthogonalGroup_fin_two_of_det_eq_neg_one g.property hg]
    push_cast
    linear_combination ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 :
      ℂ) * I_sq

end TauCeti
