/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.Forcing

/-!
# Checks for the forcing maps

On `V = H = ℂ` with `j = id` and the form `a(u, v) = conj(u) v`, the `H`-forcing map `S` is the
identity and the dual-forcing map `F` is `ℓ ↦ conj(ℓ 1)`. Scaling `ℓ` by `i` scales `F ℓ` by `-i`,
so `F` is conjugate linear, while `S (i h) = i S h`, so `S` is linear.

On `ℝ²` with `a = diag(1, 2)`, `F ℓ = (ℓ e₁, ℓ e₂ / 2)`. The constant `c = 1` is a coercivity
constant, so `‖F ℓ‖ ≤ c⁻¹ ‖ℓ‖` holds with `c = 1`; with `c = 2` the bound fails for `ℓ = e₁*`,
and `2` is not a coercivity constant. The zero form on `ℝ` is not coercive, so it is not a
`CoerciveHermitianForm`; its energy `q(u) = a(u, u)` vanishes at `u = 1 ≠ 0`, so its energy space
is not a normed space; and `0 = ℓ v` for all `v` has no solution when `ℓ ≠ 0`.
-/

public section

noncomputable section

open ComplexConjugate

namespace TauCeti.ForcingExamples

/-- The form `a(u, v) = conj(u) v` on `ℂ`, as a coercive Hermitian form. -/
def complexInnerForm : CoerciveHermitianForm ℂ ℂ where
  form := innerSL ℂ
  form_apply_eq_star u v := by simp [mul_comm]
  exists_coercive := ⟨1, one_pos, fun u ↦ by simp [← Complex.ofReal_pow]⟩

/-- The values of the form `a(u, v) = conj(u) v`. -/
@[simp]
theorem complexInnerForm_form_apply (u v : ℂ) : complexInnerForm.form u v = conj u * v := by
  simp [complexInnerForm, mul_comm]

/-- The `H`-forcing map of `conj(u) v` along the identity is the identity: `S₀ h = h`. -/
example (h : ℂ) : complexInnerForm.hForcing (ContinuousLinearMap.id ℂ ℂ) h = h := by
  refine ((complexInnerForm.eq_hForcing_iff _).2 fun v ↦ ?_).symm
  simp [mul_comm]

/-- The dual-forcing map of `conj(u) v` is `F₀ ℓ = conj(ℓ 1)`. -/
example (ℓ : StrongDual ℂ ℂ) : complexInnerForm.dualForcing ℓ = conj (ℓ 1) := by
  refine (complexInnerForm.eq_dualForcing_iff.2 fun v ↦ ?_).symm
  rw [complexInnerForm_form_apply, Complex.conj_conj]
  simpa [mul_comm] using (map_smul ℓ v 1).symm

/-- The dual-forcing map is conjugate linear: `F₀ (i ℓ) = -i F₀ ℓ`. -/
example (ℓ : StrongDual ℂ ℂ) :
    complexInnerForm.dualForcing (Complex.I • ℓ) = -Complex.I • complexInnerForm.dualForcing ℓ := by
  rw [map_smulₛₗ, Complex.conj_I]

/-- The `H`-forcing map is linear: `S₀ (i h) = i S₀ h`. -/
example (h : ℂ) :
    complexInnerForm.hForcing (ContinuousLinearMap.id ℂ ℂ) (Complex.I • h) =
      Complex.I • complexInnerForm.hForcing (ContinuousLinearMap.id ℂ ℂ) h :=
  map_smul _ _ _

/-! ### `diag(1, 2)` on `ℝ²` and the zero form -/

/-- The weight `v ↦ v + v₂ e₂`, that is `diag(1, 2)`, on `ℝ²`. -/
def diagOneTwo : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearMap.id ℝ _ + (EuclideanSpace.proj 1).smulRight (EuclideanSpace.single 1 1)

/-- The values of the weight `diag(1, 2)`. -/
theorem diagOneTwo_apply (v : EuclideanSpace ℝ (Fin 2)) :
    diagOneTwo v = v + v 1 • EuclideanSpace.single 1 1 := by
  simp [diagOneTwo]

/-- The inner products `⟪u, diag(1, 2) v⟫ = u₁ v₁ + 2 u₂ v₂`. -/
theorem inner_diagOneTwo (u v : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ u (diagOneTwo v) = u 0 * v 0 + 2 * (u 1 * v 1) := by
  simp [diagOneTwo_apply, inner_add_right, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The weight `diag(1, 2)` is coercive with constant `1`: `1 * ‖u‖² ≤ re ⟪u, diag(1, 2) u⟫`,
in the shape of the coercivity field of `CoerciveHermitianForm`. -/
theorem one_mul_norm_sq_le_re_inner_diagOneTwo (u : EuclideanSpace ℝ (Fin 2)) :
    1 * ‖u‖ ^ 2 ≤ RCLike.re (inner ℝ u (diagOneTwo u)) := by
  rw [one_mul, RCLike.re_to_real, inner_diagOneTwo, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_two]
  nlinarith [sq_nonneg (u 1)]

/-- The form `a(u, v) = u₁ v₁ + 2 u₂ v₂` on `ℝ²`, that is `⟪u, diag(1, 2) v⟫`, as a coercive
Hermitian form with coercivity constant `1`. -/
def diagOneTwoForm : CoerciveHermitianForm ℝ (EuclideanSpace ℝ (Fin 2)) where
  form := ContinuousLinearMap.toSesqForm diagOneTwo
  form_apply_eq_star u v := by simp [inner_diagOneTwo, mul_comm]
  exists_coercive := ⟨1, one_pos, fun u ↦ by simpa using one_mul_norm_sq_le_re_inner_diagOneTwo u⟩

/-- The values of the form `diag(1, 2)`. -/
@[simp]
theorem diagOneTwoForm_form_apply (u v : EuclideanSpace ℝ (Fin 2)) :
    diagOneTwoForm.form u v = u 0 * v 0 + 2 * (u 1 * v 1) := by
  simp [diagOneTwoForm, inner_diagOneTwo]

/-- The form `diag(1, 2)` is coercive with constant `1`: `1 * ‖u‖² ≤ re a(u, u)`. -/
theorem one_mul_norm_sq_le_re_diagOneTwoForm_form (u : EuclideanSpace ℝ (Fin 2)) :
    1 * ‖u‖ ^ 2 ≤ RCLike.re (diagOneTwoForm.form u u) := by
  simpa [inner_diagOneTwo] using one_mul_norm_sq_le_re_inner_diagOneTwo u

/-- The dual-forcing map of `diag(1, 2)` is `F ℓ = (ℓ e₁, ℓ e₂ / 2)`. -/
theorem diagOneTwoForm_dualForcing_apply (ℓ : StrongDual ℝ (EuclideanSpace ℝ (Fin 2))) :
    diagOneTwoForm.dualForcing ℓ =
      !₂[ℓ (EuclideanSpace.single 0 1), ℓ (EuclideanSpace.single 1 1) / 2] := by
  refine (diagOneTwoForm.eq_dualForcing_iff.2 fun v ↦ ?_).symm
  have hv : v = v 0 • EuclideanSpace.single 0 1 + v 1 • EuclideanSpace.single 1 1 := by
    ext i
    fin_cases i <;> simp
  conv_rhs => rw [hv]
  simp only [diagOneTwoForm_form_apply, map_add, map_smul, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- The bound `‖F ℓ‖ ≤ c⁻¹ ‖ℓ‖` with `c = 1`, which is a coercivity constant of `diag(1, 2)`. -/
example (ℓ : StrongDual ℝ (EuclideanSpace ℝ (Fin 2))) :
    ‖diagOneTwoForm.dualForcing ℓ‖ ≤ 1⁻¹ * ‖ℓ‖ :=
  diagOneTwoForm.norm_dualForcing_le one_pos one_mul_norm_sq_le_re_diagOneTwoForm_form ℓ

/-- With `c = 2` the bound fails for `ℓ = e₁*`: `F e₁* = e₁` has norm `1 > 2⁻¹ ‖e₁*‖`. -/
example :
    ¬ ‖diagOneTwoForm.dualForcing (innerSL ℝ (EuclideanSpace.single 0 1))‖ ≤
      2⁻¹ * ‖innerSL ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))‖ := by
  rw [diagOneTwoForm_dualForcing_apply, innerSL_apply_norm]
  norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two, EuclideanSpace.inner_single_left]

/-- `c = 2` is not a coercivity constant of `diag(1, 2)`: `q(e₁) = 1 < 2 ‖e₁‖²`. -/
example :
    ¬ ∀ u : EuclideanSpace ℝ (Fin 2), 2 * ‖u‖ ^ 2 ≤ RCLike.re (diagOneTwoForm.form u u) := by
  intro h
  have := h (EuclideanSpace.single 0 1)
  norm_num at this

/-- The zero form on `ℝ` is not coercive, so it is not a `CoerciveHermitianForm` and has no energy
space. -/
example : ¬ ∃ c > 0, ∀ u : ℝ, c * ‖u‖ ^ 2 ≤ RCLike.re ((0 : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) u u) := by
  rintro ⟨c, hc, h⟩
  have := h 1
  norm_num at this
  linarith

/-- The energy `q(u) = a(u, u)` of the zero form on `ℝ` vanishes at `u = 1 ≠ 0`, so `√q` is not
a norm and the energy space of the zero form is not a normed space. -/
example : ∃ u : ℝ, u ≠ 0 ∧ (0 : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) u u = 0 :=
  ⟨1, one_ne_zero, by simp⟩

/-- For the zero form on `ℝ` the weak equation `0 = ℓ v` has no solution when `ℓ ≠ 0`. -/
example {ℓ : StrongDual ℝ ℝ} (hℓ : ℓ ≠ 0) :
    ¬ ∃ u : ℝ, ∀ v, (0 : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) u v = ℓ v := by
  rintro ⟨u, hu⟩
  exact hℓ (ContinuousLinearMap.ext fun v ↦ by simpa using (hu v).symm)

end TauCeti.ForcingExamples
