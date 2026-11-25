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
  rw [complexInnerForm_form_apply, Complex.conj_conj, mul_comm, ← smul_eq_mul, ← map_smul,
    smul_eq_mul, mul_one]

/-- The dual-forcing map is conjugate linear: `F₀ (i ℓ) = -i F₀ ℓ`. -/
example (ℓ : StrongDual ℂ ℂ) :
    complexInnerForm.dualForcing (Complex.I • ℓ) = -Complex.I • complexInnerForm.dualForcing ℓ := by
  rw [map_smulₛₗ, Complex.conj_I]

/-- The `H`-forcing map is linear: `S₀ (i h) = i S₀ h`. -/
example (h : ℂ) :
    complexInnerForm.hForcing (ContinuousLinearMap.id ℂ ℂ) (Complex.I • h) =
      Complex.I • complexInnerForm.hForcing (ContinuousLinearMap.id ℂ ℂ) h :=
  map_smul _ _ _

end TauCeti.ForcingExamples
