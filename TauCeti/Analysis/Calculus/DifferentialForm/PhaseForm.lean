/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Calculus.DifferentialForm.Basic

/-!
# The phase form of a complex function

For a differentiable function `α : E → ℂ` on a real normed space, the **phase form**
`Im (α⁻¹ dα)` is a real one-form. Away from the zeros of `α` it is the differential of a local
branch of `arg α`. This file proves that it is as regular as `dα` away from the zeros of `α`
(`TauCeti.contDiffAt_phaseForm`), that it is closed there (`TauCeti.extDeriv_phaseForm`), and
that it is additive under products (`TauCeti.phaseForm_mul`).

## Main definitions

* `TauCeti.phaseForm α`: the one-form `Im (α⁻¹ dα)`.
-/

public section

noncomputable section

open ContinuousAlternatingMap Complex

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α u : E → ℂ} {x : E}

/-- The phase form `Im (α⁻¹ dα)` of a complex function `α`. Away from the zeros of `α` it is the
differential of a local branch of `arg α`; at a zero of `α` it is `0`. -/
def phaseForm (α : E → ℂ) (x : E) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  ofSubsingletonLIE (0 : Fin 1) (imCLM.comp ((α x)⁻¹ • fderiv ℝ α x))

/-- The phase form evaluated on a vector. -/
@[simp]
theorem phaseForm_apply (α : E → ℂ) (x : E) (v : Fin 1 → E) :
    phaseForm α x v = ((α x)⁻¹ * fderiv ℝ α x (v 0)).im := by
  simp [phaseForm]

/-- The phase form vanishes at a zero of `α`. -/
@[simp]
theorem phaseForm_of_eq_zero (h : α x = 0) : phaseForm α x = 0 := by
  ext v
  simp [h]

/-- The continuous linear map `L ↦ Im ∘ L`, with values in one-forms. -/
private def imOneForm : (E →L[ℝ] ℂ) →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ :=
  (ofSubsingletonLIE (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    ContinuousLinearMap.compL ℝ E ℂ ℝ imCLM

/-- The phase form is `imOneForm` applied to `α⁻¹ dα`. -/
private theorem phaseForm_eq_imOneForm (α : E → ℂ) :
    phaseForm α = fun y ↦ imOneForm ((α y)⁻¹ • fderiv ℝ α y) := by
  funext y
  ext v
  simp [imOneForm]

/-- The phase form of a `C^m` function is `C^n` away from its zeros, for `n + 1 ≤ m`. -/
theorem contDiffAt_phaseForm {m n : WithTop ℕ∞} (hα : ContDiffAt ℝ m α x) (h : α x ≠ 0)
    (hnm : n + 1 ≤ m) : ContDiffAt ℝ n (phaseForm α) x := by
  rw [phaseForm_eq_imOneForm]
  exact imOneForm.contDiff.contDiffAt.comp x
    (((hα.of_le (le_self_add.trans hnm)).fun_inv h).fun_smul (hα.fderiv_right hnm))

/-- The phase form is closed away from the zeros of a `C²` function: `d Im (α⁻¹ dα) = 0`. -/
theorem extDeriv_phaseForm (hα : ContDiffAt ℝ 2 α x) (h : α x ≠ 0) :
    extDeriv (phaseForm α) x = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ α) x :=
    (hα.fderiv_right le_rfl).differentiableAt one_ne_zero
  have hsymm := hα.isSymmSndFDerivAt (by simp)
  have hinv : HasFDerivAt (fun y ↦ (α y)⁻¹)
      ((-ContinuousLinearMap.mulLeftRight ℝ ℂ (α x)⁻¹ (α x)⁻¹).comp (fderiv ℝ α x)) x :=
    (hasFDerivAt_inv' h).comp x (hα.differentiableAt (by simp)).hasFDerivAt
  have hφ : HasFDerivAt (phaseForm α) (imOneForm.comp ((α x)⁻¹ • fderiv ℝ (fderiv ℝ α) x +
      ((-ContinuousLinearMap.mulLeftRight ℝ ℂ (α x)⁻¹ (α x)⁻¹).comp
        (fderiv ℝ α x)).smulRight (fderiv ℝ α x))) x := by
    rw [phaseForm_eq_imOneForm]
    exact imOneForm.hasFDerivAt.comp x (hinv.smul hd.hasFDerivAt)
  ext v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, extDeriv_apply_pair, hφ.fderiv]
  simp only [imOneForm, ContinuousLinearMap.comp_apply, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    _root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ofSubsingletonLIE_apply, ofSubsingleton_apply_apply, ContinuousLinearMap.compL_apply,
    imCLM_apply, smul_eq_mul, hsymm.eq (v 0) (v 1)]
  -- The `α⁻¹ d²α` terms cancel by the symmetry of `d²α`, and so do the `-α⁻² dα ⊗ dα` terms.
  rw [← sub_im, coe_zero, Pi.zero_apply]
  convert zero_im using 2
  ring

/-- The phase form of a product of functions that do not vanish at `x` is the sum of their
phase forms. -/
theorem phaseForm_mul (hu : DifferentiableAt ℝ u x) (hα : DifferentiableAt ℝ α x)
    (hu₀ : u x ≠ 0) (hα₀ : α x ≠ 0) :
    phaseForm (u * α) x = phaseForm u x + phaseForm α x := by
  ext v
  simp only [phaseForm_apply, Pi.mul_apply, ContinuousAlternatingMap.add_apply,
    fderiv_mul hu hα, _root_.add_apply, _root_.smul_apply, smul_eq_mul, ← add_im]
  congr 1
  field_simp
  ring

end TauCeti
