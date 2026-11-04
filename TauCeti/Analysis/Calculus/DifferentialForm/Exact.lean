/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The differential one-form of a real-valued function

For a function `f : V → ℝ` on a real normed space, its Fréchet differential defines a one-form
`df` on `V`, which is the exterior derivative of `f` viewed as a zero-form. This file proves
that `df` is closed at every point where the second derivative of `f` exists and is symmetric,
a pointwise statement under weaker hypotheses than the `C²` condition used by Mathlib's
`extDeriv_extDeriv_apply`.

## Main declarations

* `TauCeti.differentialOneForm`: the one-form associated to the Fréchet differential of a
  real-valued function.
* `TauCeti.differentialOneForm_eq_extDeriv`: this one-form is the exterior derivative of the
  associated zero-form.
* `TauCeti.extDeriv_differentialOneForm_apply_eq_zero`: the differential one-form is closed
  wherever the second derivative exists and is symmetric.
-/

public section

open ContinuousAlternatingMap

noncomputable section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The one-form `df` associated to the Fréchet differential of a function `f : V → ℝ`. -/
def differentialOneForm (f : V → ℝ) : V → V [⋀^Fin 1]→L[ℝ] ℝ :=
  fun x ↦ ofSubsingletonLIE (0 : Fin 1) (fderiv ℝ f x)

/-- Evaluating the one-form `df` on a vector agrees with evaluating the Fréchet differential. -/
@[simp]
lemma differentialOneForm_apply (f : V → ℝ) (x v : V) :
    differentialOneForm f x (fun _ ↦ v) = fderiv ℝ f x v := by
  simp [differentialOneForm]

/-- The one-form `df` is the exterior derivative of the zero-form associated to `f`. -/
lemma differentialOneForm_eq_extDeriv (f : V → ℝ) :
    differentialOneForm f =
      extDeriv (fun x ↦ constOfIsEmpty ℝ V (Fin 0) (f x)) := by
  funext x
  rw [extDeriv_constOfIsEmpty]
  simp [differentialOneForm]

/-- The differential one-form is differentiable at `x` when the derivative of `f` is. -/
lemma differentiableAt_differentialOneForm {f : V → ℝ} {x : V}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    DifferentiableAt ℝ (differentialOneForm f) x :=
  (ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ) (0 : Fin 1)).differentiableAt.comp x hf

/-- The exterior derivative of `df` vanishes at every point where the derivative of `df` exists
and is symmetric. -/
lemma extDeriv_differentialOneForm_apply_eq_zero {f : V → ℝ} {x : V}
    (hdf : DifferentiableAt ℝ (fderiv ℝ f) x) (hf : IsSymmSndFDerivAt ℝ f x) :
    extDeriv (differentialOneForm f) x = 0 := by
  ext v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [hv, extDeriv_apply_pair]
  simp only [← fderiv_continuousAlternatingMap_apply_const_apply
    (differentiableAt_differentialOneForm hdf), differentialOneForm_apply]
  rw [fderiv_clm_apply hdf (differentiableAt_const (v 1)),
    fderiv_clm_apply hdf (differentiableAt_const (v 0))]
  simp [hf.eq (v 0) (v 1)]

/-- If `f` is `C^n` and `m + 1 ≤ n`, then its differential one-form is `C^m`. -/
lemma contDiff_differentialOneForm {f : V → ℝ} {m n : WithTop ℕ∞}
    (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (differentialOneForm f) :=
  (ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ) (0 : Fin 1)).contDiff.comp
    (hf.fderiv_right hmn)

/-- The one-form `df` of a `C²` function is closed. -/
lemma extDeriv_differentialOneForm_eq_zero {f : V → ℝ} (hf : ContDiff ℝ 2 f) :
    extDeriv (differentialOneForm f) = 0 := by
  funext x
  exact extDeriv_differentialOneForm_apply_eq_zero
    ((hf.fderiv_right le_rfl).differentiable one_ne_zero x)
    (hf.contDiffAt.isSymmSndFDerivAt (by simp))

end TauCeti

end
