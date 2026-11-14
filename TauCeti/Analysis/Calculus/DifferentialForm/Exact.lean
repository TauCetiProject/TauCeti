/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The differential one-form of a function

For a function `f : V → F` between normed spaces over a nontrivially normed field `𝕜`, its
Fréchet differential defines an `F`-valued one-form `df` on `V`, which is the exterior derivative
of `f` viewed as a zero-form. This file proves that `df` is closed at every point where the
second derivative of `f` is symmetric, a pointwise statement under weaker hypotheses than the
`C²` condition (analyticity over fields other than `ℝ` and `ℂ`) used by Mathlib's
`extDeriv_extDeriv_apply`.

## Main declarations

* `TauCeti.differentialOneForm`: the one-form associated to the Fréchet differential of a
  function.
* `TauCeti.differentialOneForm_eq_extDeriv`: this one-form is the exterior derivative of the
  associated zero-form.
* `TauCeti.extDeriv_differentialOneForm_apply_eq_zero`: the differential one-form is closed
  wherever the second derivative of `f` is symmetric.
-/

public section

open ContinuousAlternatingMap

noncomputable section

namespace TauCeti

variable {𝕜 V F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜) in
/-- The one-form `df` associated to the Fréchet differential of a function `f : V → F`. -/
def differentialOneForm (f : V → F) : V → V [⋀^Fin 1]→L[𝕜] F :=
  fun x ↦ ofSubsingletonLIE (0 : Fin 1) (fderiv 𝕜 f x)

/-- The one-form `df` at `x` is the Fréchet differential of `f` at `x`, viewed as a one-form. -/
lemma differentialOneForm_def (f : V → F) :
    differentialOneForm 𝕜 f = fun x ↦ ofSubsingletonLIE (0 : Fin 1) (fderiv 𝕜 f x) :=
  (rfl)

/-- Evaluating the one-form `df` on a one-element family of vectors agrees with evaluating the
Fréchet differential on its only vector. -/
@[simp]
lemma differentialOneForm_apply (f : V → F) (x : V) (v : Fin 1 → V) :
    differentialOneForm 𝕜 f x v = fderiv 𝕜 f x (v 0) := by
  simp [differentialOneForm_def]

/-- The one-form `df` is the exterior derivative of the zero-form associated to `f`. -/
lemma differentialOneForm_eq_extDeriv (f : V → F) :
    differentialOneForm 𝕜 f =
      extDeriv (fun x ↦ constOfIsEmpty 𝕜 V (Fin 0) (f x)) := by
  funext x
  rw [extDeriv_constOfIsEmpty]
  simp [differentialOneForm_def]

/-- The differential one-form is differentiable at `x` exactly when the derivative of `f` is. -/
@[simp]
lemma differentiableAt_differentialOneForm_iff {f : V → F} {x : V} :
    DifferentiableAt 𝕜 (differentialOneForm 𝕜 f) x ↔ DifferentiableAt 𝕜 (fderiv 𝕜 f) x :=
  (ofSubsingletonLIE (𝕜 := 𝕜) (E := V) (F := F) (0 : Fin 1)).comp_differentiableAt_iff

/-- The derivative of `df` is the second derivative of `f`, transported along the identification
of continuous linear maps with one-forms. This holds whether or not `fderiv 𝕜 f` is
differentiable, since `df` is `fderiv 𝕜 f` composed with a linear isometry equivalence. -/
lemma fderiv_differentialOneForm (f : V → F) (x : V) :
    fderiv 𝕜 (differentialOneForm 𝕜 f) x =
      (ofSubsingletonLIE (𝕜 := 𝕜) (E := V) (F := F) (0 : Fin 1) : _ →L[𝕜] _).comp
        (fderiv 𝕜 (fderiv 𝕜 f) x) := by
  rw [differentialOneForm_def]
  exact LinearIsometryEquiv.comp_fderiv _

/-- The exterior derivative of `df` vanishes at every point where the second derivative of `f` is
symmetric; no differentiability of `df` is needed. -/
lemma extDeriv_differentialOneForm_apply_eq_zero {f : V → F} {x : V}
    (hf : IsSymmSndFDerivAt 𝕜 f x) :
    extDeriv (differentialOneForm 𝕜 f) x = 0 := by
  ext v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [hv, extDeriv_apply_pair, fderiv_differentialOneForm]
  simp [hf.eq (v 0) (v 1)]

/-- If `f` is `C^n` and `m + 1 ≤ n`, then its differential one-form is `C^m`. -/
lemma contDiff_differentialOneForm {f : V → F} {m n : WithTop ℕ∞}
    (hf : ContDiff 𝕜 n f) (hmn : m + 1 ≤ n) :
    ContDiff 𝕜 m (differentialOneForm 𝕜 f) :=
  (ofSubsingletonLIE (𝕜 := 𝕜) (E := V) (F := F) (0 : Fin 1)).contDiff.comp
    (hf.fderiv_right hmn)

/-- The one-form `df` of a `C^n` function is closed when `minSmoothness 𝕜 2 ≤ n`: over `ℝ` or `ℂ`
(more generally, an `IsRCLikeNormedField`) this asks for `f` to be `C²`, and over any other field
for `f` to be analytic. -/
lemma extDeriv_differentialOneForm_eq_zero {f : V → F} {n : WithTop ℕ∞} (hf : ContDiff 𝕜 n f)
    (hn : minSmoothness 𝕜 2 ≤ n) :
    extDeriv (differentialOneForm 𝕜 f) = 0 :=
  funext fun _ ↦ extDeriv_differentialOneForm_apply_eq_zero (hf.contDiffAt.isSymmSndFDerivAt hn)

end TauCeti

end
