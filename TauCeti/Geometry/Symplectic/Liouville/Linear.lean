/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# The radial primitive of a constant two-form

Every continuous bilinear form on a real normed space determines a linear one-form by
`λₓ(v) = B(x, v) / 2`. Its exterior derivative is one half of the alternatization of `B`; when
`B` is skew-symmetric, this says that the corresponding constant two-form is exact. This is the
explicit primitive for the constant model form in the local Darboux construction.

The coordinate calculation follows the convention for exterior derivatives in
`Mathlib.Analysis.Calculus.DifferentialForm.Basic` and parallels the evaluation calculation for the
cotangent Liouville form in `TauCeti/Geometry/Symplectic/Cotangent/Liouville.lean`.
-/

public section

open ContinuousAlternatingMap

noncomputable section

namespace ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The radial one-form associated to a continuous bilinear form `B`, given by
`λₓ(v) = B(x, v) / 2`. -/
def liouvilleFormCLM (B : V →L[ℝ] V →L[ℝ] ℝ) :
    V →L[ℝ] V [⋀^Fin 1]→L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp ((1 / 2 : ℝ) • B)

/-- The radial one-form evaluates by `λₓ(v) = B(x, v) / 2`. -/
@[simp]
lemma liouvilleFormCLM_apply (B : V →L[ℝ] V →L[ℝ] ℝ) (x : V) (v : Fin 1 → V) :
    liouvilleFormCLM B x v = (1 / 2 : ℝ) * B x (v 0) := by
  simp [liouvilleFormCLM]

private lemma hasFDerivAt_liouvilleFormCLM_apply (B : V →L[ℝ] V →L[ℝ] ℝ)
    (v : Fin 1 → V) (x : V) :
    HasFDerivAt (fun y ↦ liouvilleFormCLM B y v)
      ((ContinuousLinearMap.apply ℝ ℝ (v 0)).comp ((1 / 2 : ℝ) • B)) x := by
  let L := (ContinuousLinearMap.apply ℝ ℝ (v 0)).comp ((1 / 2 : ℝ) • B)
  have hfun : (fun y ↦ liouvilleFormCLM B y v) = L := by
    funext y
    simp [L, liouvilleFormCLM_apply]
  rw [hfun]
  exact L.hasFDerivAt

/-- The exterior derivative of the radial one-form of `B` is one half of the alternatization of
`B`: `dλₓ(v, w) = (B(v, w) - B(w, v)) / 2`. -/
@[simp]
lemma extDeriv_liouvilleFormCLM_apply (B : V →L[ℝ] V →L[ℝ] ℝ) (x : V)
    (v : Fin 2 → V) :
    extDeriv (liouvilleFormCLM B) x v =
      (1 / 2 : ℝ) * (B (v 0) (v 1) - B (v 1) (v 0)) := by
  rw [extDeriv_apply]
  · rw [Fin.sum_univ_two]
    simp only [Fin.isValue, Fin.val_zero, pow_zero, one_smul,
      Fin.val_one, pow_one, neg_smul, one_smul]
    rw [(hasFDerivAt_liouvilleFormCLM_apply B (Fin.removeNth 0 v) x).fderiv,
      (hasFDerivAt_liouvilleFormCLM_apply B (Fin.removeNth 1 v) x).fderiv]
    simp [Fin.removeNth]
    ring
  · exact (ContinuousLinearMap.liouvilleFormCLM B).differentiableAt

/-- If `B` is skew-symmetric, the radial one-form `λₓ(v) = B(x, v) / 2` is a primitive of the
constant two-form `B`. -/
lemma extDeriv_liouvilleFormCLM_apply_of_skew (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = -B w v) (x : V) (v : Fin 2 → V) :
    extDeriv (liouvilleFormCLM B) x v = B (v 0) (v 1) := by
  rw [extDeriv_liouvilleFormCLM_apply]
  rw [hB]
  ring

end ContinuousLinearMap

end

end
