/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Analysis.Normed.Module.Alternating.Bilinear

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

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

/-- The exterior derivative of a continuous linear differential form is its alternatization. -/
@[simp]
lemma extDeriv_eq (ω : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) (x : E) :
    extDeriv ω x = ContinuousAlternatingMap.alternatizeUncurryFin ω := by
  simp [extDeriv]

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The radial one-form associated to a continuous bilinear form `B`, given by
`λₓ(v) = B(x, v) / 2`. -/
def liouvilleFormCLM (B : V →L[ℝ] V →L[ℝ] ℝ) :
    V →L[ℝ] V [⋀^Fin 1]→L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp ((2⁻¹ : ℝ) • B)

/-- The radial one-form evaluates by `λₓ(v) = B(x, v) / 2`. -/
@[simp]
lemma liouvilleFormCLM_apply (B : V →L[ℝ] V →L[ℝ] ℝ) (x : V) (v : Fin 1 → V) :
    liouvilleFormCLM B x v = (2⁻¹ : ℝ) * B x (v 0) := by
  simp [liouvilleFormCLM]

/-- The exterior derivative of the radial one-form of `B` is one half of the alternatization of
`B`: `dλₓ(v, w) = (B(v, w) - B(w, v)) / 2`. -/
@[simp]
lemma extDeriv_liouvilleFormCLM (B : V →L[ℝ] V →L[ℝ] ℝ) (x : V) :
    extDeriv (liouvilleFormCLM B) x =
      (2⁻¹ : ℝ) • TauCeti.ContinuousAlternatingMap.alternatizeBilinCLM ℝ V ℝ B := by
  rw [ContinuousLinearMap.extDeriv_eq]
  ext v
  simp [liouvilleFormCLM, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two,
    Fin.removeNth, Fin.succAbove, sub_eq_add_neg]

/-- The exterior derivative of the radial one-form of `B` evaluates by
`dλₓ(v, w) = (B(v, w) - B(w, v)) / 2`. -/
lemma extDeriv_liouvilleFormCLM_apply (B : V →L[ℝ] V →L[ℝ] ℝ) (x : V)
    (v : Fin 2 → V) :
    extDeriv (liouvilleFormCLM B) x v =
      (2⁻¹ : ℝ) * (B (v 0) (v 1) - B (v 1) (v 0)) := by
  rw [extDeriv_liouvilleFormCLM]
  simp [TauCeti.ContinuousAlternatingMap.alternatizeBilinCLM_apply]

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
