/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Analysis.Normed.Module.Alternating.Bilinear

/-!
# The radial primitive of a constant two-form

Every continuous bilinear form on a normed space over a nontrivially normed field determines a
linear one-form by `λₓ(v) = B(x, v) / 2`. Its exterior derivative is one half of the
alternatization of `B`; when
`B` is skew-symmetric and `(2 : 𝕜) ≠ 0`, this says that the corresponding constant two-form is
exact. This is the explicit primitive for the constant model form in the local Darboux
construction.

The coordinate calculation follows the convention for exterior derivatives in
`Mathlib.Analysis.Calculus.DifferentialForm.Basic` and parallels the evaluation calculation for the
cotangent Liouville form in `TauCeti/Geometry/Symplectic/Cotangent/Liouville.lean`.
-/

public section

open ContinuousAlternatingMap

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 V F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The radial one-form associated to a continuous bilinear form `B`, given by
`λₓ(v) = B(x, v) / 2`. -/
def liouvilleFormCLM (B : V →L[𝕜] V →L[𝕜] F) :
    V →L[𝕜] V [⋀^Fin 1]→L[𝕜] F :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := 𝕜) (E := V) (F := F)
  (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp ((2⁻¹ : 𝕜) • B)

/-- The radial one-form evaluates by `λₓ(v) = B(x, v) / 2`. -/
@[simp]
lemma liouvilleFormCLM_apply (B : V →L[𝕜] V →L[𝕜] F) (x : V) (v : Fin 1 → V) :
    liouvilleFormCLM B x v = (2⁻¹ : 𝕜) • B x (v 0) := by
  simp [liouvilleFormCLM]

/-- The exterior derivative of the radial one-form of `B` is one half of the alternatization of
`B`: `dλₓ(v, w) = (B(v, w) - B(w, v)) / 2`. -/
lemma extDeriv_liouvilleFormCLM (B : V →L[𝕜] V →L[𝕜] F) (x : V) :
    extDeriv (liouvilleFormCLM B) x =
      (2⁻¹ : 𝕜) • TauCeti.ContinuousAlternatingMap.alternatizeBilinCLM 𝕜 V F B := by
  rw [ContinuousLinearMap.extDeriv_eq]
  simpa [liouvilleFormCLM] using
    (TauCeti.ContinuousAlternatingMap.alternatizeUncurryFin_ofSubsingletonLIE_comp
      ((2⁻¹ : 𝕜) • B))

/-- The exterior derivative of the radial one-form of `B` evaluates by
`dλₓ(v, w) = (B(v, w) - B(w, v)) / 2`. -/
lemma extDeriv_liouvilleFormCLM_apply (B : V →L[𝕜] V →L[𝕜] F) (x : V)
    (v : Fin 2 → V) :
    extDeriv (liouvilleFormCLM B) x v =
      (2⁻¹ : 𝕜) • (B (v 0) (v 1) - B (v 1) (v 0)) := by
  rw [extDeriv_liouvilleFormCLM]
  simp [TauCeti.ContinuousAlternatingMap.alternatizeBilinCLM_apply]

/-- If `B` is skew-symmetric and `(2 : 𝕜) ≠ 0`, the radial one-form
`λₓ(v) = B(x, v) / 2` is a primitive of the constant two-form `B`. -/
lemma extDeriv_liouvilleFormCLM_apply_of_skew (B : V →L[𝕜] V →L[𝕜] F)
    (h2 : (2 : 𝕜) ≠ 0) (hB : ∀ v w, B v w = -B w v) (x : V) (v : Fin 2 → V) :
    extDeriv (liouvilleFormCLM B) x v = B (v 0) (v 1) := by
  rw [extDeriv_liouvilleFormCLM_apply]
  rw [hB]
  rw [sub_eq_add_neg, ← two_smul 𝕜 (-(B (v 1) (v 0))), smul_smul]
  have hcoef : (2 : 𝕜)⁻¹ * 2 = 1 := by field_simp [h2]
  rw [hcoef, one_smul]

end ContinuousLinearMap

end

end
