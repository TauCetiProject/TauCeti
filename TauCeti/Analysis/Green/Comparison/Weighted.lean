/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Comparison.Integration
public import TauCeti.Analysis.Green.Comparison.ExteriorDerivative

/-!
# Weighted exterior derivatives against the canonical planar orientation

A compactly supported scalar weight with integrable weighted curl turns the actual planar
exterior derivative into an intrinsically integrable top form. Its canonical manifold integral
is the weighted
coordinate curl integral. Differentiability is needed only inside the indicated field domain.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti.Green

attribute [local instance] Complex.finrank_real_complex_fact

/-- Compact support of a weight and integrability of its weighted curl give genuine intrinsic
integrability and the canonical manifold integral of the actual weighted exterior derivative. -/
theorem _root_.HasCompactSupport.weighted_mextDeriv_integralTopForm {W : ℂ → ℝ} {U : Set ℂ}
    {P Q : ℂ → ℝ}
    (hc : HasCompactSupport W) (hU : MeasurableSet U)
    (hPd : ∀ z ∈ U, DifferentiableAt ℝ P z) (hQd : ∀ z ∈ U, DifferentiableAt ℝ Q z)
    (hi : IntegrableOn (fun z ↦ W z * curl P Q z) U) :
    IntegrableTopForm (I := 𝓘(ℝ, ℂ))
      (fun z ↦ U.indicator W z • mextDeriv (manifoldOneForm P Q) z) ∧
      integralTopForm (Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation
        (by simp))
        (fun z ↦ U.indicator W z • mextDeriv (manifoldOneForm P Q) z) =
          ∫ z in U, W z * curl P Q z := by
  let f := U.indicator (fun z ↦ W z * curl P Q z)
  have he : (fun z ↦ U.indicator W z • mextDeriv (manifoldOneForm P Q) z) =
      (fun z ↦ f z • manifoldAreaForm z : RoughForm 𝓘(ℝ, ℂ) ℂ ℝ 2) := by
    funext z
    by_cases hz : z ∈ U
    · rw [indicator_of_mem hz]
      dsimp only [f]
      rw [indicator_of_mem hz, (hPd z hz).mextDeriv_manifoldOneForm_eq_smul_area (hQd z hz),
        smul_smul]
    · simp only [f, indicator_of_notMem hz, zero_smul]
  have hf : Integrable f := hi.integrable_indicator hU
  have hcf : HasCompactSupport f := by
    have h := hc.mul_right (f' := U.indicator (curl P Q))
    convert h using 1
    funext z
    exact indicator_mul_right U W (curl P Q)
  rw [he]
  exact ⟨HasCompactSupport.integrableTopForm_fun_smul_manifoldAreaForm hcf hf,
    (HasCompactSupport.integralTopForm_model_manifoldAreaForm hcf hf).trans (integral_indicator hU)⟩

end TauCeti.Green
