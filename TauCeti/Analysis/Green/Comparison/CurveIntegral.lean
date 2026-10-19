/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.DifferentialForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Interval.Basic
import TauCeti.Analysis.Green.AbsolutelyContinuous

/-!
# The path curve integral as an actual manifold integral

For a path whose real extension is C1 on the unit interval, integration of the actual pullback
of the planar circulation form is the existing curve integral. Only integrability of its raw
circulation is required of the coefficients.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold

namespace TauCeti.Green

/-- The existing path curve integral equals integration of the actual manifold pullback on
the increasing unit interval. The path only needs C1 regularity on its parameter interval. -/
theorem _root_.Path.integralTopForm_mpullback {p q : ℂ} (γ : Path p q) (P Q : ℂ → ℝ)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hf : IntervalIntegrable (circulationFun P Q γ.extend) volume 0 1) :
    IntegrableTopForm
      (mpullback (𝓡∂ 1) 𝓘(ℝ, ℂ) (γ : Icc (0 : ℝ) 1 → ℂ) (manifoldOneForm P Q)) ∧
      integralTopForm (Manifold.Orientation.interval 0 1)
        (mpullback (𝓡∂ 1) 𝓘(ℝ, ℂ) (γ : Icc (0 : ℝ) 1 → ℂ) (manifoldOneForm P Q)) =
        curveIntegral (oneForm P Q) γ := by
  have he (t : ℝ) : manifoldOneForm P Q (γ.extend t)
      (fun _ ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (γ.extend t)).symm
        (deriv γ.extend t)) = circulationFun P Q γ.extend t := by
    rw [manifoldOneForm_apply, ContinuousLinearEquiv.apply_symm_apply,
      ← circulationFun_eq_oneForm]
  have h := integralTopForm_mpullback_curve_Icc (manifoldOneForm P Q) γ.extend hγ
    (by simpa only [he] using hf)
  have hp : (fun t : Icc (0 : ℝ) 1 ↦ γ.extend t) = (γ : Icc (0 : ℝ) 1 → ℂ) :=
    funext fun t ↦ γ.extend_apply t.property
  rw [hp] at h
  simpa only [he, ← curveIntegral_oneForm_eq] using h

/-- Continuous coefficients on the path trace give both existing curve integrability and
intrinsic integrability of the actual pullback, together with equality of the two integrals. -/
theorem _root_.Path.integralTopForm_mpullback_of_continuousOn {p q : ℂ} (γ : Path p q)
    (P Q : ℂ → ℝ) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hP : ContinuousOn P (γ.extend '' Icc 0 1))
    (hQ : ContinuousOn Q (γ.extend '' Icc 0 1)) :
    CurveIntegrable (oneForm P Q) γ ∧
      IntegrableTopForm
        (mpullback (𝓡∂ 1) 𝓘(ℝ, ℂ) (γ : Icc (0 : ℝ) 1 → ℂ) (manifoldOneForm P Q)) ∧
      integralTopForm (Manifold.Orientation.interval 0 1)
        (mpullback (𝓡∂ 1) 𝓘(ℝ, ℂ) (γ : Icc (0 : ℝ) 1 → ℂ) (manifoldOneForm P Q)) =
        curveIntegral (oneForm P Q) γ := by
  have hγu : ContDiffOn ℝ 1 γ.extend (uIcc 0 1) := by
    simpa only [uIcc_of_le zero_le_one] using hγ
  have hac : AbsolutelyContinuousOnInterval γ.extend 0 1 :=
    hγu.absolutelyContinuousOnInterval
  exact ⟨hac.curveIntegrable_oneForm hP hQ,
    Path.integralTopForm_mpullback γ P Q hγ
      (hac.intervalIntegrable_circulationFun (by simpa using hP) (by simpa using hQ))⟩

end TauCeti.Green
