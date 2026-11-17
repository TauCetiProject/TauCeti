/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.Analysis.Complex.BranchLogRoot

/-!
# Angle lifts of curves on a circle

A `Cⁿ` curve `ℓ : ℝ → ℂ` with values in the circle of radius `r > 0` about `c` lifts to a `Cⁿ`
angle, `ℓ t = circleMap c r (φ t)` (`TauCeti.Contour.exists_contDiff_eq_circleMap`): `φ` is a
smooth phase of the unimodular map `(ℓ - c) / r`.
-/

public section

noncomputable section

open Complex

namespace TauCeti.Contour

variable {ℓ : ℝ → ℂ} {c : ℂ} {r : ℝ}

/-- **An angle lift of a curve on a circle.** A `Cⁿ` curve with values in the circle of radius
`r > 0` about `c` is `circleMap c r ∘ φ` for a `Cⁿ` angle `φ : ℝ → ℝ`. -/
theorem exists_contDiff_eq_circleMap {n : WithTop ℕ∞} (hℓ : ContDiff ℝ n ℓ) (hr : 0 < r)
    (hs : ∀ t, ℓ t ∈ Metric.sphere c r) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ n φ ∧ ∀ t, ℓ t = circleMap c r (φ t) := by
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  obtain ⟨f, hf, hfe⟩ := exists_contDiff_eq_exp_ofReal_mul_I (h := fun z ↦ (ℓ z.re - c) / r)
    (((hℓ.comp reCLM.contDiff).sub contDiff_const).div_const _) fun z ↦ by
      rw [norm_div, ← dist_eq_norm, Metric.mem_sphere.1 (hs z.re), norm_real,
        Real.norm_of_nonneg hr.le, div_self hr.ne']
  refine ⟨fun t ↦ f t, hf.comp ofRealCLM.contDiff, fun t ↦ ?_⟩
  have h := hfe t
  rw [ofReal_re, div_eq_iff hr'] at h
  simp only [circleMap]
  linear_combination h

end TauCeti.Contour
