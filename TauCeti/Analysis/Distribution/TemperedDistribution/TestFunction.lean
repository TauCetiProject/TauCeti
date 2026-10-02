/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff

/-!
# Determining tempered distributions by real test functions

Two complex-linear tempered distributions agree if they agree on real-valued smooth,
compactly supported functions, embedded in complex Schwartz space. This connects the real
test functions used to define weak derivatives with the complex tests used in Fourier analysis.

The density input is `SchwartzMap.dense_hasCompactSupport`. See L. Hörmander,
*The Analysis of Linear Partial Differential Operators I*, Section 7.1.
-/

public section

namespace TauCeti

open scoped SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Real-valued compactly supported Schwartz functions determine a complex-linear tempered
distribution. The real functions are embedded in complex Schwartz space by `Complex.ofRealCLM`.
-/
theorem temperedDistribution_ext_real {u v : 𝓢'(E, F)}
    (h : ∀ φ : 𝓢(E, ℝ), HasCompactSupport φ →
      u (φ.postcompCLM Complex.ofRealCLM) = v (φ.postcompCLM Complex.ofRealCLM)) : u = v := by
  have hreal : ∀ φ : 𝓢(E, ℝ),
      u (φ.postcompCLM Complex.ofRealCLM) = v (φ.postcompCLM Complex.ofRealCLM) := by
    exact (SchwartzMap.dense_hasCompactSupport (E := E) (F := ℝ)).induction h
      (isClosed_eq
        (u.continuous.comp (SchwartzMap.postcompCLM Complex.ofRealCLM).continuous)
        (v.continuous.comp (SchwartzMap.postcompCLM Complex.ofRealCLM).continuous))
  ext φ
  have hsplit : φ = (φ.postcompCLM Complex.reCLM).postcompCLM Complex.ofRealCLM +
      Complex.I • (φ.postcompCLM Complex.imCLM).postcompCLM Complex.ofRealCLM := by
    ext x
    simp only [add_apply, smul_apply, SchwartzMap.postcompCLM_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, Complex.ofRealCLM_apply, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im (φ x)).symm
  rw [hsplit]
  simp only [map_add, map_smul, hreal]

end TauCeti
