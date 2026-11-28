/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Basic

/-!
# Normalized matrix resolvent traces

The normalized resolvent trace is continuous along continuous Hermitian matrix families
at each fixed nonreal spectral parameter.
-/

public section

namespace Matrix

/-- The trace of `(A - z • 1)⁻¹` divided by the dimension of `A`. -/
noncomputable def normalizedResolventTrace {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [Field 𝕜]
    (A : Matrix n n 𝕜) (z : 𝕜) : 𝕜 :=
  (Fintype.card n : 𝕜)⁻¹ * (A - z • 1)⁻¹.trace

theorem normalizedResolventTrace_def {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [Field 𝕜]
    (A : Matrix n n 𝕜) (z : 𝕜) :
    A.normalizedResolventTrace z = (Fintype.card n : 𝕜)⁻¹ * (A - z • 1)⁻¹.trace := (rfl)

end Matrix

/-- The normalized resolvent trace of a continuous Hermitian matrix family is continuous at a
fixed nonreal spectral parameter. -/
theorem Continuous.matrix_normalizedResolventTrace {X n 𝕜 : Type*} [TopologicalSpace X]
    [Fintype n] [DecidableEq n] [RCLike 𝕜] {A : X → Matrix n n 𝕜}
    (hc : Continuous A) (hA : ∀ x, (A x).IsHermitian) {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    Continuous (fun x ↦ (A x).normalizedResolventTrace z) := by
  simp only [Matrix.normalizedResolventTrace_def]
  exact continuous_const.mul (hc.matrix_inv_sub_smul_one hA hz).matrix_trace
