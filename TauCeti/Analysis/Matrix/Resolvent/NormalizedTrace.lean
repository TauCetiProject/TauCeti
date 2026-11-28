/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Basic

import TauCeti.Topology.Instances.Matrix

/-!
# Normalized matrix resolvent traces

The normalized resolvent trace is continuous along continuous matrix families wherever
the shifted matrices are invertible. This includes Hermitian families at nonreal parameters.
-/

public section

namespace Matrix

/-- The trace of `(A - z • 1)⁻¹` divided by the dimension of `A`. It is zero if
`A - z • 1` is singular or if the dimension vanishes in the coefficient field. -/
noncomputable def normalizedResolventTrace {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [Field 𝕜]
    (A : Matrix n n 𝕜) (z : 𝕜) : 𝕜 :=
  (Fintype.card n : 𝕜)⁻¹ * (A - z • 1)⁻¹.trace

theorem normalizedResolventTrace_def {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [Field 𝕜]
    (A : Matrix n n 𝕜) (z : 𝕜) :
    A.normalizedResolventTrace z = (Fintype.card n : 𝕜)⁻¹ * (A - z • 1)⁻¹.trace := (rfl)

/-- For a matrix indexed by a sum, the normalizing dimension is the sum of the two
index cardinalities. -/
theorem normalizedResolventTrace_sum {m n 𝕜 : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Field 𝕜] (A : Matrix (m ⊕ n) (m ⊕ n) 𝕜) (z : 𝕜) :
    A.normalizedResolventTrace z =
      (Fintype.card m + Fintype.card n : 𝕜)⁻¹ * (A - z • 1)⁻¹.trace := by
  rw [normalizedResolventTrace_def, Fintype.card_sum, Nat.cast_add]

end Matrix

/-- At a fixed parameter, the normalized resolvent trace of a continuous matrix family
is continuous if every shifted matrix is invertible. -/
theorem Continuous.matrix_normalizedResolventTrace {X n 𝕜 : Type*} [TopologicalSpace X]
    [Fintype n] [DecidableEq n] [Field 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] [ContinuousInv₀ 𝕜] {A : X → Matrix n n 𝕜}
    (hc : Continuous A) {z : 𝕜} (hdet : ∀ x, (A x - z • 1).det ≠ 0) :
    Continuous (fun x ↦ (A x).normalizedResolventTrace z) := by
  simp only [Matrix.normalizedResolventTrace_def]
  exact continuous_const.mul ((hc.sub continuous_const).matrix_inv hdet).matrix_trace

/-- The normalized resolvent trace of a continuous Hermitian matrix family is continuous at a
fixed nonreal spectral parameter. -/
theorem Continuous.matrix_normalizedResolventTrace_of_isHermitian {X n 𝕜 : Type*}
    [TopologicalSpace X]
    [Fintype n] [DecidableEq n] [RCLike 𝕜] {A : X → Matrix n n 𝕜}
    (hc : Continuous A) (hA : ∀ x, (A x).IsHermitian) {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    Continuous (fun x ↦ (A x).normalizedResolventTrace z) := by
  exact hc.matrix_normalizedResolventTrace fun x ↦
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      ((hA x).isUnit_sub_smul_one_of_im_ne_zero hz))
