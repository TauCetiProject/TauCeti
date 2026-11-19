/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Extending an orthonormal family by one vector

Appending a unit vector orthogonal to every member of a finite orthonormal family
`v₀, …, vₖ₋₁` gives an orthonormal family `v₀, …, vₖ₋₁, z` (`Orthonormal.snoc`). This is the step
used to build an orthonormal family one vector at a time, each chosen in the orthogonal complement
of the span of the previous ones, as in the proof of the Dvoretzky–Rogers lemma.
-/

public section

open scoped InnerProductSpace

namespace Orthonormal

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Appending to an orthonormal family `v` a unit vector `z` orthogonal to every `v i` gives an
orthonormal family. -/
theorem snoc {k : ℕ} {v : Fin k → E} (hv : Orthonormal 𝕜 v) {z : E} (hz : ‖z‖ = 1)
    (hvz : ∀ i, ⟪v i, z⟫_𝕜 = 0) : Orthonormal 𝕜 (Fin.snoc v z : Fin (k + 1) → E) := by
  classical
  refine orthonormal_iff_ite.2 fun i j ↦ ?_
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [hz, hvz, orthonormal_iff_ite.1 hv, inner_self_eq_norm_sq_to_K, ← inner_conj_symm z,
      Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

end Orthonormal
