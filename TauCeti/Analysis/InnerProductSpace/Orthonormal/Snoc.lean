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
`v₀, …, vₖ₋₁` gives an orthonormal family `v₀, …, vₖ₋₁, z` (`Orthonormal.snoc`). Conversely, if
`v₀, …, vₖ₋₁, z` is orthonormal then so is `v₀, …, vₖ₋₁`, and `z` is a unit vector orthogonal to
each `vᵢ`; `orthonormal_snoc_iff` states both directions, as Mathlib's `orthonormal_vecCons_iff`
does for prepending. `Orthonormal.snoc` is the step used to build an orthonormal family one
vector at a time, each chosen in the orthogonal complement of the span of the previous ones, as
in the proof of the Dvoretzky–Rogers lemma.
-/

public section

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Orthonormal

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

/-- `Fin.snoc v z` is orthonormal if and only if `v` is orthonormal and `z` is a unit vector
orthogonal to every `v i`. -/
@[simp]
theorem orthonormal_snoc_iff {k : ℕ} {v : Fin k → E} {z : E} :
    Orthonormal 𝕜 (Fin.snoc v z : Fin (k + 1) → E) ↔
      Orthonormal 𝕜 v ∧ ‖z‖ = 1 ∧ ∀ i, ⟪v i, z⟫_𝕜 = 0 := by
  refine ⟨fun h ↦ ⟨?_, ?_, fun i ↦ ?_⟩, fun ⟨hv, hz, hvz⟩ ↦ hv.snoc hz hvz⟩
  · simpa [Function.comp_def] using h.comp _ (Fin.castSucc_injective k)
  · simpa using h.1 (Fin.last k)
  · simpa using h.2 (Fin.castSucc_ne_last i)
