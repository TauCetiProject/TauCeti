/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Positive tangent cones and outward normals

In a real inner product space, a vector `n` is an outward normal of a set `s` at `y` when
`⟪n, k - y⟫ ≤ 0` for every `k ∈ s`. Such a normal pairs nonpositively with every positive tangent
vector of `s` at `y`, since `y` is then a local maximum of `⟪n, ·⟫` on `s`.

## Main results

* `TauCeti.real_inner_le_zero_of_mem_posTangentConeAt`: an outward normal of a set pairs
  nonpositively with its positive tangent vectors.
-/

public section

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace TauCeti

/-- An outward normal `n` of a set `s` at `y`, in the sense that `⟪n, k - y⟫ ≤ 0` for every
`k ∈ s`, pairs nonpositively with every positive tangent vector of `s` at `y`. -/
theorem real_inner_le_zero_of_mem_posTangentConeAt {s : Set E} {y n w : E}
    (hn : ∀ k ∈ s, ⟪n, k - y⟫ ≤ 0) (hw : w ∈ posTangentConeAt s y) : ⟪n, w⟫ ≤ 0 := by
  have hmax : IsLocalMaxOn (innerSL ℝ n) s y :=
    eventually_nhdsWithin_of_forall fun k hk ↦ by
      simpa [innerSL_apply_apply, inner_sub_right] using hn k hk
  simpa using hmax.hasFDerivWithinAt_nonpos (innerSL ℝ n).hasFDerivWithinAt hw

end TauCeti
