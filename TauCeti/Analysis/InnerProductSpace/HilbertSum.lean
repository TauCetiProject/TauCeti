/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
# Adjoint of a Hilbert direct sum of operators

The adjoint of a uniformly bounded coordinatewise operator on the Hilbert sum `lp E 2` is the
coordinatewise family of adjoints. This makes it possible to assemble star representations
on arbitrary Hilbert direct sums using Mathlib's `lp.mapCLM`.
-/

public section

open scoped InnerProductSpace

namespace lp

variable {ι 𝕜 : Type*} {E F : ι → Type*} [RCLike 𝕜]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, NormedAddCommGroup (F i)]
  [∀ i, InnerProductSpace 𝕜 (F i)] [∀ i, CompleteSpace (F i)]

/-- Taking adjoints commutes with the Hilbert direct sum of a uniformly bounded operator family. -/
@[simp]
theorem adjoint_mapCLM (T : ∀ i, E i →L[𝕜] F i) {K : ℝ} (hK : 0 ≤ K)
    (hT : ∀ i, ‖T i‖ ≤ K) :
    (mapCLM 2 T hK hT).adjoint =
      mapCLM 2 (fun i => (T i).adjoint) hK (fun i => by simpa using hT i) := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left 𝕜
  intro x
  simp only [ContinuousLinearMap.adjoint_inner_right, inner_eq_tsum, mapCLM_apply_coe]

end lp
