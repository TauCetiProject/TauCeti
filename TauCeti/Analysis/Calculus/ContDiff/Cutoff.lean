/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Cutting off a map that is smooth on an open set

Multiplying a map `u` that is `C^n` on an open set `W` by a scalar cutoff `g` that is `C^n` near
every point of a set `U` and vanishes near every point of `U` outside `W` gives a map that is
`C^n` on all of `U` (`TauCeti.contDiffOn_smul_of_eventuallyEq_zero`). This is how a map defined
on a punctured domain is extended across a puncture by a cutoff vanishing near it.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞}

/-- Multiplying a map that is `C^n` on an open set `W` by a cutoff that is `C^n` at every point of
a set `U` and vanishes near every point of `U` outside `W` gives a map that is `C^n` on `U`. -/
theorem contDiffOn_smul_of_eventuallyEq_zero {U W : Set E} (hW : IsOpen W) {g : E → 𝕜}
    {u : E → F} (hg : ∀ z ∈ U, ContDiffAt 𝕜 n g z) (hu : ContDiffOn 𝕜 n u W)
    (h : ∀ z ∈ U, z ∉ W → g =ᶠ[𝓝 z] fun _ ↦ 0) :
    ContDiffOn 𝕜 n (fun z ↦ g z • u z) U := by
  intro z hz
  by_cases hzW : z ∈ W
  · exact ((hg z hz).smul (hu.contDiffAt (hW.mem_nhds hzW))).contDiffWithinAt
  · refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_ |>.contDiffWithinAt
    filter_upwards [h z hz hzW] with z' hz'
    rw [hz', zero_smul]

end TauCeti
