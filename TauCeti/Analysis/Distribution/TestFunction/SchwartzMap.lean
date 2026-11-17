/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.Distribution.SchwartzSpace.SupportedIn

/-!
# Test functions are Schwartz functions

A smooth function with compact support is a Schwartz function
(`HasCompactSupport.toSchwartzMap`). This file shows that the inclusion of the space `𝓓(Ω, F)` of
test functions on an open set, with its inductive limit topology, into `𝓢(E, F)` is continuous; on
each `𝓓_{K}(E, F)` it restricts to `ContDiffMapSupportedIn.toSchwartzMapCLM`. Transposing this
inclusion restricts tempered distributions to distributions on open sets.

## Main declarations

* `TestFunction.toSchwartzMapCLM`: the inclusion `𝓓(Ω, F) → 𝓢(E, F)`.
-/

public section

noncomputable section

open TopologicalSpace
open scoped Distributions SchwartzMap ContDiff

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

namespace TestFunction

variable [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] {Ω : Opens E}

variable (𝕜) in
/-- **Test functions are Schwartz functions**, continuously: the inclusion `𝓓(Ω, F) → 𝓢(E, F)`
of the test functions on an open set `Ω`, extended by zero, as a continuous linear map for the
inductive limit topology of `𝓓(Ω, F)`. -/
def toSchwartzMapCLM : 𝓓(Ω, F) →L[𝕜] 𝓢(E, F) :=
  TestFunction.mkCLM 𝕜 (fun f ↦ f.hasCompactSupport.toSchwartzMap f.contDiff)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun _ _ ↦
      (ContDiffMapSupportedIn.toSchwartzMapCLM 𝕜).continuous.congr fun _ ↦
        SchwartzMap.ext fun _ ↦ ContDiffMapSupportedIn.toSchwartzMapCLM_apply 𝕜 _ _

@[simp]
theorem coe_toSchwartzMapCLM (f : 𝓓(Ω, F)) : ⇑(toSchwartzMapCLM 𝕜 f) = f :=
  (rfl)

theorem toSchwartzMapCLM_apply (f : 𝓓(Ω, F)) (x : E) : toSchwartzMapCLM 𝕜 f x = f x :=
  (rfl)

theorem hasCompactSupport_toSchwartzMapCLM (f : 𝓓(Ω, F)) :
    HasCompactSupport (toSchwartzMapCLM 𝕜 f) := by
  rw [coe_toSchwartzMapCLM]
  exact f.hasCompactSupport

end TestFunction
