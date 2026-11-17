/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness of coproducts of operator families

The coproduct `(f x).coprod (g x)` of two `C^n` families of continuous linear maps is `C^n`
(`ContDiffAt.continuousLinearMapCoprod`, `ContDiffOn.continuousLinearMapCoprod`), the smooth
analogue of Mathlib's `ContinuousAt.continuousLinearMapCoprod`.
-/

public section

open scoped ContDiff

variable {𝕜 E F G X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The coproduct of two families of operators has their common regularity. -/
theorem ContDiffAt.continuousLinearMapCoprod {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G} {x : X}
    {n : ℕ∞ω} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun y ↦ (f y).coprod (g y)) x := by
  simp_rw [← ContinuousLinearMap.comp_fst_add_comp_snd]
  exact (hf.clm_comp contDiffAt_const).add (hg.clm_comp contDiffAt_const)

/-- The coproduct of two families of operators has their common regularity on a set. -/
theorem ContDiffOn.continuousLinearMapCoprod {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G}
    {s : Set X} {n : ℕ∞ω} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun y ↦ (f y).coprod (g y)) s := by
  simp_rw [← ContinuousLinearMap.comp_fst_add_comp_snd]
  exact (hf.clm_comp contDiffOn_const).add (hg.clm_comp contDiffOn_const)
