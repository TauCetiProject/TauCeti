/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Schwartz

/-!
# Smooth functions supported in a compact set as Schwartz functions

A smooth function supported in a compact set `K` is a Schwartz function, by the continuous
inclusion `ContDiffMapSupportedIn.toSchwartzMapCLM` of `𝓓_{K}(E, F)` into `𝓢(E, F)`. This file
records that the inclusion keeps the values and the support
(`ContDiffMapSupportedIn.toSchwartzMapCLM_apply`,
`ContDiffMapSupportedIn.tsupport_toSchwartzMapCLM_subset`), and that it agrees with reading a
function supported in `K` as a test function and then as a Schwartz function
(`ContDiffMapSupportedIn.toSchwartzMap_ofSupportedIn`).
-/

public section

noncomputable section

open TopologicalSpace
open scoped SchwartzMap Distributions

namespace ContDiffMapSupportedIn

variable (𝕜 : Type*) {E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  [SMulCommClass ℝ 𝕜 F] {K : Compacts E}

/-- A smooth function supported in `K`, read as a Schwartz function, has the same values. -/
theorem toSchwartzMapCLM_apply (f : 𝓓_{K}(E, F)) (x : E) : toSchwartzMapCLM 𝕜 f x = f x :=
  congrFun (coe_toSchwartzMapCLM f) x

/-- A smooth function supported in `K`, read as a Schwartz function, is still supported in `K`. -/
theorem tsupport_toSchwartzMapCLM_subset (f : 𝓓_{K}(E, F)) :
    tsupport (toSchwartzMapCLM 𝕜 f) ⊆ K :=
  coe_toSchwartzMapCLM (𝕜 := 𝕜) f ▸ f.tsupport_subset

/-- A smooth function supported in `K`, read as a test function on an open set `Ω ⊇ K` and then as
a Schwartz function, is its image under `toSchwartzMapCLM`. -/
theorem toSchwartzMap_ofSupportedIn {Ω : Opens E} (hK : (K : Set E) ⊆ Ω) (f : 𝓓_{K}(E, F)) :
    (TestFunction.ofSupportedIn hK f).hasCompactSupport.toSchwartzMap
        (TestFunction.ofSupportedIn hK f).contDiff =
      toSchwartzMapCLM 𝕜 f :=
  SchwartzMap.ext fun x ↦ (toSchwartzMapCLM_apply 𝕜 f x).symm

end ContDiffMapSupportedIn
