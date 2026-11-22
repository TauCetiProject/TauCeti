/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

/-!
# Basic facts about functions supported in a compact set

Elementary properties of the space `𝓓^{n}_{K}(E, F)` of `C^n` functions `E → F` supported in a
compact set `K`.

## Main results

* `ContDiffMapSupportedIn.differentiable`: for `1 ≤ n`, the elements of `𝓓^{n}_{K}(E, F)` are
  differentiable.
* `ContDiffMapSupportedIn.structureMapCLM_apply_eq_zero_of_notMem`: the structure maps, that is
  the derivatives of `f ∈ 𝓓^{n}_{K}(E, F)`, vanish off `K`.
-/

public section

open TopologicalSpace
open scoped Distributions

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {n : ℕ∞} {K : Compacts E}

/-- For `1 ≤ n`, a `C^n` function supported in `K` is differentiable. -/
protected theorem differentiable (hn : 1 ≤ n) (f : 𝓓^{n}_{K}(E, F)) : Differentiable ℝ f :=
  f.contDiff.differentiable (by exact_mod_cast (one_ne_zero.bot_lt.trans_le hn).ne')

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The structure maps vanish off `K`. -/
theorem structureMapCLM_apply_eq_zero_of_notMem (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) {x : E}
    (hx : x ∉ K) : structureMapCLM 𝕜 n i f x = 0 := by
  rw [structureMapCLM_apply]
  split_ifs
  · exact f.iteratedFDeriv_zero_on_compl hx
  · simp

end ContDiffMapSupportedIn
