/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# Uniform convergence under the real exponential

The real exponential is not uniformly continuous on `ℝ`, but it is on every half-line `(-∞, a]`.
So `exp ∘ f i → exp ∘ g` uniformly whenever `f i → g` uniformly and the limit `g` is bounded
above; this is the real-valued form of Mathlib's `TendstoUniformlyOn.comp_cexp`. The upper bound
cannot be dropped: `x + 1 / n → x` uniformly on `ℝ`, but
`exp (x + 1 / n) - exp x = (exp (1 / n) - 1) exp x` is unbounded for every `n`.

## Main results

* `TendstoUniformly.rexp_of_le`: if `f i → g` uniformly and `g ≤ M`, then
  `exp ∘ f i → exp ∘ g` uniformly.
-/

public section

open Filter

/-- If `f i → g` uniformly and `g` is bounded above, then `exp ∘ f i → exp ∘ g` uniformly. This is
the real part of `TendstoUniformlyOn.comp_cexp` for the complexified functions. -/
theorem TendstoUniformly.rexp_of_le {α ι : Type*} {l : Filter ι} {f : ι → α → ℝ} {g : α → ℝ}
    {M : ℝ} (hf : TendstoUniformly f g l) (hM : ∀ x, g x ≤ M) :
    TendstoUniformly (fun i x ↦ Real.exp (f i x)) (fun x ↦ Real.exp (g x)) l := by
  have h := (tendstoUniformlyOn_univ.2
    (Complex.ofRealCLM.uniformContinuous.comp_tendstoUniformly hf)).comp_cexp
    ⟨M, by rintro _ ⟨x, -, rfl⟩; simpa using hM x⟩
  simpa [← Complex.ofReal_exp, Function.comp_def] using
    Complex.reCLM.uniformContinuous.comp_tendstoUniformly (tendstoUniformlyOn_univ.1 h)
