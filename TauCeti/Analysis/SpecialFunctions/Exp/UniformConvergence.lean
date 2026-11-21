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

* `TendstoUniformlyOn.rexp`: if `f i → g` uniformly on `K` and `g` is bounded above on `K`, then
  `exp ∘ f i → exp ∘ g` uniformly on `K`.
* `TendstoUniformly.rexp`: the same on the whole space.
-/

public section

open Filter

/-- If `f i → g` uniformly on `K` and `g` is bounded above on `K`, then `exp ∘ f i → exp ∘ g`
uniformly on `K`. This is the real part of `TendstoUniformlyOn.comp_cexp` for the complexified
functions. -/
theorem TendstoUniformlyOn.rexp {α ι : Type*} {l : Filter ι} {f : ι → α → ℝ} {g : α → ℝ}
    {K : Set α} (hf : TendstoUniformlyOn f g l K) (hg : BddAbove (g '' K)) :
    TendstoUniformlyOn (fun i x ↦ Real.exp (f i x)) (fun x ↦ Real.exp (g x)) l K := by
  have h := (Complex.ofRealCLM.uniformContinuous.comp_tendstoUniformlyOn hf).comp_cexp
    (by simpa [Set.image_image] using hg)
  simpa [← Complex.ofReal_exp, Function.comp_def] using
    Complex.reCLM.uniformContinuous.comp_tendstoUniformlyOn h

/-- If `f i → g` uniformly and `g` is bounded above, then `exp ∘ f i → exp ∘ g` uniformly. -/
theorem TendstoUniformly.rexp {α ι : Type*} {l : Filter ι} {f : ι → α → ℝ} {g : α → ℝ}
    (hf : TendstoUniformly f g l) (hg : BddAbove (Set.range g)) :
    TendstoUniformly (fun i x ↦ Real.exp (f i x)) (fun x ↦ Real.exp (g x)) l :=
  tendstoUniformlyOn_univ.1 <| (tendstoUniformlyOn_univ.2 hf).rexp <| by rwa [Set.image_univ]
