/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Continuity of products of continuous linear maps

For spaces of continuous linear maps endowed with the topology of bounded convergence (which
coincides with the operator-norm topology on normed spaces), pairing two families of continuous
linear maps into a product map `y ↦ (f y).prod (g y)` preserves limits and continuity. These
lemmas are the `ContinuousLinearMap.prod` counterparts of Mathlib's
`Continuous*.continuousLinearMapCoprod` lemmas, proved directly from the continuous linear
equivalence `ContinuousLinearMap.prodL` without normed-space hypotheses.

## Main results

* `Filter.Tendsto.continuousLinearMapProd`: limit preservation for `i ↦ (f i).prod (g i)`.
* `ContinuousWithinAt.continuousLinearMapProd`, `ContinuousAt.continuousLinearMapProd`,
  `ContinuousOn.continuousLinearMapProd`, and `Continuous.continuousLinearMapProd`: `@[fun_prop]`
  continuity rules for `y ↦ (f y).prod (g y)`.
-/

public section

open Filter
open scoped Topology

section ContinuousLinearMapProd

variable {𝕜 E F G : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

/-- If `f i → f₀` and `g i → g₀` in the topology of bounded convergence (which coincides with the
operator-norm topology on normed spaces), then `(f i).prod (g i) → f₀.prod g₀`. -/
theorem Filter.Tendsto.continuousLinearMapProd {ι : Type*} {l : Filter ι}
    {f : ι → E →L[𝕜] F} {g : ι → E →L[𝕜] G} {f₀ : E →L[𝕜] F} {g₀ : E →L[𝕜] G}
    (hf : Tendsto f l (𝓝 f₀)) (hg : Tendsto g l (𝓝 g₀)) :
    Tendsto (fun i ↦ (f i).prod (g i)) l (𝓝 (f₀.prod g₀)) := by
  simpa only [Function.comp_def, ContinuousLinearMap.prodL_apply] using
    ((ContinuousLinearMap.prodL ℕ).continuous.tendsto (f₀, g₀)).comp (hf.prodMk_nhds hg)

variable {α : Type*} [TopologicalSpace α]

/-- Pairing two families of continuous linear maps that are continuous within `s` at `x` yields a
family continuous within `s` at `x` in the topology of bounded convergence. -/
@[fun_prop]
theorem ContinuousWithinAt.continuousLinearMapProd
    {f : α → E →L[𝕜] F} {g : α → E →L[𝕜] G} {s : Set α} {x : α}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun y ↦ (f y).prod (g y)) s x :=
  Filter.Tendsto.continuousLinearMapProd hf hg

/-- Pairing two families of continuous linear maps that are continuous at `x` yields a family
continuous at `x` in the topology of bounded convergence. -/
@[fun_prop]
theorem ContinuousAt.continuousLinearMapProd
    {f : α → E →L[𝕜] F} {g : α → E →L[𝕜] G} {x : α}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun y ↦ (f y).prod (g y)) x :=
  Filter.Tendsto.continuousLinearMapProd hf hg

/-- Pairing two families of continuous linear maps that are continuous on `s` yields a family
continuous on `s` in the topology of bounded convergence. -/
@[fun_prop]
theorem ContinuousOn.continuousLinearMapProd
    {f : α → E →L[𝕜] F} {g : α → E →L[𝕜] G} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun y ↦ (f y).prod (g y)) s :=
  fun x hx ↦ (hf x hx).continuousLinearMapProd (hg x hx)

/-- Pairing two continuous families of continuous linear maps yields a continuous family in the
topology of bounded convergence. -/
@[fun_prop]
theorem Continuous.continuousLinearMapProd
    {f : α → E →L[𝕜] F} {g : α → E →L[𝕜] G}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun y ↦ (f y).prod (g y)) :=
  continuous_iff_continuousAt.mpr fun _ ↦ hf.continuousAt.continuousLinearMapProd hg.continuousAt

end ContinuousLinearMapProd
