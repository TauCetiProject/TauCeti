/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Differentiability of the coordinate slices of a function on a product

A function `f` on a finite product `∀ i, E i` which is differentiable at `y` is differentiable in
each variable separately: the slice `x ↦ f (update y i x)` through `y` in the `i`-th coordinate is
differentiable at `y i`.

Conversely, for a finite family of functions `φ i : ℝ → ℝ`, the *separated sum*
`z ↦ ∑ i, φ i (z i)` on `ι → ℝ` has derivative `∑ i, φ i' (y i) • dzᵢ` at `y`, so its critical
points are the points whose coordinates are critical points of the summands.

## Main declarations

* `DifferentiableWithinAt.comp_update`: the slice of a function differentiable within a set, within
  any set of coordinates which `update y i` maps into it.
* `DifferentiableAt.comp_update`: the slice of a function differentiable at a point.
* `TauCeti.hasFDerivAt_sum_comp_eval`, `TauCeti.fderiv_sum_comp_eval`: the derivative of a
  separated sum.
* `TauCeti.fderiv_sum_comp_eval_eventuallyEq`: the same formula for the derivative near a point at
  which the summands are continuously differentiable.
* `TauCeti.fderiv_sum_comp_eval_eq_zero_iff`: the critical points of a separated sum.
-/

public section

open Filter Function Topology ContinuousLinearMap

namespace TauCeti

section Update

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Finite ι] [DecidableEq ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : (∀ i, E i) → F} {y : ∀ i, E i}

/-- A function differentiable within `s` at `y` is differentiable in its `i`-th variable: the slice
`x ↦ f (update y i x)` is differentiable at `y i` within any set `t` that `update y i` maps into
`s`. -/
theorem _root_.DifferentiableWithinAt.comp_update {s : Set (∀ i, E i)}
    (h : DifferentiableWithinAt 𝕜 f s y) (i : ι) {t : Set (E i)}
    (hst : Set.MapsTo (update y i) t s) :
    DifferentiableWithinAt 𝕜 (fun x => f (update y i x)) t (y i) := by
  have := Fintype.ofFinite ι
  refine DifferentiableWithinAt.comp (y i) ?_
    (hasFDerivAt_update (𝕜 := 𝕜) y (y i)).differentiableAt.differentiableWithinAt hst
  rwa [update_eq_self]

/-- A function differentiable at `y` is differentiable in its `i`-th variable: the slice
`x ↦ f (update y i x)` is differentiable at `y i`. -/
theorem _root_.DifferentiableAt.comp_update (h : DifferentiableAt 𝕜 f y) (i : ι) :
    DifferentiableAt 𝕜 (fun x => f (update y i x)) (y i) := by
  simpa only [differentiableWithinAt_univ] using
    h.differentiableWithinAt.comp_update i (Set.mapsTo_univ _ Set.univ)

end Update

section SumCompEval

variable {ι : Type*} [Fintype ι] {φ : ι → ℝ → ℝ} {y : ι → ℝ}

/-- The derivative of the separated sum `z ↦ ∑ i, φ i (z i)` at `y` is `∑ i, φ i' (y i) • dzᵢ`. -/
theorem hasFDerivAt_sum_comp_eval {φ' : ι → ℝ} (hφ : ∀ i, HasDerivAt (φ i) (φ' i) (y i)) :
    HasFDerivAt (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) (∑ i, φ' i • (proj i : (ι → ℝ) →L[ℝ] ℝ)) y :=
  HasFDerivAt.fun_sum fun i _ ↦ (hφ i).comp_hasFDerivAt y (hasFDerivAt_apply i y)

/-- The derivative of a separated sum of differentiable functions. -/
theorem fderiv_sum_comp_eval (hφ : ∀ i, DifferentiableAt ℝ (φ i) (y i)) :
    fderiv ℝ (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) y =
      ∑ i, deriv (φ i) (y i) • (proj i : (ι → ℝ) →L[ℝ] ℝ) :=
  (hasFDerivAt_sum_comp_eval fun i ↦ (hφ i).hasDerivAt).fderiv

/-- **Critical points of a separated sum.** For differentiable summands, `y` is a critical point
of `z ↦ ∑ i, φ i (z i)` exactly when every `y i` is a critical point of `φ i`. -/
theorem fderiv_sum_comp_eval_eq_zero_iff (hφ : ∀ i, DifferentiableAt ℝ (φ i) (y i)) :
    fderiv ℝ (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) y = 0 ↔ ∀ i, deriv (φ i) (y i) = 0 := by
  classical
  rw [fderiv_sum_comp_eval hφ]
  refine ⟨fun h i ↦ ?_, fun h ↦ by simp [h]⟩
  simpa [Pi.single_apply] using DFunLike.congr_fun h (Pi.single i 1)

/-- Near a point at which every summand is continuously differentiable, the derivative of a
separated sum is given by the formula of `TauCeti.fderiv_sum_comp_eval`. -/
theorem fderiv_sum_comp_eval_eventuallyEq (hφ : ∀ i, ContDiffAt ℝ 1 (φ i) (y i)) :
    fderiv ℝ (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) =ᶠ[𝓝 y]
      fun z ↦ ∑ i, deriv (φ i) (z i) • (proj i : (ι → ℝ) →L[ℝ] ℝ) := by
  have hdiff : ∀ i, ∀ᶠ z : ι → ℝ in 𝓝 y, DifferentiableAt ℝ (φ i) (z i) := fun i ↦
    (continuous_apply i).continuousAt.eventually
      (((hφ i).eventually (by simp)).mono fun t ht ↦ ht.differentiableAt (by simp))
  filter_upwards [eventually_all.2 hdiff] with z hz
  exact fderiv_sum_comp_eval hz

end SumCompEval

end TauCeti
