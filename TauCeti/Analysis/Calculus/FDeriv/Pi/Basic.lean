/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Differentiability of the coordinate slices of a function on a product

A function `f` on a finite product `∀ i, E i` which is differentiable at `y` is differentiable in
each variable separately: the slice `x ↦ f (update y i x)` through `y` in the `i`-th coordinate is
differentiable at `y i`.

Conversely, for a finite family of functions `φ i : 𝕜 → 𝕜`, the *separated sum*
`z ↦ ∑ i, φ i (z i)` on `ι → 𝕜` has derivative `∑ i, φ i' (y i) • dzᵢ` at `y`, so its critical
points are the points whose coordinates are critical points of the summands. The *separated
product* `z ↦ ∏ i, φ i (z i)`, such as a multivariable Hermite function, has partial derivative in
the `i`-th variable the separated product with the `i`-th factor replaced by its derivative.

## Main declarations

* `DifferentiableWithinAt.comp_update`: the slice of a function differentiable within a set, within
  any set of coordinates which `update y i` maps into it.
* `DifferentiableAt.comp_update`: the slice of a function differentiable at a point.
* `TauCeti.hasFDerivAt_sum_comp_eval`, `TauCeti.fderiv_sum_comp_eval`: the derivative of a
  separated sum.
* `TauCeti.fderiv_sum_comp_eval_eventuallyEq`: the same formula for the derivative near a point at
  which the summands are continuously differentiable.
* `TauCeti.fderiv_sum_comp_eval_eq_zero_iff`: the critical points of a separated sum.
* `TauCeti.hasFDerivAt_prod_comp_eval`, `TauCeti.fderiv_prod_comp_eval_apply_single`: the derivative
  of a separated product `z ↦ ∏ i, φ i (z i)`, whose partial derivative in the `i`-th variable
  replaces the `i`-th factor by its derivative.
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

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] {φ : ι → 𝕜 → 𝕜} {y : ι → 𝕜}

/-- The derivative of the separated sum `z ↦ ∑ i, φ i (z i)` at `y` is `∑ i, φ i' (y i) • dzᵢ`. -/
theorem hasFDerivAt_sum_comp_eval {φ' : ι → 𝕜} (hφ : ∀ i, HasDerivAt (φ i) (φ' i) (y i)) :
    HasFDerivAt (fun z : ι → 𝕜 ↦ ∑ i, φ i (z i)) (∑ i, φ' i • (proj i : (ι → 𝕜) →L[𝕜] 𝕜)) y :=
  HasFDerivAt.fun_sum fun i _ ↦ (hφ i).comp_hasFDerivAt y (hasFDerivAt_apply i y)

/-- The derivative of a separated sum of differentiable functions. -/
theorem fderiv_sum_comp_eval (hφ : ∀ i, DifferentiableAt 𝕜 (φ i) (y i)) :
    fderiv 𝕜 (fun z : ι → 𝕜 ↦ ∑ i, φ i (z i)) y =
      ∑ i, deriv (φ i) (y i) • (proj i : (ι → 𝕜) →L[𝕜] 𝕜) :=
  (hasFDerivAt_sum_comp_eval fun i ↦ (hφ i).hasDerivAt).fderiv

/-- **Critical points of a separated sum.** For differentiable summands, `y` is a critical point
of `z ↦ ∑ i, φ i (z i)` exactly when every `y i` is a critical point of `φ i`. -/
theorem fderiv_sum_comp_eval_eq_zero_iff (hφ : ∀ i, DifferentiableAt 𝕜 (φ i) (y i)) :
    fderiv 𝕜 (fun z : ι → 𝕜 ↦ ∑ i, φ i (z i)) y = 0 ↔ ∀ i, deriv (φ i) (y i) = 0 := by
  classical
  rw [fderiv_sum_comp_eval hφ]
  refine ⟨fun h i ↦ ?_, fun h ↦ by ext; simp [h]⟩
  simpa [Pi.single_apply] using DFunLike.congr_fun h (Pi.single i 1)

/-- Near a point at which every summand is continuously differentiable, the derivative of a
separated sum is given by the formula of `TauCeti.fderiv_sum_comp_eval`. -/
theorem fderiv_sum_comp_eval_eventuallyEq (hφ : ∀ i, ContDiffAt 𝕜 1 (φ i) (y i)) :
    fderiv 𝕜 (fun z : ι → 𝕜 ↦ ∑ i, φ i (z i)) =ᶠ[𝓝 y]
      fun z ↦ ∑ i, deriv (φ i) (z i) • (proj i : (ι → 𝕜) →L[𝕜] 𝕜) := by
  have hdiff : ∀ i, ∀ᶠ z : ι → 𝕜 in 𝓝 y, DifferentiableAt 𝕜 (φ i) (z i) := fun i ↦
    (continuous_apply i).continuousAt.eventually
      (((hφ i).eventually (by simp)).mono fun t ht ↦ ht.differentiableAt (by simp))
  filter_upwards [eventually_all.2 hdiff] with z hz
  exact fderiv_sum_comp_eval hz

end SumCompEval

section ProdCompEval

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι] {φ : ι → 𝕜 → 𝕜}
  {y : ι → 𝕜}

/-- The derivative of the separated product `z ↦ ∏ i, φ i (z i)` at `y` is
`∑ i, (∏ j ≠ i, φ j (y j)) • φ i' (y i) • dzᵢ`. -/
theorem hasFDerivAt_prod_comp_eval {φ' : ι → 𝕜} (hφ : ∀ i, HasDerivAt (φ i) (φ' i) (y i)) :
    HasFDerivAt (fun z : ι → 𝕜 ↦ ∏ i, φ i (z i))
      (∑ i, (∏ j ∈ Finset.univ.erase i, φ j (y j)) • φ' i • (proj i : (ι → 𝕜) →L[𝕜] 𝕜)) y :=
  HasFDerivAt.finsetProd fun i _ ↦ (hφ i).comp_hasFDerivAt y (hasFDerivAt_apply i y)

/-- **The partial derivative of a separated product.** Differentiating `z ↦ ∏ j, φ j (z j)` in the
`i`-th variable replaces the factor `φ i` by its derivative. -/
theorem fderiv_prod_comp_eval_apply_single (hφ : ∀ i, DifferentiableAt 𝕜 (φ i) (y i)) (i : ι) :
    fderiv 𝕜 (fun z : ι → 𝕜 ↦ ∏ j, φ j (z j)) y (Pi.single i 1) =
      ∏ j, update φ i (deriv (φ i)) j (y j) := by
  rw [(hasFDerivAt_prod_comp_eval fun j ↦ (hφ j).hasDerivAt).fderiv,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [sum_apply, smul_apply, proj_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, update_self]
  rw [mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun j hj ↦ by rw [update_of_ne (Finset.ne_of_mem_erase hj)]

end ProdCompEval

end TauCeti
