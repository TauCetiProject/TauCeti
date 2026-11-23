/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Pointwise bounds for families of Hölder coefficients

Second-order operators on `ℝⁿ = EuclideanSpace ℝ ι` have scalar Hölder coefficients `aⁱʲ` and
`bⁱ` on a metric space `X`. At each point `p : X` they assemble into the matrix `(aⁱʲ(p))` and
the vector `∑ᵢ bⁱ(p) eᵢ`. This file bounds the trace of that matrix and the norm of that vector
by the supremum-plus-Hölder norms of the coefficients, uniformly in `p`, and bounds each
coefficient entrywise in the same way.

## Main declarations

* `TauCeti.HolderSpace.trace_le_sum_norm`: `tr (aⁱʲ(p)) ≤ ∑ᵢ ‖aⁱⁱ‖`.
* `TauCeti.HolderSpace.norm_sum_apply_smul_single_le_sum_norm`: `‖∑ᵢ bⁱ(p) eᵢ‖ ≤ ∑ᵢ ‖bⁱ‖`.
* `TauCeti.HolderSpace.abs_apply_le_sum_sum_norm`, `TauCeti.HolderSpace.abs_apply_le_sum_norm`:
  the entrywise bounds `|aⁱʲ(p)| ≤ ∑ᵢ ∑ⱼ ‖aⁱʲ‖` and `|bⁱ(p)| ≤ ∑ᵢ ‖bⁱ‖`.
-/

public section

namespace TauCeti.HolderSpace

open scoped NNReal

variable {α : ℝ≥0} {X : Type*} [MetricSpace X] {ι : Type*} [Fintype ι]

/-- The trace of the coefficient matrix `(aⁱʲ(p))` is at most `∑ᵢ ‖aⁱⁱ‖`. -/
theorem trace_le_sum_norm (a : ι → ι → HolderSpace α X ℝ) (p : X) :
    (Matrix.of fun i j ↦ a i j p).trace ≤ ∑ i, ‖a i i‖ :=
  Finset.sum_le_sum fun i _ ↦ (le_abs_self _).trans (norm_apply_le (a i i) _)

/-- The drift vector `∑ᵢ bⁱ(p) eᵢ` has norm at most `∑ᵢ ‖bⁱ‖`. -/
theorem norm_sum_apply_smul_single_le_sum_norm [DecidableEq ι] (b : ι → HolderSpace α X ℝ)
    (p : X) : ‖∑ i, b i p • EuclideanSpace.single i (1 : ℝ)‖ ≤ ∑ i, ‖b i‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ by
    simpa [norm_smul] using norm_apply_le (b i) _)

/-- Each drift coefficient is bounded pointwise by the sum of their norms:
`|bⁱ(p)| ≤ ∑ᵢ ‖bⁱ‖`. -/
theorem abs_apply_le_sum_norm (b : ι → HolderSpace α X ℝ) (p : X) (i : ι) :
    |b i p| ≤ ∑ i, ‖b i‖ :=
  (abs_apply_le_norm (b i) p).trans
    (Finset.single_le_sum (fun i _ ↦ norm_nonneg (b i)) (Finset.mem_univ i))

/-- Each diffusion coefficient is bounded pointwise by the sum of their norms:
`|aⁱʲ(p)| ≤ ∑ᵢ ∑ⱼ ‖aⁱʲ‖`. -/
theorem abs_apply_le_sum_sum_norm (a : ι → ι → HolderSpace α X ℝ) (p : X) (i j : ι) :
    |a i j p| ≤ ∑ i, ∑ j, ‖a i j‖ :=
  (abs_apply_le_sum_norm (a i) p j).trans
    (Finset.single_le_sum (f := fun i ↦ ∑ j, ‖a i j‖)
      (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg (a i j))
      (Finset.mem_univ i))

end TauCeti.HolderSpace
