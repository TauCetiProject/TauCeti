/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Smooth maps into Euclidean half-spaces

A nonnegative `C^n` real-valued function `f : M → ℝ` on a manifold lifts along the `0`-th
coordinate embedding `t ↦ (𝓡∂ k).symm (EuclideanSpace.single 0 t)` to a `C^n` map into
`EuclideanHalfSpace k` (`ContMDiff.modelWithCornersEuclideanHalfSpace_symm_single`). In
particular, for `k = 1`, any nonnegative `C^n` real function defines a `C^n` map into the closed
half-line `EuclideanHalfSpace 1`.

## Main results

* `ContMDiff.modelWithCornersEuclideanHalfSpace_symm_single`: lifting a nonnegative `C^n`
  real-valued function into `EuclideanHalfSpace k` along the `0`-th coordinate is `C^n`.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ} [NeZero k] {n : ℕ∞ω} {f : M → ℝ}

/-- Lifting a nonnegative `C^n` real-valued function `f : M → ℝ` into `EuclideanHalfSpace k` via
the `0`-th coordinate embedding `t ↦ (𝓡∂ k).symm (EuclideanSpace.single 0 t)` gives a `C^n` map.
In particular, for `k = 1`, any nonnegative `C^n` real function lifts to a `C^n` map into the
closed half-line `EuclideanHalfSpace 1`. -/
theorem ContMDiff.modelWithCornersEuclideanHalfSpace_symm_single
    (hf : ContMDiff I 𝓘(ℝ) n f) (hf₀ : ∀ x, 0 ≤ f x) :
    ContMDiff I (𝓡∂ k) n fun x ↦ (𝓡∂ k).symm (EuclideanSpace.single (0 : Fin k) (f x)) :=
  (𝓡∂ k).contMDiffOn_symm.comp_contMDiff
    ((((EuclideanSpace.equiv (Fin k) ℝ).symm.contDiff.comp
      (contDiff_single (F' := fun _ : Fin k ↦ ℝ) n (0 : Fin k))).contMDiff).comp hf)
    fun x ↦ by
      rw [range_modelWithCornersEuclideanHalfSpace]
      simpa using hf₀ x
