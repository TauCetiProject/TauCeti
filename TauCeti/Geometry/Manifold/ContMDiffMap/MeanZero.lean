/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# Mean-zero `C^n` functions on a compact manifold

Given a finite measure `μ` on a compact manifold `M` and a differentiability order `n : ℕ∞ω`, the
`C^n` real-valued functions on `M` whose integral against `μ` vanishes form the `ℝ`-submodule
`TauCeti.Manifold.meanZeroSmoothFunctions I M μ n`, defined as the kernel of integration against
`μ` via `ContinuousMap.integralPositiveLinearMap` and `ContMDiffMap.toContinuousMapLinearMap`.

## Main definitions

* `TauCeti.Manifold.meanZeroSmoothFunctions`: the submodule of `C^n` functions on `M` with
  vanishing integral against `μ`.
* `TauCeti.Manifold.meanZeroSmoothFunctions.mk`: bundle a `C^n` function of vanishing integral as
  an element of `meanZeroSmoothFunctions`.

## Main results

* `TauCeti.Manifold.mem_meanZeroSmoothFunctions_iff`: membership characterization in
  `meanZeroSmoothFunctions I M μ n`.
* `TauCeti.Manifold.integral_coe_meanZeroSmoothFunctions_eq_zero`: the integral of a bundled
  mean-zero `C^n` function against `μ` is zero.
* `TauCeti.Manifold.meanZeroSmoothFunctions.coe_mk`: coercion of `meanZeroSmoothFunctions.mk` to a
  function.
-/

public section

open MeasureTheory
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
  [MeasurableSpace M] [OpensMeasurableSpace M] (μ : Measure M) [IsFiniteMeasure μ]
  (n : ℕ∞ω)

/-- The submodule of `C^n` functions on `M` with vanishing integral against `μ`. -/
def meanZeroSmoothFunctions : Submodule ℝ C^n⟮I, M; ℝ⟯ :=
  LinearMap.ker
    ((ContinuousMap.integralPositiveLinearMap μ).toLinearMap.comp
      ContMDiffMap.toContinuousMapLinearMap)

variable {I M μ n}

/-- A `C^n` function belongs to `meanZeroSmoothFunctions I M μ n` exactly when its integral
against `μ` vanishes. -/
@[simp]
theorem mem_meanZeroSmoothFunctions_iff {u : C^n⟮I, M; ℝ⟯} :
    u ∈ meanZeroSmoothFunctions I M μ n ↔ ∫ x, u x ∂μ = 0 := by
  simp [meanZeroSmoothFunctions, ContinuousMap.integralPositiveLinearMap_apply]

/-- The integral against `μ` of an element of `meanZeroSmoothFunctions I M μ n` vanishes. -/
@[simp]
theorem integral_coe_meanZeroSmoothFunctions_eq_zero (u : meanZeroSmoothFunctions I M μ n) :
    ∫ x, u.val x ∂μ = 0 :=
  mem_meanZeroSmoothFunctions_iff.1 u.property

/-- Bundle a `C^n` function with vanishing integral against `μ` as an element of
`meanZeroSmoothFunctions I M μ n`. -/
def meanZeroSmoothFunctions.mk {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f)
    (hf0 : ∫ x, f x ∂μ = 0) : meanZeroSmoothFunctions I M μ n :=
  ⟨⟨f, hf⟩, mem_meanZeroSmoothFunctions_iff.2 hf0⟩

/-- Coercing `meanZeroSmoothFunctions.mk hf hf0` to a function recovers `f`. -/
@[simp]
theorem meanZeroSmoothFunctions.coe_mk {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f)
    (hf0 : ∫ x, f x ∂μ = 0) :
    ((meanZeroSmoothFunctions.mk hf hf0).val : M → ℝ) = f :=
  ContMDiffMap.coeFn_mk f hf

end TauCeti.Manifold
