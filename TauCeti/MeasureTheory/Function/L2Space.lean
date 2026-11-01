/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Inner products of square-integrable functions

The pointwise inner product of two square-integrable functions with values in an inner product
space is integrable. Mathlib states this for elements of `L²` (`MeasureTheory.L2.integrable_inner`);
this file gives the form for functions satisfying `MemLp f 2 μ`, which is how second-moment
hypotheses on random vectors are usually stated, together with the special case of a quadratic
form `⟪B (f x), f x⟫` of a matrix `B` on a Euclidean-valued function.
-/

public section

open scoped InnerProductSpace

namespace MeasureTheory

variable {α 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The pointwise inner product of two square-integrable functions is integrable. -/
theorem MemLp.integrable_inner {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x ↦ ⟪f x, g x⟫_𝕜) μ :=
  (L2.integrable_inner (𝕜 := 𝕜) (hf.toLp f) (hg.toLp g)).congr <| by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    rw [hfx, hgx]

/-- The quadratic form of a matrix on a square-integrable Euclidean-valued function is
integrable. -/
theorem MemLp.integrable_inner_toEuclideanLin {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : α → EuclideanSpace 𝕜 ι} (hf : MemLp f 2 μ) (B : Matrix ι ι 𝕜) :
    Integrable (fun x ↦ ⟪B.toEuclideanLin (f x), f x⟫_𝕜) μ :=
  (hf.continuousLinearMap_comp (LinearMap.toContinuousLinearMap B.toEuclideanLin)).integrable_inner
    hf

end MeasureTheory
