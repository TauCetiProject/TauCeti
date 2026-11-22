/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# Rank-one projections on Bochner `Lᵖ` spaces

For an inner product space `E` over `𝕜` (`ℝ` or `ℂ`) and any exponent `p : ℝ≥0∞`, projecting a
rank-one `Lᵖ` function `x ↦ f x • w` along `v` scales `f` by `⟪v, w⟫`, both pointwise on `Lp` and as
continuous linear operators when `1 ≤ p`.

## Main declarations

* `ContinuousLinearMap.innerSL_comp_toSpanSingleton`: `(innerSL 𝕜 v).comp (toSpanSingleton 𝕜 w) =
  ⟪v, w⟫_𝕜 • id`.
* `MeasureTheory.Lp.compLp_innerSL_compLp_toSpanSingleton`: rank-one projection on `Lp 𝕜 p μ`.
* `MeasureTheory.Lp.compLpL_innerSL_comp_compLpL_toSpanSingleton`: operator-level rank-one
  projection on `Lp 𝕜 p μ` for `1 ≤ p`.
-/

public section

noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace

namespace ContinuousLinearMap

/-- Composing `innerSL 𝕜 v` with `toSpanSingleton 𝕜 w` scales the scalar identity by `⟪v, w⟫`. -/
@[simp]
theorem innerSL_comp_toSpanSingleton {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (v w : E) :
    (innerSL 𝕜 v).comp (toSpanSingleton 𝕜 w) = ⟪v, w⟫_𝕜 • ContinuousLinearMap.id 𝕜 𝕜 := by
  ext; simp

end ContinuousLinearMap

namespace MeasureTheory.Lp

variable {α 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Projecting a rank-one `Lᵖ` function `x ↦ f x • w` along `v` scales `f` by `⟪v, w⟫`, for any
exponent `p : ℝ≥0∞`. -/
@[simp]
theorem compLp_innerSL_compLp_toSpanSingleton {p : ℝ≥0∞} (v w : E) (f : Lp 𝕜 p μ) :
    (innerSL 𝕜 v).compLp ((toSpanSingleton 𝕜 w).compLp f) = ⟪v, w⟫_𝕜 • f := by
  rw [compLp_compLp, innerSL_comp_toSpanSingleton, smul_compLp, id_compLp]

/-- Operator-level projection identity on `Lᵖ`: composing `(innerSL 𝕜 v).compLpL p μ` with
`(toSpanSingleton 𝕜 w).compLpL p μ` is scaling by `⟪v, w⟫`. -/
@[simp]
theorem compLpL_innerSL_comp_compLpL_toSpanSingleton {p : ℝ≥0∞} [Fact (1 ≤ p)] (v w : E) :
    ((innerSL 𝕜 v).compLpL p μ).comp ((toSpanSingleton 𝕜 w).compLpL p μ) =
      ⟪v, w⟫_𝕜 • ContinuousLinearMap.id 𝕜 (Lp 𝕜 p μ) :=
  ContinuousLinearMap.ext (compLp_innerSL_compLp_toSpanSingleton v w)

end MeasureTheory.Lp

end
