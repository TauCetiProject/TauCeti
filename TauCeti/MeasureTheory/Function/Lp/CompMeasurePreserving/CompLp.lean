/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.LinearIsometry
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv

/-!
# Measure-preserving pullbacks commute with pointwise isometries on `L^p`

Precomposition by a measure-preserving map, `MeasureTheory.Lp.compMeasurePreservingₗᵢEquiv`, moves
the points of the domain, and pointwise composition with a linear isometry equivalence of the
values, `LinearIsometryEquiv.compLpₗᵢ`, rotates the values. The two operations commute, so a
rigid motion of the domain together with a rotation of the values acts on `L^p` by either
composite.

This lemma has its own file because it needs both `TauCeti.MeasureTheory.Function.Lp.LinearIsometry`
and `TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv`, neither of which imports the
other.

## Main declarations

* `MeasureTheory.Lp.compMeasurePreservingₗᵢEquiv_trans_compLpₗᵢ`: precomposition commutes
  with the pointwise isometry of the values.
-/

public section

open scoped ENNReal

namespace MeasureTheory
namespace Lp

variable {α β E F 𝕜 : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  {μb : Measure β} {p : ℝ≥0∞} [Fact (1 ≤ p)] [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
  [IsBoundedSMul 𝕜 E] [NormedAddCommGroup F] [Module 𝕜 F] [IsBoundedSMul 𝕜 F] {f : α → β}
  {g : β → α}

/-- Precomposition by a measure-preserving map commutes with pointwise composition with a linear
isometry equivalence of the values. -/
theorem compMeasurePreservingₗᵢEquiv_trans_compLpₗᵢ (hf : MeasurePreserving f μ μb)
    (hg : MeasurePreserving g μb μ) (hfg : f ∘ g =ᵐ[μb] id) (R : E ≃ₗᵢ[𝕜] F) :
    (compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg).trans (R.compLpₗᵢ p μ) =
      (R.compLpₗᵢ p μb).trans (compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg) := by
  refine LinearIsometryEquiv.ext fun x ↦ Lp.ext ?_
  filter_upwards [R.coeFn_compLpₗᵢ (compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg x),
    coeFn_compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg x,
    coeFn_compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg (R.compLpₗᵢ p μb x),
    hf.quasiMeasurePreserving.ae (R.coeFn_compLpₗᵢ x)] with a h₁ h₂ h₃ h₄
  rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply, h₁, h₂, h₃,
    Function.comp_apply, Function.comp_apply, h₄]

end Lp
end MeasureTheory
