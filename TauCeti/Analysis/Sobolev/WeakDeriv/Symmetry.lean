/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Weak derivatives commute

Let `u` have weak derivatives `u₁` in the direction `v` and `u₂` in the direction `w` on an open
set `Ω`. If `u₁` has a weak derivative `u₁₂` in the direction `w`, then `u₂` has the same weak
derivative `u₁₂` in the direction `v`: the mixed weak derivatives `∂_w ∂_v u` and `∂_v ∂_w u`
agree as soon as one of them exists. No regularity beyond the existence of the three weak
derivatives is assumed.

The proof moves both derivatives onto the test function and uses that directional derivatives of
test functions commute (`TestFunction.lineDerivOp_comm`).

## Main declarations

* `TauCeti.HasWeakLineDerivOn.comm`: weak derivatives in two directions commute.
* `TauCeti.W1p.hasWeakLineDerivOn_inner_gradient_comm`: the same for the first derivatives
  `⟪∇u, y⟫` of a Sobolev function `u ∈ W^{1,p}(Ω)`.
-/

public section

namespace TauCeti

open LineDeriv MeasureTheory TopologicalSpace
open scoped Distributions InnerProductSpace

section Comm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] {μ : Measure E} {Ω : Opens E}
  {u u₁ u₂ u₁₂ : E → F} {v w : E}

/-- **Weak derivatives commute.** If `u` has weak derivatives `u₁ = ∂_v u` and `u₂ = ∂_w u` on
`Ω`, and `u₁` has a weak derivative `u₁₂ = ∂_w ∂_v u`, then `u₁₂` is also a weak derivative of
`u₂` in the direction `v`, that is, `∂_v ∂_w u = ∂_w ∂_v u`. -/
theorem HasWeakLineDerivOn.comm (h₁ : HasWeakLineDerivOn μ Ω u u₁ v)
    (h₁₂ : HasWeakLineDerivOn μ Ω u₁ u₁₂ w) (h₂ : HasWeakLineDerivOn μ Ω u u₂ w) :
    HasWeakLineDerivOn μ Ω u₂ u₁₂ v := by
  refine hasWeakLineDerivOn_iff_testFunction.2
    ⟨h₁.completeSpace, h₂.locallyIntegrableOn_deriv, h₁₂.locallyIntegrableOn_deriv, fun φ => ?_⟩
  calc ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u₂ x ∂μ
      = ∫ x, (∂_{v} φ : 𝓓(Ω, ℝ)) x • u₂ x ∂μ := by simp only [TestFunction.lineDerivOp_apply]
    _ = -∫ x, lineDeriv ℝ (∂_{v} φ : 𝓓(Ω, ℝ)) x w • u x ∂μ := by
        rw [h₂.integral_lineDeriv_smul_eq_neg_integral_smul, neg_neg]
    _ = -∫ x, lineDeriv ℝ (∂_{w} φ : 𝓓(Ω, ℝ)) x v • u x ∂μ := by
        simp only [TestFunction.lineDeriv_lineDerivOp_comm φ v w]
    _ = ∫ x, (∂_{w} φ : 𝓓(Ω, ℝ)) x • u₁ x ∂μ := by
        rw [h₁.integral_lineDeriv_smul_eq_neg_integral_smul, neg_neg]
    _ = ∫ x, lineDeriv ℝ (φ : E → ℝ) x w • u₁ x ∂μ := by
        simp only [TestFunction.lineDerivOp_apply]
    _ = -∫ x, (φ : E → ℝ) x • u₁₂ x ∂μ := h₁₂.integral_lineDeriv_smul_eq_neg_integral_smul φ

end Comm

section W1p

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- **Second derivatives of a Sobolev function are symmetric.** If `∂_y u = ⟪∇u, y⟫` has the weak
derivative `G` in the direction `w`, then `∂_w u` has the weak derivative `G` in the direction
`y`. -/
theorem W1p.hasWeakLineDerivOn_inner_gradient_comm {U : W1p μ Ω p} {y w : E} {G : E → ℝ}
    (hG : HasWeakLineDerivOn μ Ω (fun x => ⟪W1p.gradient U x, y⟫_ℝ) G w) :
    HasWeakLineDerivOn μ Ω (fun x => ⟪W1p.gradient U x, w⟫_ℝ) G y := by
  have hfd : ∀ z, HasWeakLineDerivOn μ Ω (W1p.value U) (fun x => ⟪W1p.gradient U x, z⟫_ℝ) z :=
    fun z => by simpa only [innerSL_apply_apply] using (W1p.hasWeakFDerivOn U).hasWeakLineDerivOn z
  exact (hfd y).comm hG (hfd w)

end W1p

end TauCeti
