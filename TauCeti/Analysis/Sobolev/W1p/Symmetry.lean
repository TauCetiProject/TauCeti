/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry

/-!
# Symmetry of second weak derivatives of `W^{1,p}` functions

The first weak derivatives `∂_y u = ⟪∇u, y⟫` of a Sobolev function `u ∈ W^{1,p}(Ω)` are
weak derivatives of `u` itself, so the commutation of weak derivatives
(`TauCeti.HasWeakLineDerivOn.comm`) applies to them: if `∂_y u` has a weak derivative `G` in the
direction `w`, then `∂_w u` has the same weak derivative `G` in the direction `y`. Tested against
a test function `ψ`, the first weak derivatives of `u` pair symmetrically with those of `ψ`:
`∫ (∂_v ψ) ∂_w u = ∫ (∂_w ψ) ∂_v u`, as both equal `-∫ (∂_v ∂_w ψ) u`.

## Main declarations

* `TauCeti.W1p.hasWeakLineDerivOn_inner_gradient`: the weak line derivative of a `W^{1,p}`
  function in the direction `z` is `⟪∇u, z⟫`.
* `TauCeti.W1p.hasWeakLineDerivOn_inner_gradient_comm`: second weak derivatives of a
  `W^{1,p}` function are symmetric.
* `TauCeti.W1p.integral_lineDeriv_smul_inner_gradient_comm`: first derivatives of a test function
  and of a `W^{1,p}` function pair symmetrically.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- The weak line derivative of `u ∈ W^{1,p}(Ω)` in the direction `z` is `⟪∇u, z⟫`. -/
theorem W1p.hasWeakLineDerivOn_inner_gradient (U : W1p μ Ω p) (z : E) :
    HasWeakLineDerivOn μ Ω (W1p.value U) (fun x => ⟪W1p.gradient U x, z⟫_ℝ) z := by
  simpa only [innerSL_apply_apply] using (W1p.hasWeakFDerivOn U).hasWeakLineDerivOn z

/-- **Second derivatives of a Sobolev function are symmetric.** If `∂_y u = ⟪∇u, y⟫` has the weak
derivative `G` in the direction `w`, then `∂_w u` has the weak derivative `G` in the direction
`y`. -/
theorem W1p.hasWeakLineDerivOn_inner_gradient_comm {U : W1p μ Ω p} {y w : E} {G : E → ℝ}
    (hG : HasWeakLineDerivOn μ Ω (fun x => ⟪W1p.gradient U x, y⟫_ℝ) G w) :
    HasWeakLineDerivOn μ Ω (fun x => ⟪W1p.gradient U x, w⟫_ℝ) G y :=
  (W1p.hasWeakLineDerivOn_inner_gradient U y).comm hG (W1p.hasWeakLineDerivOn_inner_gradient U w)

open LineDeriv in
/-- **Symmetric pairing of first derivatives.** For `u ∈ W^{1,p}(Ω)`, a test function `ψ` on `Ω`
and directions `v`, `w`, `∫ (∂_v ψ) ⟪∇u, w⟫ = ∫ (∂_w ψ) ⟪∇u, v⟫`: integrating by parts, both
sides are `-∫ (∂_w ∂_v ψ) u`, and derivatives of test functions commute. -/
theorem W1p.integral_lineDeriv_smul_inner_gradient_comm (U : W1p μ Ω p) (ψ : 𝓓(Ω, ℝ)) (v w : E) :
    ∫ x, lineDeriv ℝ (ψ : E → ℝ) x v • ⟪W1p.gradient U x, w⟫_ℝ ∂μ =
      ∫ x, lineDeriv ℝ (ψ : E → ℝ) x w • ⟪W1p.gradient U x, v⟫_ℝ ∂μ := by
  have h := fun z z' : E =>
    (W1p.hasWeakLineDerivOn_inner_gradient U z).integral_lineDeriv_smul_eq_neg_integral_smul
      (∂_{z'} ψ)
  simp only [TestFunction.lineDerivOp_apply] at h
  rw [← neg_neg (∫ x, _ ∂μ), ← h w v]
  simp_rw [TestFunction.lineDeriv_lineDerivOp_comm ψ v w]
  rw [h v w, neg_neg]

end TauCeti
