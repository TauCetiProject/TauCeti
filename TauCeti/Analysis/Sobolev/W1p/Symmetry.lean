/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry

/-!
# Symmetry of second weak derivatives of `W^{1,p}` functions

The first weak derivatives `∂_y u = ⟪∇u, y⟫` of a Sobolev function `u ∈ W^{1,p}(Ω)` are
weak derivatives of `u` itself, so the commutation of weak derivatives
(`TauCeti.HasWeakLineDerivOn.comm`) applies to them: if `∂_y u` has a weak derivative `G` in the
direction `w`, then `∂_w u` has the same weak derivative `G` in the direction `y`.

## Main declarations

* `TauCeti.W1p.hasWeakLineDerivOn_inner_gradient_comm`: second weak derivatives of a
  `W^{1,p}` function are symmetric.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace

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

end TauCeti
