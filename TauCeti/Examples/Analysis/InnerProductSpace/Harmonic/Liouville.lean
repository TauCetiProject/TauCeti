/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Decay
import TauCeti.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# A linear function is harmonic and unbounded

Liouville's theorem (`InnerProductSpace.HarmonicOnNhd.exists_const_forall_eq_of_bounded`) says
that a bounded harmonic function on a finite-dimensional real inner product space is constant.
This file checks that its boundedness hypothesis is load-bearing. For `v ≠ 0` the linear function
`u = ⟪v, ·⟫`, which on `ℝⁿ` with `v = e₁` is the coordinate `x₁`, is harmonic on the whole space,
like every continuous linear map (`ContinuousLinearMap.harmonicOnNhd`), and it is not constant, as
`u 0 = 0` while `u v = ‖v‖²`. Liouville's theorem therefore forces its range to be unbounded
(`TauCeti.Examples.Liouville.not_isBounded_range_inner`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §2.2.3, Theorem 8 (Liouville's
  theorem).
-/

public section

namespace TauCeti.Examples.Liouville

open InnerProductSpace Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The boundedness hypothesis of Liouville's theorem is needed.** For `v ≠ 0` the harmonic
function `x ↦ ⟪v, x⟫` is not constant, so by Liouville's theorem its range is unbounded. -/
theorem not_isBounded_range_inner {v : E} (hv : v ≠ 0) :
    ¬Bornology.IsBounded (range fun x : E ↦ ⟪v, x⟫) := fun hb ↦ by
  obtain ⟨c, hc⟩ := ((innerSL ℝ v).harmonicOnNhd (s := univ)).exists_const_forall_eq_of_bounded
    (by simpa using hb)
  have h0 : c = 0 := by simpa using (hc 0).symm
  have hv' : ‖v‖ ^ 2 = 0 := by simpa [h0, real_inner_self_eq_norm_sq] using hc v
  exact hv (by simpa using hv')

end TauCeti.Examples.Liouville
