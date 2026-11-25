/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.WeakPNT

/-!
# A uniform form of `ψ(x) ∼ x`

From the prime number theorem `ψ(x) ∼ x` (Mathlib's `Chebyshev.isEquivalent_psi_id`), for every
`ε > 0` there is a constant `C` with `|ψ(y) - y| ≤ ε y + C` for every `y ≥ 0`, not only for large
`y`. On `[0, B]`, with `B` beyond which the asymptotic bound holds, both `ψ(y)` and `y` lie in
`[0, ψ(B) + B]`.

## Main results

* `Chebyshev.exists_abs_psi_sub_le`: `∀ ε > 0, ∃ C, ∀ y ≥ 0, |ψ(y) - y| ≤ ε y + C`.
-/

public section

open Filter
open scoped Chebyshev

namespace Chebyshev

/-- `|ψ(y) - y| ≤ ε y + C` for every `y ≥ 0`, for some `C` depending on `ε > 0`. -/
theorem exists_abs_psi_sub_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C, ∀ y, 0 ≤ y → |ψ y - y| ≤ ε * y + C := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp (isEquivalent_psi_id.isLittleO.def hε)
  set B := max A 0
  refine ⟨ψ B + B, fun y hy ↦ ?_⟩
  rcases le_total B y with hBy | hyB
  · have h := hA y ((le_max_left A 0).trans hBy)
    simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg hy] at h
    linarith [psi_nonneg B, le_max_right A 0]
  · have hψ := psi_mono hyB
    rw [abs_le]
    constructor <;> linarith [psi_nonneg y, mul_nonneg hε.le hy]

end Chebyshev
