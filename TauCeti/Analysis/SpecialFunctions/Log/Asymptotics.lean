/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Asymptotics of the scale `x / log x`

The Chebyshev scale `x / log x` diverges, and it can be inverted asymptotically: if `u → ∞` and
`u / log u ∼ v`, then taking logarithms gives `log u - log log u ∼ log v`, and
`log log u = o(log u)`, so `log u ∼ log v`; multiplying, `u = (u / log u) · log u ∼ v log v`.

## Main declarations

* `TauCeti.Real.tendsto_div_log_atTop` — `x / log x → ∞` as `x → ∞`.
* `Asymptotics.IsEquivalent.log_of_div_log`, `Asymptotics.IsEquivalent.of_div_log` — inversion of
  the scale `x / log x`: if `u → ∞` and `u / log u ∼ v`, then `log u ∼ log v` and
  `u ∼ v log v`.
-/

public section

open Filter Topology

namespace TauCeti.Real

/-- **The Chebyshev scale `x / log x` diverges.**  Equivalently, a constant is `o (x / log x)`. -/
theorem tendsto_div_log_atTop : Tendsto (fun x : ℝ ↦ x / Real.log x) atTop atTop := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  simp only [id_eq] at hlog
  have h : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlog ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  exact h.inv_tendsto_nhdsGT_zero.congr fun x ↦ inv_div _ _

end TauCeti.Real

namespace Asymptotics.IsEquivalent

variable {α : Type*} {l : Filter α} {u v : α → ℝ}

/-- If `u → ∞` and `u / log u ∼ v`, then `log u ∼ log v`. -/
theorem log_of_div_log (hu : Tendsto u l atTop)
    (h : (fun x ↦ u x / Real.log (u x)) ~[l] v) :
    (fun x ↦ Real.log (u x)) ~[l] fun x ↦ Real.log (v x) := by
  have hlogu := Real.tendsto_log_atTop.comp hu
  have hv := h.tendsto_atTop (TauCeti.Real.tendsto_div_log_atTop.comp hu)
  refine IsEquivalent.trans ?_ (h.log hv)
  have hsub : (fun x ↦ Real.log (u x) - Real.log (Real.log (u x))) ~[l]
      fun x ↦ Real.log (u x) :=
    IsEquivalent.refl.sub_isLittleO (Real.isLittleO_log_id_atTop.comp_tendsto hlogu)
  refine (hsub.congr_left ?_).symm
  filter_upwards [hu.eventually_gt_atTop 1] with x hx
  rw [Real.log_div (by linarith) (Real.log_pos hx).ne']

/-- **Asymptotic inversion of `x / log x`.** If `u → ∞` and `u / log u ∼ v`, then
`u ∼ v log v`. -/
theorem of_div_log (hu : Tendsto u l atTop) (h : (fun x ↦ u x / Real.log (u x)) ~[l] v) :
    u ~[l] fun x ↦ v x * Real.log (v x) := by
  refine (h.mul (h.log_of_div_log hu)).congr_left ?_
  filter_upwards [hu.eventually_gt_atTop 1] with x hx
  exact div_mul_cancel₀ _ (Real.log_pos hx).ne'

end Asymptotics.IsEquivalent
