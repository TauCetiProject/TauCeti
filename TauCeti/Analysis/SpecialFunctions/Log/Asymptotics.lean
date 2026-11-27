/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Asymptotics of the scale `x / log x`

The Chebyshev scale `x / log x` (and more generally `x / log x ^ n`) diverges, and it can be
inverted asymptotically: if `u → ∞` and `u / log u ∼ v`, then taking logarithms gives
`log u - log log u ∼ log v`, and `log log u = o(log u)`, so `log u ∼ log v`; multiplying,
`u = (u / log u) · log u ∼ v log v`.

## Main declarations

* `TauCeti.Real.tendsto_div_log_pow_atTop` — `x / log x ^ n → +∞` as `x → +∞` for every `n : ℕ`.
* `TauCeti.Real.isLittleO_const_div_log_pow`, `TauCeti.Real.isLittleO_const_div_log` — a constant
  is `o(x / log x ^ n)` and `o(x / log x)` as `x → ∞`.
* `TauCeti.Real.tendsto_div_log_atTop` — `x / log x → ∞` as `x → ∞`.
* `Asymptotics.IsEquivalent.log_of_div_log`, `Asymptotics.IsEquivalent.of_div_log` — inversion of
  the scale `x / log x`: if `u → ∞` and `u / log u ∼ v`, then `log u ∼ log v` and
  `u ∼ v log v`.
-/

public section

open Asymptotics Filter Topology

namespace TauCeti.Real

/-- For every `n : ℕ`, `x / log x ^ n → +∞` as `x → +∞`. -/
theorem tendsto_div_log_pow_atTop (n : ℕ) :
    Tendsto (fun x : ℝ ↦ x / Real.log x ^ n) atTop atTop := by
  have hlog : Tendsto (fun x : ℝ ↦ Real.log x ^ n / x) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have hpos : Tendsto (fun x : ℝ ↦ Real.log x ^ n / x) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlog <| by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact div_pos (pow_pos (Real.log_pos hx) n) (zero_lt_one.trans hx)
  exact hpos.inv_tendsto_nhdsGT_zero.congr fun x ↦ inv_div _ _

/-- **The Chebyshev scale `x / log x` diverges.**  Equivalently, a constant is `o (x / log x)`. -/
theorem tendsto_div_log_atTop : Tendsto (fun x : ℝ ↦ x / Real.log x) atTop atTop := by
  simpa only [pow_one] using tendsto_div_log_pow_atTop 1

/-- A constant is `o(x / log x ^ n)` as `x → ∞` for every `n : ℕ`. -/
theorem isLittleO_const_div_log_pow (c : ℝ) (n : ℕ) :
    (fun _ : ℝ ↦ c) =o[atTop] fun x : ℝ ↦ x / Real.log x ^ n :=
  isLittleO_const_left.mpr <| Or.inr <|
    (tendsto_abs_atTop_atTop.comp (tendsto_div_log_pow_atTop n)).congr fun _ ↦
      (Real.norm_eq_abs _).symm

/-- A constant is `o(x / log x)` as `x → ∞`, because that scale diverges. -/
theorem isLittleO_const_div_log (c : ℝ) :
    (fun _ : ℝ ↦ c) =o[atTop] fun x : ℝ ↦ x / Real.log x := by
  simpa only [pow_one] using isLittleO_const_div_log_pow c 1

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
