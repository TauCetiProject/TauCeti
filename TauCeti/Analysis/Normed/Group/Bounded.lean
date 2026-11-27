/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Real-valued functions at infinity in a seminormed group

Along the filter `cobounded E` of complements of bounded sets, an eventual property is one that
holds beyond some radius, `R ≤ ‖x‖` (`Filter.hasBasis_cobounded_norm`). This file records two
consequences for a real-valued function `g` on a seminormed additive group `E`.

* If `g` tends to `a < δ` along `cobounded E`, then `g x ≤ δ` once `‖x‖` exceeds some radius.
* A power bound `g x ≤ K ‖x‖ ^ b` beyond some radius makes the weighted function
  `‖x‖ ^ c g x` tend to zero along `cobounded E` when `g ≥ 0` and `c + b < 0`.

In a proper space, such as a finite-dimensional real vector space, `cobounded E` is the
cocompact filter (`Metric.cobounded_eq_cocompact`), so both apply to limits at infinity there.
-/

public section

namespace TauCeti

open Bornology Filter Topology

variable {E : Type*} [SeminormedAddGroup E] {g : E → ℝ}

/-- If `g` tends to `a < δ` along `cobounded E`, then `g x ≤ δ` for all `x` beyond some radius. -/
theorem exists_forall_le_of_tendsto_cobounded {a δ : ℝ} (hg : Tendsto g (cobounded E) (𝓝 a))
    (hδ : a < δ) : ∃ R, ∀ x : E, R ≤ ‖x‖ → g x ≤ δ := by
  obtain ⟨R, -, hR⟩ :=
    hasBasis_cobounded_norm.eventually_iff.1 (hg.eventually (ge_mem_nhds hδ))
  exact ⟨R, fun x hx => hR hx⟩

/-- A power bound `g x ≤ K ‖x‖ ^ b` beyond some radius makes `‖x‖ ^ c g x` tend to zero along
`cobounded E`, for nonnegative `g` and `c + b < 0`. -/
theorem tendsto_norm_rpow_mul_cobounded_of_le {R K b c : ℝ} (hbc : c + b < 0)
    (hg0 : ∀ x, 0 ≤ g x) (hg : ∀ x : E, R ≤ ‖x‖ → g x ≤ K * ‖x‖ ^ b) :
    Tendsto (fun x => ‖x‖ ^ c * g x) (cobounded E) (𝓝 0) := by
  have hlim : Tendsto (fun x : E => K * ‖x‖ ^ (c + b)) (cobounded E) (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (y := -(c + b)) (by linarith)).comp
      (tendsto_norm_cobounded_atTop (E := E))).const_mul K
    rw [mul_zero] at h
    exact h.congr fun x => by simp only [Function.comp_apply, neg_neg]
  refine squeeze_zero' (Eventually.of_forall fun x => mul_nonneg (by positivity) (hg0 x)) ?_ hlim
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop (max R 1)] with x hx
  have hx0 : 0 < ‖x‖ := zero_lt_one.trans_le ((le_max_right _ _).trans hx)
  calc ‖x‖ ^ c * g x ≤ ‖x‖ ^ c * (K * ‖x‖ ^ b) :=
        mul_le_mul_of_nonneg_left (hg x ((le_max_left _ _).trans hx)) (by positivity)
    _ = K * ‖x‖ ^ (c + b) := by rw [Real.rpow_add hx0]; ring

end TauCeti
