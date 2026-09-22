/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.FieldSimp

/-!
# Real asymptotic estimates

This file provides general-purpose results for real-valued asymptotic estimates. In particular,
convergence of a quotient to a constant can be restated as a linear little-`o` estimate for the
corresponding remainder.

## Main results

* `TauCeti.isLittleO_sub_mul_id_of_tendsto_div`: if `f x / x` tends to `δ`, then
  `f x - δ * x = o(x)`.
-/

public section

namespace TauCeti

open Asymptotics Filter
open scoped Topology

/-- A quotient limit for a function gives the corresponding linear little-`o` remainder. -/
theorem isLittleO_sub_mul_id_of_tendsto_div {f : ℝ → ℝ} {δ : ℝ}
    (h : Tendsto (fun x : ℝ ↦ f x / x) atTop (𝓝 δ)) :
    (fun x : ℝ ↦ f x - δ * x) =o[atTop] fun x : ℝ ↦ x := by
  refine (isLittleO_iff_tendsto'
    ((eventually_ne_atTop (0 : ℝ)).mono fun _ hx hzero ↦ (hx hzero).elim)).2 ?_
  have h' := h.sub_const δ
  rw [sub_self] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  field_simp

end TauCeti
