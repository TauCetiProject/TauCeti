/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Differentiability of functions pre-composed with absolute value

If the even reflection `s ↦ f |s|` of a curve `f : ℝ → E` is differentiable at `t : ℝ`, then `f` is
differentiable at `|t|` when `t ≠ 0`, and right-differentiable on `Set.Ici |t|` at `|t|` for every
`t : ℝ` (including `t = 0`, where `s ↦ f |s|` depends only on the values of `f` on `[0, ∞)`).

Contrapositively, a curve that is nowhere right-differentiable on `[0, ∞)` reflects via `s ↦ f |s|`
to a curve on `ℝ` that is differentiable at no real number.

## Main statements

* `DifferentiableAt.differentiableAt_of_comp_abs` — differentiability of `s ↦ f |s|` at `t ≠ 0`
  implies `DifferentiableAt ℝ f |t|`.
* `DifferentiableAt.differentiableWithinAt_Ici_of_comp_abs` — differentiability of `s ↦ f |s|` at
  any `t : ℝ` implies `DifferentiableWithinAt ℝ f (Set.Ici |t|) |t|`.
-/

public section

open Filter Set
open scoped Topology

namespace DifferentiableAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {t : ℝ}

/-- If `s ↦ f |s|` is differentiable at `t ≠ 0`, then `f` is differentiable at `|t|`. -/
theorem differentiableAt_of_comp_abs (h : DifferentiableAt ℝ (fun s ↦ f |s|) t) (ht : t ≠ 0) :
    DifferentiableAt ℝ f |t| := by
  rcases ht.lt_or_gt with ht_neg | ht_pos
  · have hpos : 0 < -t := neg_pos.mpr ht_neg
    have h' : DifferentiableAt ℝ (fun s ↦ f |s|) (- -t) := by rwa [neg_neg]
    have hd_neg : DifferentiableAt ℝ (fun s ↦ f |-s|) (-t) :=
      h'.comp (-t) differentiableAt_id.fun_neg
    have heq : (fun s : ℝ ↦ f |-s|) =ᶠ[𝓝 (-t)] f := by
      filter_upwards [Ioi_mem_nhds hpos] with s (hs : 0 < s)
      rw [abs_neg, abs_of_pos hs]
    rw [abs_of_neg ht_neg]
    exact hd_neg.congr_of_eventuallyEq heq.symm
  · have heq : (fun s : ℝ ↦ f |s|) =ᶠ[𝓝 t] f := by
      filter_upwards [Ioi_mem_nhds ht_pos] with s (hs : 0 < s)
      rw [abs_of_pos hs]
    rw [abs_of_pos ht_pos]
    exact h.congr_of_eventuallyEq heq.symm

/-- If `s ↦ f |s|` is differentiable at `t : ℝ`, then `f` is right-differentiable at `|t|`. -/
theorem differentiableWithinAt_Ici_of_comp_abs (h : DifferentiableAt ℝ (fun s ↦ f |s|) t) :
    DifferentiableWithinAt ℝ f (Ici |t|) |t| := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [abs_zero]
    exact h.differentiableWithinAt.congr (fun s hs ↦ by rw [abs_of_nonneg hs]) (by simp)
  · exact (h.differentiableAt_of_comp_abs ht).differentiableWithinAt

end DifferentiableAt
