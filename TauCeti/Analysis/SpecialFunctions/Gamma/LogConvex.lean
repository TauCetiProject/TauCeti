/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Log-convexity of shifted and rescaled Gamma

Mathlib's `Real.convexOn_log_Gamma` states that `log ∘ Γ` is convex on `(0, ∞)`. This file
transports it along the affine maps `x ↦ (x + c)/m` with `c ≥ 0` and `m > 0`, which send `(0, ∞)`
into itself, and sums the results over a finite set of shifts.

## Main results

* `Real.convexOn_log_Gamma_add_div`: `x ↦ log Γ((x + c)/m)` is convex on `(0, ∞)`.
* `Real.convexOn_sum_log_Gamma_add_div`: `x ↦ ∑_{i ∈ s} log Γ((x + c i)/m)` is convex on `(0, ∞)`.

These are the log-convexity inputs of the Bohr–Mollerup proof of Gauss's multiplication formula.

The statements are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/Gamma/Multiplication.lean`.
-/

public section

open Finset

namespace Real

/-- For `c ≥ 0` and `m > 0`, `x ↦ log Γ((x + c)/m)` is convex on `(0, ∞)`. -/
theorem convexOn_log_Gamma_add_div {c m : ℝ} (hc : 0 ≤ c) (hm : 0 < m) :
    ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => log (Gamma ((x + c) / m))) := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx' : (x + c) / m ∈ Set.Ioi 0 :=
    div_pos (add_pos_of_pos_of_nonneg (Set.mem_Ioi.mp hx) hc) hm
  have hy' : (y + c) / m ∈ Set.Ioi 0 :=
    div_pos (add_pos_of_pos_of_nonneg (Set.mem_Ioi.mp hy) hc) hm
  have hcombo : a * ((x + c) / m) + b * ((y + c) / m) = (a * x + b * y + c) / m := by
    linear_combination (c / m) * hab
  simpa [smul_eq_mul, hcombo] using convexOn_log_Gamma.2 hx' hy' ha hb hab

/-- For shifts `c i ≥ 0` and `m > 0`, `x ↦ ∑_{i ∈ s} log Γ((x + c i)/m)` is convex on
`(0, ∞)`. -/
theorem convexOn_sum_log_Gamma_add_div {ι : Type*} (s : Finset ι) {c : ι → ℝ}
    (hc : ∀ i ∈ s, 0 ≤ c i) {m : ℝ} (hm : 0 < m) :
    ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => ∑ i ∈ s, log (Gamma ((x + c i) / m))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) (convex_Ioi 0)
  | insert i s hi ih =>
    simp_rw [sum_insert hi]
    exact (convexOn_log_Gamma_add_div (hc i (mem_insert_self i s)) hm).add
      (ih fun j hj => hc j (mem_insert_of_mem hj))

end Real
