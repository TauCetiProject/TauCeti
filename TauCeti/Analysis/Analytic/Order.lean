/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order

/-!
# The analytic order of products, power maps and derivatives

Extensions of Mathlib's analytic-order calculus: `analyticOrderNatAt` respects eventual equality,
the order is additive over finite products, composing with `q ↦ q ^ N` at `0` multiplies the order
by `N`, the power map `w ↦ w ^ m` recentred at `0` has order `m` there for `m ≠ 0`, and the
recentred function `f · - f x` has order `1` at `x` exactly when `deriv f x ≠ 0`. The finiteness a
zero count also needs is
`TauCeti.finite_setOf_mem_and_eq_zero_of_isCompact`, provided by
`TauCeti.Analysis.Analytic.IsolatedZeros`, which mentions no order.

## Main declarations

* `TauCeti.analyticOrderNatAt_congr`: eventual equality preserves the natural analytic order.
* `TauCeti.analyticOrderAt_prod`: the order of `∏ i ∈ s, F i` is `∑ i ∈ s`, of the orders.
* `TauCeti.analyticOrderAt_comp_pow_zero`: the order of `q ↦ f (q ^ N)` at `0` is `N` times
  the order of `f` at `0`.
* `TauCeti.analyticOrderAt_pow_sub_zero_pow`: the order of `w ↦ w ^ m - 0 ^ m` at `0` is `m`
  for `m ≠ 0`.
* `AnalyticAt.analyticOrderAt_sub_eq_one_iff_deriv_ne_zero`: `f · - f x` has order `1` at `x`
  exactly when `deriv f x ≠ 0`, the `iff` form of Mathlib's
  `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`.

## References

* [Mathlib PR #39083](https://github.com/leanprover-community/mathlib4/pull/39083)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {z₀ : 𝕜}

/-- Functions that agree near a point have the same natural analytic order there. -/
theorem analyticOrderNatAt_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f g : 𝕜 → E} (hfg : f =ᶠ[𝓝 z₀] g) :
    analyticOrderNatAt f z₀ = analyticOrderNatAt g z₀ := by
  rw [analyticOrderNatAt, analyticOrderNatAt, analyticOrderAt_congr hfg]

/-- The order is additive when taking a finite product of analytic functions. -/
theorem analyticOrderAt_prod {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜}
    (hF : ∀ i ∈ s, AnalyticAt 𝕜 (F i) z₀) :
    analyticOrderAt (∏ i ∈ s, F i) z₀ = ∑ i ∈ s, analyticOrderAt (F i) z₀ := by
  induction s using Finset.cons_induction with
  | empty => simp [analyticOrderAt_eq_zero]
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      analyticOrderAt_mul (hF a (Finset.mem_cons_self a s))
        (Finset.analyticAt_prod _ fun i hi ↦ hF i (Finset.mem_cons_of_mem hi)),
      ih fun i hi ↦ hF i (Finset.mem_cons_of_mem hi)]

/-- The analytic order of `q ↦ f (q ^ N)` at `0` is `N` times the analytic order of `f`
at `0`. -/
lemma analyticOrderAt_comp_pow_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} (hf : AnalyticAt 𝕜 f 0) {N : ℕ} (hN : 0 < N) :
    analyticOrderAt (fun q : 𝕜 ↦ f (q ^ N)) 0 = analyticOrderAt f 0 * N := by
  set g : 𝕜 → 𝕜 := fun q ↦ q ^ N with hg_def
  have hzero : g 0 = 0 := zero_pow hN.ne'
  have h_sub_eq : (fun x : 𝕜 ↦ g x - 0) = (id : 𝕜 → 𝕜) ^ N := funext fun x ↦ by simp [hg_def]
  -- The composite is definitionally the power lambda; `show … from rfl` records the
  -- identification once so the composition rule applies.
  rw [show (fun q : 𝕜 ↦ f (q ^ N)) = f ∘ g from rfl,
    AnalyticAt.analyticOrderAt_comp (hzero.symm ▸ hf) (analyticAt_id.pow N), hzero, h_sub_eq,
    analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
  simp

/-- The power map `w ↦ w ^ m`, recentred at `0`, has analytic order `m` at `0` when `m ≠ 0`. -/
theorem analyticOrderAt_pow_sub_zero_pow {m : ℕ} (hm : m ≠ 0) :
    analyticOrderAt (fun w : 𝕜 ↦ w ^ m - 0 ^ m) 0 = m := by
  have hpow : (fun w : 𝕜 ↦ w ^ m - 0 ^ m) = (· - 0) ^ m := funext fun w ↦ by simp [zero_pow hm]
  rw [hpow, analyticOrderAt_centeredMonomial]

/-- A function analytic at `x` has a simple zero of `f · - f x` at `x` exactly when its
derivative at `x` does not vanish: the `iff` form of Mathlib's
`AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`. -/
theorem _root_.AnalyticAt.analyticOrderAt_sub_eq_one_iff_deriv_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [CharZero 𝕜] {f : 𝕜 → E} {x : 𝕜}
    (hf : AnalyticAt 𝕜 f x) :
    analyticOrderAt (f · - f x) x = 1 ↔ deriv f x ≠ 0 := by
  rw [← hf.analyticOrderAt_deriv_add_one, ← hf.deriv.analyticOrderAt_eq_zero]
  simp

end TauCeti

end
