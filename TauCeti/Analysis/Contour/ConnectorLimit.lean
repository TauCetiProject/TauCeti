/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Vanishing of horizontal and vertical connector integrals

Contour shifts in the complex plane close a contour with horizontal segments `[d, c] + iT` or
vertical segments `σ + i[a, b]`, and then send the connector to infinity. When the integrand tends
to `0` uniformly along the connector, its integral tends to `0`.

## Main results

* `TauCeti.Contour.tendsto_intervalIntegral_horizontal`: if `H (σ + iT) → 0` as `T` tends along a
  filter, uniformly for `σ` between `d` and `c`, then `∫ σ in d..c, H (σ + T * I)` tends to `0`.
* `TauCeti.Contour.tendsto_intervalIntegral_vertical_atBot`: if `f s → 0` as `Re s → -∞`,
  uniformly for `Im s ∈ [a, b]`, then `∫ y in a..b, f (σ + y * I)` tends to `0` as `σ → -∞`.
-/

public section

open Complex Filter Set
open scoped Interval Topology

namespace TauCeti.Contour

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `H(σ + iT) → 0` as `T` tends along `l`, uniformly for `σ` between `d` and `c`, then the
horizontal connector `∫_d^c H(σ + iT) dσ` tends to `0` along `l`. -/
theorem tendsto_intervalIntegral_horizontal {H : ℂ → E} {c d : ℝ} {l : Filter ℝ}
    (h : Tendsto (fun q : ℝ × ℝ => H (q.2 + q.1 * I)) (l ×ˢ 𝓟 (uIcc d c)) (𝓝 0)) :
    Tendsto (fun T : ℝ => ∫ σ in d..c, H (σ + T * I)) l (𝓝 0) :=
  TendstoUniformlyOn.tendsto_intervalIntegral_nhds_zero (tendsto_prod_principal_iff.mp h)

/-- If `f s → 0` as `Re s → -∞` uniformly for `Im s ∈ [a, b]` (`a ≤ b`), then the vertical
connector integral `∫ y in a..b, f (σ + y * I)` tends to `0` as `σ → -∞`. -/
theorem tendsto_intervalIntegral_vertical_atBot {f : ℂ → E} {a b : ℝ} (hab : a ≤ b)
    (hdecay : Tendsto f (comap Complex.re atBot ⊓ 𝓟 {s : ℂ | a ≤ s.im ∧ s.im ≤ b}) (𝓝 0)) :
    Tendsto (fun σ : ℝ ↦ ∫ y : ℝ in a..b, f ((σ : ℂ) + y * I)) atBot (𝓝 0) := by
  have hmap : Tendsto (fun q : ℝ × ℝ ↦ (q.1 : ℂ) + q.2 * I)
      (atBot ×ˢ 𝓟 (uIcc a b))
      (comap Complex.re atBot ⊓ 𝓟 {s : ℂ | a ≤ s.im ∧ s.im ≤ b}) := by
    refine tendsto_inf.2 ⟨?_, ?_⟩
    · rw [tendsto_comap_iff]
      simpa [Function.comp_def] using (tendsto_fst : Tendsto Prod.fst (atBot ×ˢ 𝓟 (uIcc a b)) atBot)
    · rw [tendsto_principal, Filter.eventually_prod_iff]
      refine ⟨fun _ ↦ True, .of_forall fun _ ↦ trivial, fun y ↦ y ∈ uIcc a b,
        eventually_principal.2 fun _ h ↦ h, fun {_} _ {_} hy ↦ ?_⟩
      rw [uIcc_of_le hab] at hy
      simpa using hy
  exact TendstoUniformlyOn.tendsto_intervalIntegral_nhds_zero
    (tendsto_prod_principal_iff.mp (hdecay.comp hmap))

end TauCeti.Contour
