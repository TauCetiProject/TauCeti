/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The time change of a positive periodic speed

Let `h : ℝ → ℝ` be continuous, positive and `T`-periodic with `T > 0`. The new time
`θ t = ∫₀ᵗ 1 / h` is a strictly increasing homeomorphism of `ℝ` fixing `0`, and it is additive
along the period: `θ (t + T) = θ t + θ T`. Its inverse `ψ` therefore shifts by `T` along the
period `θ T`, and has derivative `h ∘ ψ`. This is the change of time which turns an integral
curve of a vector field `X` into one of `h • X`.

## Main results

* `Function.Periodic.exists_homeomorph_hasDerivAt_of_pos`: the inverse time change `ψ`, with
  its normalization, its period shift and its derivative.
-/

public section

namespace Function

/-- **The time change of a positive periodic speed.** For a continuous, positive function `h`
of positive period `T`, the inverse `ψ` of `θ t = ∫₀ᵗ 1 / h` is a homeomorphism of `ℝ` fixing
`0`, which shifts by `T` along the period `θ T` of the new time and has derivative `h ∘ ψ`. -/
theorem Periodic.exists_homeomorph_hasDerivAt_of_pos {h : ℝ → ℝ} {T : ℝ} (hhT : Periodic h T)
    (hT : 0 < T) (hh : Continuous h) (hpos : ∀ t, 0 < h t) :
    ∃ ψ : ℝ ≃ₜ ℝ, ψ 0 = 0 ∧ (∃ T', T' ≠ 0 ∧ ∀ s, ψ (s + T') = ψ s + T) ∧
      ∀ s, HasDerivAt ψ (h (ψ s)) s := by
  set k : ℝ → ℝ := fun t ↦ (h t)⁻¹
  have hk : Continuous k := hh.inv₀ fun t ↦ (hpos t).ne'
  have hkpos : ∀ t, 0 < k t := fun t ↦ inv_pos.2 (hpos t)
  have hkT : Periodic k T := fun t ↦ by simp only [k, hhT t]
  set θ : ℝ → ℝ := fun t ↦ ∫ u in (0 : ℝ)..t, k u
  have hθd : ∀ t, HasDerivAt θ (k t) t := fun t ↦ (hk.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hθc : Continuous θ := continuous_iff_continuousAt.2 fun t ↦ (hθd t).continuousAt
  have hθmono : StrictMono θ := strictMono_of_hasDerivAt_pos hθd hkpos
  have hθ0 : θ 0 = 0 := intervalIntegral.integral_same
  -- `θ` is additive along the period, because `1 / h` is periodic, and it is onto.
  have hθT : ∀ t, θ (t + T) = θ t + θ T := fun t ↦ by
    simpa only [θ, zero_add] using
      hkT.intervalIntegral_add_eq_add 0 t fun _ _ ↦ hk.intervalIntegrable _ _
  have hθsurj : Surjective θ := hθc.surjective
    (hkT.tendsto_atTop_intervalIntegral_of_pos' (hk.intervalIntegrable 0 T) hkpos hT)
    (hkT.tendsto_atBot_intervalIntegral_of_pos' (hk.intervalIntegrable 0 T) hkpos hT)
  set ψ : ℝ ≃ₜ ℝ := (hθmono.orderIsoOfSurjective θ hθsurj).symm.toHomeomorph
  have hθψ : ∀ s, θ (ψ s) = s := fun s ↦ (hθmono.orderIsoOfSurjective θ hθsurj).apply_symm_apply s
  have hψθ : ∀ t, ψ (θ t) = t := fun t ↦ (hθmono.orderIsoOfSurjective θ hθsurj).symm_apply_apply t
  refine ⟨ψ, by simpa [hθ0] using hψθ 0, ⟨θ T, (hθ0.symm.trans_lt (hθmono hT)).ne',
    fun s ↦ by rw [← hθψ s, hψθ, ← hθT, hψθ]⟩, fun s ↦ ?_⟩
  simpa [k] using (hθd (ψ s)).of_local_left_inverse ψ.continuous.continuousAt (hkpos _).ne'
    (Filter.Eventually.of_forall hθψ)

end Function
