/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.MeasureTheory.Integral.Exp.Damped
import TauCeti.MeasureTheory.Integral.RpowLaplace

/-!
# The remainder bound of Watson's lemma

If `G : ℝ → E`, with values in a real normed space, is `O(t^{s-1})` as `t → 0+`, then its
Laplace integral `∫₀^∞ e^{-xt} G(t) dt` is `O(x^{-s})` as `x → +∞`. One splits the integral at a
small `δ`: near `0` the bound on `G` gives `O(x^{-s})` through the Gamma integral, and beyond `δ`
the factor `e^{-xt}` contributes `O(e^{-δx})`, which is smaller than every power of `x`. This is
the estimate behind Watson's lemma, `Asymptotics.hasAsymptoticExpansion_laplace` of
`TauCeti.Analysis.LaplaceTransform.Watson`; it is kept apart from that file so that the real
estimate does not need the complex expansion, and apart from
`TauCeti.MeasureTheory.Integral.RpowLaplace` so that its importers do not need
`TauCeti.MeasureTheory.Integral.Exp.Damped`.

## Main results

* `TauCeti.isBigO_integral_exp_neg_mul_smul`: Watson's remainder bound. If `G(t) = O(t^{s-1})`
  as `t → 0+`, then `∫₀^∞ e^{-xt} G(t) dt = O(x^{-s})` as `x → +∞`. Near `0` it uses
  `TauCeti.norm_setIntegral_Ioc_exp_neg_mul_smul_le` of
  `TauCeti.MeasureTheory.Integral.RpowLaplace`, and beyond a small `δ` the tail bound
  `TauCeti.norm_setIntegral_Ioi_exp_neg_mul_smul_le` of
  `TauCeti.MeasureTheory.Integral.Exp.Damped`, which is `O(e^{-δx})`.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMFMathlib/Analysis/Asymptotics/Watson.lean`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Real Set Asymptotics Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `isBigO_integral_exp_neg_mul_smul` when `t ↦ e^{-σt} G(t)` is integrable on `(0, ∞)`. -/
private theorem isBigO_integral_exp_neg_mul_smul_of_integrableOn {G : ℝ → E} {s σ : ℝ}
    (hint : IntegrableOn (fun t => Real.exp (-σ * t) • G t) (Ioi 0))
    (hG : G =O[𝓝[>] 0] fun t => t ^ (s - 1)) :
    (fun x : ℝ => ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) • G t) =O[atTop] fun x => x ^ (-s) := by
  set A := ∫ t in Ioi (0 : ℝ), ‖Real.exp (-σ * t) • G t‖
  rcases le_or_gt s 0 with hs | hs
  · -- for `s ≤ 0` the integral is at most `A ≤ A x^{-s}`
    refine IsBigO.of_bound A ?_
    filter_upwards [eventually_ge_atTop σ, eventually_ge_atTop 1] with x hxσ hx1
    have h := norm_setIntegral_Ioi_exp_neg_mul_smul_le hint hxσ
    rw [mul_zero, Real.exp_zero, one_mul] at h
    refine h.trans (le_mul_of_one_le_right (integral_nonneg fun _ => norm_nonneg _) ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact Real.one_le_rpow hx1 (neg_nonneg.mpr hs)
  -- the bound `‖G t‖ ≤ K t^{s-1}` on `(0, δ]`
  obtain ⟨K, hK0, hK⟩ := hG.exists_pos
  obtain ⟨δ, hδ0, hδ⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hK.bound
  have hδ0 : 0 < δ := hδ0
  have hGb (t : ℝ) (ht : t ∈ Ioc 0 δ) : ‖G t‖ ≤ K * t ^ (s - 1) := by
    simpa [abs_of_nonneg (Real.rpow_nonneg ht.1.le _)] using hδ ht
  have hAle : ∫ t in Ioi δ, ‖Real.exp (-σ * t) • G t‖ ≤ A :=
    setIntegral_mono_set hint.norm (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall (Ioi_subset_Ioi hδ0.le))
  -- `e^{-δx}` is eventually smaller than `x^{-s}`
  have hexp : ∀ᶠ x in atTop, Real.exp (-δ * x) ≤ x ^ (-s) := by
    filter_upwards [(isLittleO_exp_neg_mul_rpow_atTop hδ0 (-s)).bound one_pos,
      eventually_gt_atTop 0] with x hx hx0
    rwa [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
  refine IsBigO.of_bound (K * Real.Gamma s + Real.exp (σ * δ) * A) ?_
  filter_upwards [hexp, eventually_ge_atTop σ, eventually_gt_atTop 0] with x hxe hxσ hx0
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), add_mul]
  have hI : IntegrableOn (fun t => Real.exp (-x * t) • G t) (Ioi 0) :=
    integrable_exp_neg_mul_smul_of_le hint
      ((ae_restrict_mem measurableSet_Ioi).mono fun _ ht => le_of_lt ht) hxσ
  rw [← intervalIntegral.integral_interval_add_Ioi hI (hI.mono_set (Ioi_subset_Ioi hδ0.le)),
    intervalIntegral.integral_of_le hδ0.le]
  refine (norm_add_le _ _).trans
    (add_le_add (norm_setIntegral_Ioc_exp_neg_mul_smul_le hs hx0 hK0.le hGb) ?_)
  -- the tail: `e^{-(x-σ)δ} = e^{σδ} e^{-δx}`
  refine (norm_setIntegral_Ioi_exp_neg_mul_smul_le
    (hint.mono_set (Ioi_subset_Ioi hδ0.le)) hxσ).trans ?_
  have hsplit : -(x - σ) * δ = σ * δ + -δ * x := by ring
  rw [hsplit, Real.exp_add, mul_right_comm]
  gcongr

/-- **Watson's remainder bound.** If `G(t) = O(t^{s-1})` as `t → 0+`, then
`∫₀^∞ e^{-xt} G(t) dt = O(x^{-s})` as `x → +∞`. If `t ↦ e^{-xt} G(t)` is integrable on `(0, ∞)`
for no `x`, every integral is `0` and the bound holds trivially. -/
theorem isBigO_integral_exp_neg_mul_smul {G : ℝ → E} {s : ℝ}
    (hG : G =O[𝓝[>] 0] fun t => t ^ (s - 1)) :
    (fun x : ℝ => ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) • G t) =O[atTop] fun x => x ^ (-s) := by
  by_cases hex : ∃ σ, IntegrableOn (fun t => Real.exp (-σ * t) • G t) (Ioi 0)
  · obtain ⟨σ, hint⟩ := hex
    exact isBigO_integral_exp_neg_mul_smul_of_integrableOn hint hG
  · simp only [not_exists] at hex
    have h0 : (fun x : ℝ => ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) • G t) = 0 :=
      funext fun x => integral_undef (hex x)
    rw [h0]
    exact isBigO_zero _ _

end TauCeti
