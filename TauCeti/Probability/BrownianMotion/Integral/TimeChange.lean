/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Wiener
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import TauCeti.Probability.BrownianMotion.Integral.ByParts
import TauCeti.Probability.BrownianMotion.Version
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import TauCeti.Probability.Moments.Covariance

/-!
# Wiener integrals along a deterministic time change

Let `B` be a pre-Brownian motion, `k : ℝ≥0 → ℝ` a deterministic integrand and
`a : ℝ≥0 → ℝ≥0` a time change with `∫₀^{a t} k² = t` for every `t`. Then the Wiener integrals
`M_t = ∫₀^{a t} k dB` form a pre-Brownian motion
(`ProbabilityTheory.IsPreBrownianReal.isPreBrownianReal_of_ae_eq_wienerIntegral`). They are
jointly Gaussian and centered, and their covariance is `∫₀^{min (a s) (a t)} k² = min s t`
because `c ↦ ∫₀^c k²` is monotone. No monotonicity of `a` is assumed: it follows from the
normalization on the times where `k` does not vanish.

This is the deterministic case of the Dambis–Dubins–Schwarz time change. Combined with
integration by parts for Wiener integrals, it identifies explicit pathwise transforms of a
Brownian motion `b` as Brownian motions: if `h` is continuous on `[0, ∞)`, differentiable on
`(0, ∞)` and normalized by `∫₀^{a t} h² = t`, then a process with continuous paths equal at each
time almost surely to `h (a t) b_{a t} - ∫₀^{a t} h' u b_u du` is a Brownian motion
(`ProbabilityTheory.IsBrownianReal.isBrownianReal_of_ae_eq_mul_sub_integral`). Examples are the
Ornstein–Uhlenbeck time changes `t ↦ ∫₀^{e^t - 1} (1 + r)^{-1/2} db_r` and
`s ↦ ∫₀^{log (1 + s)} e^{u/2} db_u`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2 and §3.4.A.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Wiener integrals along a time change form a pre-Brownian motion.** Let `f t` be an `L²`
class on the horizon `a t` represented by a fixed integrand `k`, normalized by
`∫₀^{a t} k² = t`. A process `X` with `X t = ∫₀^{a t} k dB` almost surely at each time is a
pre-Brownian motion. -/
theorem isPreBrownianReal_of_ae_eq_wienerIntegral (hB : IsPreBrownianReal B P)
    {a : ℝ≥0 → ℝ≥0} {k : ℝ≥0 → ℝ} {f : ∀ t, Lp ℝ 2 (timeMeasure (a t))}
    (hf : ∀ t, f t =ᵐ[timeMeasure (a t)] k) (hk : ∀ t, ∫ s, k s ^ 2 ∂timeMeasure (a t) = t)
    {X : ℝ≥0 → Ω → ℝ} (hX : ∀ t, X t =ᵐ[P] hB.wienerIntegral (a t) (f t)) :
    IsPreBrownianReal X P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  -- Every integral may be read on any longer horizon.
  have hext (t : ℝ≥0) {T : ℝ≥0} (hT : a t ≤ T) :
      X t =ᵐ[P] hB.wienerIntegral T (timeMeasureExtendLp ℝ hT (f t)) := by
    rw [wienerIntegral_timeMeasureExtendLp]
    exact hX t
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ⟨fun I ↦ ?_⟩ (fun t ↦ ?_)
    (fun s t hst ↦ ?_)
  · -- On a finite set of times, all integrals live on the largest horizon.
    classical
    let g : ℝ≥0 → Lp ℝ 2 (timeMeasure (I.sup a)) := fun t ↦
      if h : a t ≤ I.sup a then timeMeasureExtendLp ℝ h (f t) else 0
    refine (((hB.isGaussianProcess_wienerIntegral _).comp_right g).hasGaussianLaw I).congr ?_
    filter_upwards [ae_all_iff.2 fun i : I ↦ hext i (Finset.le_sup i.property)] with ω hω
    ext i
    simp [g, Finset.le_sup i.property, hω i]
  · rw [integral_congr_ae (hX t), integral_wienerIntegral]
  · rw [TauCeti.covariance_congr_ae (hext s (le_max_left (a s) (a t)))
      (hext t (le_max_right (a s) (a t))), covariance_wienerIntegral,
      inner_timeMeasureExtendLp _ _ (hf s) (hf t)]
    rcases le_total (a s) (a t) with hle | hle
    · rw [min_eq_left hle, hk]
    -- If `a t ≤ a s`, then `t ≤ s` by monotonicity of `c ↦ ∫₀^c k²`, so `s = t`.
    rw [min_eq_right hle, hk]
    refine le_antisymm ?_ (NNReal.coe_le_coe.2 hst)
    rw [← hk t, ← hk s]
    exact integral_mono_measure (timeMeasure_mono hle) (.of_forall fun _ ↦ sq_nonneg _)
      ((Lp.memLp (f s)).integrable_sq.congr ((hf s).mono fun _ h ↦ by simp only [h]))

end ProbabilityTheory.IsPreBrownianReal

namespace ProbabilityTheory.IsBrownianReal

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ}

/-- **Brownian motion from a pathwise integration by parts formula.** Let `h` be continuous on
`[0, ∞)` and differentiable on `(0, ∞)` with derivative `h'`, interval integrable up to each
`a t`, and normalized by `∫₀^{a t} h² = t`. A process with almost surely continuous paths that
equals `h (a t) b_{a t} - ∫₀^{a t} h' u b_u du` almost surely at each time `t` is a Brownian
motion: it is the Wiener integral `∫₀^{a t} h db` along the time change `a`. -/
theorem isBrownianReal_of_ae_eq_mul_sub_integral (hb : IsBrownianReal b P) {a : ℝ≥0 → ℝ≥0}
    {h h' : ℝ → ℝ} (hh : ContinuousOn h (Ici 0)) (hderiv : ∀ x, 0 < x → HasDerivAt h (h' x) x)
    (hint : ∀ t, IntervalIntegrable h' volume 0 (a t))
    (hnorm : ∀ t, ∫ r in (0 : ℝ)..a t, h r ^ 2 = t) {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, X t =ᵐ[P] fun ω ↦ h (a t) * b (a t) ω - ∫ u in (0 : ℝ)..a t, h' u * b u.toNNReal ω)
    (hXc : ∀ᵐ ω ∂P, Continuous (X · ω)) : IsBrownianReal X P := by
  have hb' := hb.toIsPreBrownianReal
  have hk : Continuous fun s : ℝ≥0 ↦ h s :=
    hh.comp_continuous NNReal.continuous_coe fun s ↦ s.coe_nonneg
  refine ⟨hb'.isPreBrownianReal_of_ae_eq_wienerIntegral
    (f := fun t ↦ (hk.memLp_timeMeasure 2 (a t)).toLp _) (fun t ↦ MemLp.coeFn_toLp _)
    (fun t ↦ ?_) (fun t ↦ ?_), hXc⟩
  · rw [integral_timeMeasure, ← hnorm t]
    refine intervalIntegral.integral_congr fun r hr ↦ ?_
    rw [uIcc_of_le (a t).coe_nonneg] at hr
    simp only [Real.coe_toNNReal r hr.1]
  · exact (hX t).trans (hb'.wienerIntegral_ae_eq_mul_sub_integral (hh.mono Icc_subset_Ici_self)
      (fun x hx ↦ hderiv x hx.1) (hint t) (MemLp.coeFn_toLp _)
      (hb.aestronglyMeasurable_uncurry_toNNReal _)).symm

end ProbabilityTheory.IsBrownianReal
