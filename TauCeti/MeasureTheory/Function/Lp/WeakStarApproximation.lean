/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.Analysis.Convolution.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.MeasureTheory.Function.Holder

/-!
# Weak-star convergence of bounded mollifications

Normalized smooth mollifiers converge on essentially bounded functions when paired with any
integrable scalar function. This is the endpoint substitute for norm convergence in `L^∞`,
which fails even for a step function. The conclusion holds in norm in a Banach codomain; for
scalar functions it is weak-star convergence under the `L¹`–`L^∞` pairing.

The argument transfers the mollifier to the integrable test function by convolution
associativity and uses strong `L¹` convergence there.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 4.21.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory
open scoped Convolution ENNReal Topology

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {mu : Measure E} [mu.IsAddHaarMeasure]

/-- **Weak-star mollification at the infinite exponent.** Pairing the mollifications of an
`L^∞` function with any `L¹` scalar function converges in the Banach codomain. No countability
assumption on the convergence filter is needed. -/
theorem tendsto_integral_smul_normed_convolution_top {I : Type*} {l : Filter I}
    {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (𝓝 0))
    {a : E → ℝ} (ha : Integrable a mu) {f : E → F} (hf : MemLp f ∞ mu) :
    Tendsto (fun i ↦ ∫ x, a x • ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f) x ∂mu)
      l (𝓝 (∫ x, a x • f x ∂mu)) := by
  -- Reflect the test function so that the dual pairing is convolution evaluated at zero.
  let b : E → ℝ := fun x ↦ a (-x)
  have hb : Integrable b mu := ha.comp_neg
  have hbmem : MemLp b 1 mu := memLp_one_iff_integrable.mpr hb
  have hfn : MemLp (fun x ↦ f (-x)) ∞ mu :=
    hf.comp_measurePreserving (Measure.measurePreserving_neg mu)
  let L : Lp ℝ 1 mu →L[ℝ] F :=
    (lsmul ℝ ℝ).flip.lpPairing mu ∞ 1 (hfn.toLp (fun x ↦ f (-x)))
  have hL (v : Lp ℝ 1 mu) (g : E → ℝ) (hv : v =ᵐ[mu] g) :
      L v = ∫ x, g x • f (-x) ∂mu := by
    dsimp only [L]
    rw [lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hfn.coeFn_toLp, hv] with x hx hx'
    simp only [flip_apply, lsmul_apply, hx, hx']
  have hfbound : ∀ᵐ x ∂mu, ‖f x‖ ≤ ‖hf.toLp f‖ := by
    filter_upwards [hf.coeFn_toLp, Lp.ae_norm_le_norm_top (hf.toLp f)] with x hx hbound
    simpa only [hx] using hbound
  have hlim := L.continuous.tendsto (hbmem.toLp b) |>.comp
    (tendsto_normedBumpLp ENNReal.one_ne_top hphi (hbmem.toLp b))
  have htarget : L (hbmem.toLp b) = ∫ x, a x • f x ∂mu := by
    rw [hL _ _ hbmem.coeFn_toLp]
    exact integral_neg_eq_self (fun x ↦ a x • f x) mu
  have hsource (i : I) : L (normedBumpLp ENNReal.one_ne_top (phi i) mu (hbmem.toLp b)) =
      ∫ x, a x • ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f) x ∂mu := by
    rw [hL _ _ (normedBumpLp_ae_eq_convolution ENNReal.one_ne_top (phi i)
      (memLp_one_iff_integrable.mpr hb))]
    have hassoc := congrFun
      (convolution_lsmul_assoc_of_integrable_of_ae_norm_le hb (phi i).integrable_normed
        hf.aestronglyMeasurable hfbound) 0
    have hcomm : b ⋆[lsmul ℝ ℝ, mu] (phi i).normed mu =
        (phi i).normed mu ⋆[lsmul ℝ ℝ, mu] b :=
      convolution_symm (lsmul ℝ ℝ) (by ext; simp)
    rw [hcomm] at hassoc
    have hpair : (b ⋆[lsmul ℝ ℝ, mu]
        ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f)) 0 =
        ∫ x, a x • ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f) x ∂mu := by
      rw [convolution_lsmul]
      simpa only [zero_sub, b] using integral_neg_eq_self (fun x ↦ a x •
        ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] f) x) mu
    simpa only [convolution_lsmul, zero_sub] using hassoc.trans hpair
  simpa only [Function.comp_def, hsource, htarget] using hlim

end TauCeti
