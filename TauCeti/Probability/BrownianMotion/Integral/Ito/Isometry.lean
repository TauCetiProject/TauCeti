/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Probability.BrownianMotion.Integral.Simple
import TauCeti.Probability.Martingale.ContinuousLimit

/-!
# Existence of the Itô integral for square-integrable integrands and the Itô isometry

For a pre-Brownian motion `W` relative to a filtration and a predictable integrand `H` with
finite expected square energy on every finite horizon (`TauCeti.BrownianIntegrable`), this file
constructs the Itô integral of `H` against `W`, identifies it with the terminal `L²` integral
`TauCeti.Probability.IsFilteredPreBrownianReal.l2Integral`, and proves the Itô isometry.

* `TauCeti.Probability.IsFilteredPreBrownianReal.ae_eq_l2Integral_of_isItoIntegral`: any Itô
  integral of `H` agrees almost surely at each finite horizon `T` with `hW.l2Integral T`.
* `TauCeti.BrownianIntegrable.exists_isItoIntegral`: when `W` has almost surely continuous paths,
  `H` has an Itô integral which is a predictable martingale.
* `TauCeti.Probability.IsItoIntegral.martingale`: every adapted Itô integral of `H` is a
  martingale.
* `TauCeti.Probability.IsItoIntegral.memLp`, `TauCeti.Probability.IsItoIntegral.eLpNorm_eq` and
  `TauCeti.Probability.IsItoIntegral.integral_sq`: every Itô integral `I` of `H` is square
  integrable at each time `t`, with `E[I_t²] = E ∫_(0,t] H_s² ds`.

The integral is the limit of the elementary integrals of bounded simple holdings approximating
`H` in `L²` of Lebesgue time times `P` on every finite horizon, supplied by
`TauCeti.Probability.IsFilteredPreBrownianReal.exists_simpleHolding_approx` and
`exists_simpleHolding_martingale_approx`. Their Cauchy property feeds
`MeasureTheory.exists_continuous_martingale_of_cauchySeq_Lp` to select a predictable version with
almost surely continuous paths when `W` is continuous, while
`TauCeti.Probability.IsItoIntegral.ae_eq_of_tendstoInMeasure` identifies every Itô integral with
`hW.l2Integral t`, giving the martingale property and the isometry without repeating the norm
computation.

Neither usual conditions on the filtration nor path continuity of `W` are needed for the
isometry and the martingale property; only existence uses continuous paths. Adaptedness is
needed for the martingale property because an Itô integral is determined only up to
indistinguishability, and an arbitrary indistinguishable version need not be adapted to a raw
filtration.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B (Proposition 3.2.10) and §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W H I : ℝ≥0 → Ω → ℝ}

/-- **Agreement with the terminal L² integral.** For a Brownian-integrable integrand, any Itô
integral agrees almost surely at each finite horizon `T` with `hW.l2Integral T`. Path continuity
of `W` is not required. -/
theorem IsFilteredPreBrownianReal.ae_eq_l2Integral_of_isItoIntegral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    I T =ᵐ[P] hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) := by
  obtain ⟨n, τ, a, -, hmem, hτ, ha, -, -, -, -, hE, hLp⟩ := hW.exists_simpleHolding_approx hH
  exact hI.ae_eq_of_tendstoInMeasure hW hτ ha (hE T)
    ((tendstoInMeasure_of_tendsto_Lp (hLp T)).congr_left fun k ↦ (hmem k T).coeFn_toLp)

/-- **Existence of the Itô integral for square-integrable integrands.** Against a pre-Brownian
motion relative to the filtration with almost surely continuous paths, every predictable
integrand with finite expected square energy on every finite horizon has an Itô integral which
is a predictable martingale. No usual conditions on the filtration are assumed. -/
theorem _root_.TauCeti.BrownianIntegrable.exists_isItoIntegral (hH : BrownianIntegrable ℱ P H)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω) :
    ∃ I, IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧ Martingale I ℱ P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, -, hmem, hτ, ha, -, -, hmart, -, hE, hLp⟩ := hW.exists_simpleHolding_approx hH
  obtain ⟨I, hI, hIp, hIlim, -, _, -, hIc⟩ := exists_continuous_martingale_of_cauchySeq_Lp hmart
    (fun k ↦ hWc.mono fun ω hω ↦ Finance.continuous_simpleGains hω) hmem
    fun t ↦ (hLp t).cauchySeq
  refine ⟨I, ⟨hH.isStronglyPredictable, hIc.mono fun ω hω ↦ hω.1,
    fun t ↦ ⟨n, τ, a, hτ, ha, hE t, tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (hIlim t).2⟩⟩,
    hIp, hI⟩



/-- **The martingale property of the Itô integral.** Against a pre-Brownian motion relative to
the filtration, an adapted Itô integral of a Brownian-integrable integrand is a martingale.
Neither path continuity of the integrator nor usual conditions on the filtration are needed. -/
theorem IsItoIntegral.martingale (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hIa : StronglyAdapted ℱ I) : Martingale I ℱ P := by
  obtain ⟨-, -, -, Z, -, -, -, -, hZ, -, -, hZL⟩ := hW.exists_simpleHolding_martingale_approx hH
  exact hZ.congr hIa fun t ↦ (hZL t).trans (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).symm

/-- An Itô integral of a Brownian-integrable integrand against a pre-Brownian motion relative to
the filtration is square integrable at every time. -/
theorem IsItoIntegral.memLp (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    MemLp (I t) 2 P :=
  (Lp.memLp _).ae_eq (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).symm

/-- **The Itô isometry**, in `L²` norms. Against a pre-Brownian motion relative to the
filtration, the `L²(P)` norm at time `t` of an Itô integral of a Brownian-integrable integrand is
the `L²` norm of the integrand for Lebesgue time on `(0,t]` times `P`. -/
theorem IsItoIntegral.eLpNorm_eq (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    eLpNorm (I t) 2 P = eLpNorm (Function.uncurry H) 2 ((timeMeasure t).prod P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  rw [eLpNorm_congr_ae (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t)]
  have hsub := hW.eLpNorm_l2Integral_sub t hH.isStronglyPredictable stronglyMeasurable_zero
    (hH.memLp_predictableMeasure t) MemLp.zero
  rw [MemLp.toLp_zero, map_zero] at hsub
  have hae : (fun ω ↦ hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp
      (Function.uncurry H)) ω - (0 : Lp ℝ 2 P) ω) =ᵐ[P]
      hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) :=
    (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := P)).mono fun ω hω ↦ by
      dsimp only; rw [hω, Pi.zero_apply, sub_zero]
  rw [← eLpNorm_congr_ae hae, hsub]
  simp only [sub_zero]

/-- **The Itô isometry.** Against a pre-Brownian motion relative to the filtration, an Itô
integral `I` of a Brownian-integrable integrand `H` satisfies `E[I_t²] = E ∫_(0,t] H_s² ds`. -/
theorem IsItoIntegral.integral_sq (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  have hH₂ : AEStronglyMeasurable (Function.uncurry H) ((timeMeasure t).prod P) :=
    (hH.isStronglyPredictable.mono ℱ.predictable_le_prod).aestronglyMeasurable
  have h := congrArg (fun x ↦ x.toReal ^ 2) (hI.eLpNorm_eq hW hH t)
  simp only [← integral_norm_sq_eq_toReal_eLpNorm_sq (hI.memLp hW hH t).aestronglyMeasurable,
    ← integral_norm_sq_eq_toReal_eLpNorm_sq hH₂, Real.norm_eq_abs, sq_abs] at h
  exact h

end TauCeti.Probability
