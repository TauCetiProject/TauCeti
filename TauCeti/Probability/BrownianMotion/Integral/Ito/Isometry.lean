/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Probability.BrownianMotion.Integral.Simple
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Martingale.LpLimit
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim

/-!
# Existence of the Itô integral for square-integrable integrands and the Itô isometry

For a pre-Brownian motion `W` relative to a filtration and a predictable integrand `H` with
finite expected square energy on every finite horizon (`TauCeti.BrownianIntegrable`), this file
constructs the Itô integral of `H` against `W`, identifies it with the terminal `L²` integral
`TauCeti.Probability.IsFilteredPreBrownianReal.l2Integral`, and proves the Itô isometry.

* `TauCeti.Probability.IsFilteredPreBrownianReal.eLpNorm_l2Integral_sub`: the `L²(P)` distance
  between two terminal `L²` integrals equals the `L²` distance between their predictable
  integrands on `(0, t] × Ω`.
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
`H` in `L²` of Lebesgue time times `P` on every finite horizon. By `coeFn_l2Integral_simpleHolding`
and the terminal linear isometry `hW.l2Integral`, these elementary integrals converge in `L²(P)` at
every time to `hW.l2Integral t`. Their Cauchy property feeds
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

/-- The `L²(P)` distance between two terminal `L²` Brownian integrals equals the `L²` distance
between their predictable integrands for Lebesgue time on `(0, T]` times `P`. -/
theorem IsFilteredPreBrownianReal.eLpNorm_l2Integral_sub
    (hW : IsFilteredPreBrownianReal ℱ W P) (T : ℝ≥0) {H₁ H₂ : ℝ≥0 × Ω → ℝ}
    (hH₁p : StronglyMeasurable[ℱ.predictable] H₁)
    (hH₂p : StronglyMeasurable[ℱ.predictable] H₂)
    (hH₁m : MemLp H₁ 2 (ℱ.predictableMeasure P T))
    (hH₂m : MemLp H₂ 2 (ℱ.predictableMeasure P T)) :
    eLpNorm (fun ω ↦ hW.l2Integral T (hH₁m.toLp H₁) ω - hW.l2Integral T (hH₂m.toLp H₂) ω) 2 P =
      eLpNorm (H₁ - H₂) 2 ((timeMeasure T).prod P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  calc eLpNorm (fun ω ↦ hW.l2Integral T (hH₁m.toLp H₁) ω - hW.l2Integral T (hH₂m.toLp H₂) ω) 2 P
      = edist (hW.l2Integral T (hH₁m.toLp H₁)) (hW.l2Integral T (hH₂m.toLp H₂)) := by
        rw [Lp.edist_def]; rfl
    _ = eLpNorm (⇑(hH₁m.toLp H₁) - ⇑(hH₂m.toLp H₂)) 2 (ℱ.predictableMeasure P T) := by
        rw [(hW.l2Integral T).isometry.edist_eq, Lp.edist_def]
    _ = eLpNorm (H₁ - H₂) 2 (ℱ.predictableMeasure P T) :=
        eLpNorm_congr_ae (hH₁m.coeFn_toLp.sub hH₂m.coeFn_toLp)
    _ = eLpNorm (H₁ - H₂) 2 ((timeMeasure T).prod P) := by
        rw [ℱ.predictableMeasure_def]
        exact eLpNorm_trim ℱ.predictable_le_prod (hH₁p.sub hH₂p)

/-- Bounded simple holdings approximating a Brownian-integrable integrand on every finite horizon
in `L²` also approximate it in square energy in probability, produce true elementary martingales,
and have elementary gains converging in `L²(P)` at every horizon to the terminal `L²` integral
`hW.l2Integral T`. -/
theorem IsFilteredPreBrownianReal.exists_simpleHolding_approx
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ)
      (hmem : ∀ k t, MemLp (Finance.simpleGains (τ k) (n k) (a k) W t) 2 P),
      (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      (∀ k j, j < n k → MemLp (a k j) 2 P) ∧
      (∀ k, Martingale (Finance.simpleGains (τ k) (n k) (a k) W) ℱ P) ∧
      (∀ T, Tendsto (fun k ↦ eLpNorm (Function.uncurry (Finance.simpleHolding (τ k) (n k) (a k)) -
        Function.uncurry H) 2 ((timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      (∀ T ε, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
        ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure T})
          atTop (𝓝 0)) ∧
      (∀ T, Tendsto (fun k ↦ (hmem k T).toLp (Finance.simpleGains (τ k) (n k) (a k) W T)) atTop
        (𝓝 (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))))) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, haC, hlim⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
    MemLp.of_bound ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable (C k)
      (ae_of_all _ (haC k j hj))
  have hKm (k : ℕ) (T : ℝ≥0) : MemLp (Function.uncurry (Finance.simpleHolding (τ k) (n k) (a k)))
      2 (ℱ.predictableMeasure P T) :=
    Finance.memLp_simpleHolding_predictableMeasure (ha k) (ha₂ k) T
  have hgain (k : ℕ) (T : ℝ≥0) :
      hW.l2Integral T ((hKm k T).toLp _) =ᵐ[P] Finance.simpleGains (τ k) (n k) (a k) W T :=
    hW.coeFn_l2Integral_simpleHolding (hτ k).monotoneOn (ha k) T (hKm k T)
  have hmem (k : ℕ) (T : ℝ≥0) : MemLp (Finance.simpleGains (τ k) (n k) (a k) W T) 2 P :=
    (Lp.memLp _).ae_eq (hgain k T)
  refine ⟨n, τ, a, C, hmem, fun k ↦ (hτ k).monotoneOn, ha, haC, ha₂,
    fun k ↦ hW.martingale.simpleGains_of_bdd (hτ k).monotoneOn (ha k)
      fun j hj ↦ ⟨C k, ae_of_all _ fun ω ↦ by simpa using haC k j hj ω⟩,
    hlim,
    fun T ε hε ↦ tendsto_measure_le_lintegral_enorm_sq_of_tendsto_eLpNorm
      (fun k ↦ (((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
        hH.isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
      (hlim T) hε,
    fun T ↦ (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).2 <| (hlim T).congr fun k ↦ by
      have hsub := hW.eLpNorm_l2Integral_sub T (Finance.isStronglyPredictable_simpleHolding (ha k))
        hH.isStronglyPredictable (hKm k T) (hH.memLp_predictableMeasure T)
      exact hsub.symm.trans (eLpNorm_congr_ae
        (((hgain k T).trans (hmem k T).coeFn_toLp.symm).sub EventuallyEq.rfl))⟩

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

/-- Bounded simple holdings approximating a Brownian-integrable integrand on every finite horizon
in `L²` have elementary integrals converging in `L²(P)` to a martingale that agrees almost surely
at every time with the terminal `L²` integral `hW.l2Integral t`. -/
theorem IsFilteredPreBrownianReal.exists_simpleHolding_martingale_approx
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (Z : ℝ≥0 → Ω → ℝ),
      (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → MemLp (a k j) 2 P) ∧
      (∀ T, Tendsto (fun k ↦ eLpNorm (Function.uncurry (Finance.simpleHolding (τ k) (n k) (a k)) -
        Function.uncurry H) 2 ((timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      Martingale Z ℱ P ∧
      (∀ t, MemLp (Z t) 2 P) ∧
      (∀ t, Tendsto (fun k ↦ eLpNorm (Finance.simpleGains (τ k) (n k) (a k) W t - Z t) 2 P)
        atTop (𝓝 0)) ∧
      (∀ t, Z t =ᵐ[P]
        hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, -, hmem, hτ, ha, -, ha₂, hmart, hlim, -, hLp⟩ :=
    hW.exists_simpleHolding_approx hH
  obtain ⟨Z, hZ, hZlim⟩ :=
    exists_martingale_of_cauchySeq_Lp hmart hmem fun t ↦ (hLp t).cauchySeq
  refine ⟨n, τ, a, Z, hτ, ha, ha₂, hlim, hZ, fun t ↦ (hZlim t).1, fun t ↦ (hZlim t).2,
    fun t ↦ tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (hZlim t).2)
      ((tendstoInMeasure_of_tendsto_Lp (hLp t)).congr_left fun k ↦ (hmem k t).coeFn_toLp)⟩

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
