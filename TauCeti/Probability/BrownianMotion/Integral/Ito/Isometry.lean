/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Deterministic
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.Process
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import TauCeti.Probability.BrownianMotion.Integral.Energy.Basic
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Martingale.LpLimit

/-!
# Existence of the Itô integral for square-integrable integrands and the Itô isometry

For a pre-Brownian motion `W` relative to a filtration and a predictable integrand `H` with
finite expected square energy on every finite horizon (`TauCeti.BrownianIntegrable`), this file
constructs the Itô integral of `H` against `W`, identifies `IsItoIntegral` with the completed
`L²` integral and with the deterministic Wiener integral, and proves the Itô isometries and
martingale properties.

* `TauCeti.BrownianIntegrable.exists_isItoIntegral`: when `W` has almost surely continuous paths,
  `H` has an Itô integral which is a predictable martingale.
* `TauCeti.Probability.IsFilteredPreBrownianReal.isItoIntegral_of_ae_eq_l2Integral` and
  `TauCeti.Probability.IsFilteredPreBrownianReal.itoIntegral_ae_eq_l2Integral`: two-way
  comparison between `IsItoIntegral` and modifications of `hW.l2Integral t (hH.toPredictableLp t)`.
* `TauCeti.Probability.IsItoIntegral.ae_eq_wienerIntegral`: an Itô integral of a deterministic
  integrand agrees almost surely at each finite horizon with its Wiener integral.
* `TauCeti.Probability.IsItoIntegral.martingale` and
  `TauCeti.Probability.IsItoIntegral.martingale_sq_sub_integral`: every adapted Itô integral of
  `H` is a martingale, with square-compensation martingale `I_t² - ∫_(0,t] H_s² ds`.
* `TauCeti.Probability.IsItoIntegral.memLp`, `TauCeti.Probability.IsItoIntegral.eLpNorm_eq`,
  `TauCeti.Probability.IsItoIntegral.integral_sq`, and
  `TauCeti.Probability.IsFilteredPreBrownianReal.itoIntegral_mul_isometry`: every Itô integral `I`
  of `H` is square integrable at each time `t`, with `E[I_t²] = E ∫_(0,t] H_s² ds` and the
  polarized cross-isometry `E[I_T J_T] = E ∫_(0,T] H_s K_s ds`.

The integral is the limit of the elementary integrals of bounded simple holdings approximating
`H` in `L²` of Lebesgue time times `P` on every finite horizon. By the elementary isometry
`TauCeti.Probability.IsFilteredPreBrownianReal.eLpNorm_simpleGains`, these elementary integrals
are Cauchy in `L²(P)` at every time. Their fixed-time limit is a martingale, and, when `W` has
continuous paths, the continuous martingale completion
`MeasureTheory.exists_continuous_martingale_of_cauchySeq_Lp` selects a predictable version with
almost surely continuous paths. Any Itô integral agrees almost surely at each time with this
fixed-time limit, by `TauCeti.Probability.IsItoIntegral.ae_eq_of_tendstoInMeasure`, which gives
the martingale property, square compensation, Wiener-integral comparison, and the isometry for
every Itô integral.

Neither usual conditions on the filtration nor path continuity of `W` are needed for the
isometry, Wiener comparison, and martingale properties; only existence uses continuous paths.
Adaptedness is needed for the martingale properties because an Itô integral is determined only up
to indistinguishability, and an arbitrary indistinguishable version need not be adapted to a raw
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

/-- The elementary isometry for the difference of two simple holdings with bounded heights:
the `L²(P)` distance of their elementary integrals at `t` is the `L²` distance of the holdings
for Lebesgue time on `(0,t]` times `P`. -/
private theorem eLpNorm_simpleGains_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ σ : ℕ → ℝ≥0} {n m : ℕ} {a b : ℕ → Ω → ℝ} {C D : ℝ}
    (hτ : MonotoneOn τ (Iic n)) (hσ : MonotoneOn σ (Iic m))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j < m, StronglyMeasurable[ℱ (σ j)] (b j))
    (haC : ∀ j < n, ∀ ω, ‖a j ω‖ ≤ C) (hbD : ∀ j < m, ∀ ω, ‖b j ω‖ ≤ D) (t : ℝ≥0) :
    eLpNorm (Finance.simpleGains τ n a W t - Finance.simpleGains σ m b W t) 2 P =
      eLpNorm (Function.uncurry (Finance.simpleHolding τ n a) -
        Function.uncurry (Finance.simpleHolding σ m b)) 2 ((timeMeasure t).prod P) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨N, ρ, c, -, hρ, hc, hhold, hgain⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sub ℱ hτ hσ ha hb
  -- Each height on the common grid is a value of the difference of the two holdings.
  have hc₂ (j : ℕ) (hj : j < N) : MemLp (c j) 2 P := by
    refine MemLp.of_bound ((hc j hj).mono (ℱ.le _)).aestronglyMeasurable (max C 0 + max D 0)
      (ae_of_all _ fun ω ↦ ?_)
    have hmem : ρ (j + 1) ∈ Ioc (ρ j) (ρ (j + 1)) :=
      ⟨hρ (mem_Iic.mpr hj.le) (mem_Iic.mpr hj) (Nat.lt_succ_self j), le_rfl⟩
    rw [← Finance.simpleHolding_of_mem_Ioc (a := c) hρ.monotoneOn hj hmem ω, hhold]
    exact (norm_sub_le _ _).trans
      (add_le_add (Finance.norm_simpleHolding_le hτ _ ω fun j hj ↦ haC j hj ω)
        (Finance.norm_simpleHolding_le hσ _ ω fun j hj ↦ hbD j hj ω))
  have hG : Finance.simpleGains τ n a W t - Finance.simpleGains σ m b W t =
      Finance.simpleGains ρ N c W t := funext fun ω ↦ (hgain W t ω).symm
  have hK : Function.uncurry (Finance.simpleHolding τ n a) -
      Function.uncurry (Finance.simpleHolding σ m b) =
        Function.uncurry (Finance.simpleHolding ρ N c) := funext fun p ↦ (hhold p.1 p.2).symm
  rw [hG, hK]
  exact hW.eLpNorm_simpleGains hρ.monotoneOn hc hc₂ t

/-- Bounded simple holdings approximating a Brownian-integrable integrand on every finite
horizon have elementary martingales which are Cauchy in `L²(P)` at every time, with `L²(P)`
norms equal to the `L²` norms of their holdings. -/
private theorem _root_.TauCeti.BrownianIntegrable.exists_simpleGains_cauchySeq
    (hH : BrownianIntegrable ℱ P H) (hW : IsFilteredPreBrownianReal ℱ W P) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ)
      (hmem : ∀ k t, MemLp (Finance.simpleGains (τ k) (n k) (a k) W t) 2 P),
      (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k, Martingale (Finance.simpleGains (τ k) (n k) (a k) W) ℱ P) ∧
      (∀ t, CauchySeq fun k ↦ (hmem k t).toLp (Finance.simpleGains (τ k) (n k) (a k) W t)) ∧
      (∀ t, Tendsto (fun k ↦ eLpNorm (Function.uncurry (Finance.simpleHolding (τ k) (n k) (a k))
        - Function.uncurry H) 2 ((timeMeasure t).prod P)) atTop (𝓝 0)) ∧
      ∀ k t, eLpNorm (Finance.simpleGains (τ k) (n k) (a k) W t) 2 P =
        eLpNorm (Function.uncurry (Finance.simpleHolding (τ k) (n k) (a k))) 2
          ((timeMeasure t).prod P) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, haC, hKH⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
    MemLp.of_bound ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable (C k)
      (ae_of_all _ (haC k j hj))
  have hmem (k : ℕ) (t : ℝ≥0) : MemLp (Finance.simpleGains (τ k) (n k) (a k) W t) 2 P :=
    hW.memLp_simpleGains (hτ k).monotoneOn (ha k) (ha₂ k) t
  have hK (k : ℕ) (t : ℝ≥0) : MemLp (Function.uncurry (Finance.simpleHolding (τ k) (n k) (a k)))
      2 ((timeMeasure t).prod P) :=
    MemLp.of_bound (((Finance.isStronglyPredictable_simpleHolding (ha k)).mono
        ℱ.predictable_le_prod).aestronglyMeasurable) (max (C k) 0)
      (ae_of_all _ fun p ↦
        Finance.norm_simpleHolding_le (hτ k).monotoneOn p.1 p.2 fun j hj ↦ haC k j hj p.2)
  refine ⟨n, τ, a, hmem, fun k ↦ (hτ k).monotoneOn, ha, fun k ↦ ?_, fun t ↦ ?_, hKH,
    fun k t ↦ hW.eLpNorm_simpleGains (hτ k).monotoneOn (ha k) (ha₂ k) t⟩
  · exact hW.martingale.simpleGains_of_bdd (hτ k).monotoneOn (ha k)
      fun j hj ↦ ⟨C k, ae_of_all _ fun ω ↦ by simpa using haC k j hj ω⟩
  · -- The elementary integrals at `t` are exactly as far apart as their holdings.
    have hH₂ := hH.memLp_timeMeasure t
    have hconv : Tendsto (fun k ↦ (hK k t).toLp _) atTop (𝓝 (hH₂.toLp _)) :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun k ↦ hK k t) _ hH₂).2 (hKH t)
    have hdist (k l : ℕ) : dist ((hmem k t).toLp _) ((hmem l t).toLp _) =
        dist ((hK k t).toLp _) ((hK l t).toLp _) := by
      rw [dist_eq_norm, dist_eq_norm, ← MemLp.toLp_sub, ← MemLp.toLp_sub, Lp.norm_toLp,
        Lp.norm_toLp, eLpNorm_simpleGains_sub hW (hτ k).monotoneOn (hτ l).monotoneOn (ha k)
          (ha l) (haC k) (haC l) t]
    have hcau := hconv.cauchySeq
    rw [Metric.cauchySeq_iff] at hcau ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcau ε hε
    exact ⟨N, fun k hk l hl ↦ hdist k l ▸ hN k hk l hl⟩

/-- The pathwise square energies of the approximating holdings of
`TauCeti.BrownianIntegrable.exists_simpleGains_cauchySeq` converge in probability. -/
private theorem tendsto_measure_le_lintegral_simpleHolding_sub [SFinite P]
    (hH : IsStronglyPredictable ℱ H) {n : ℕ → ℕ} {τ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (ha : ∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) {t : ℝ≥0}
    (hKH : Tendsto (fun k ↦ eLpNorm (Function.uncurry (Finance.simpleHolding (τ k) (n k) (a k))
        - Function.uncurry H) 2 ((timeMeasure t).prod P)) atTop (𝓝 0))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s,
      ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t})
        atTop (𝓝 0) :=
  MeasureTheory.tendsto_measure_le_lintegral_enorm_pow_of_tendsto_eLpNorm (n := 2) two_ne_zero
    (fun k ↦ (((Finance.isStronglyPredictable_simpleHolding (ha k)).sub hH).mono
      ℱ.predictable_le_prod).aestronglyMeasurable) (by simpa only [Nat.cast_ofNat] using hKH) hε

/-- **Existence of the Itô integral for square-integrable integrands.** Against a pre-Brownian
motion relative to the filtration with almost surely continuous paths, every predictable
integrand with finite expected square energy on every finite horizon has an Itô integral which
is a predictable martingale. No usual conditions on the filtration are assumed. -/
theorem _root_.TauCeti.BrownianIntegrable.exists_isItoIntegral (hH : BrownianIntegrable ℱ P H)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω) :
    ∃ I, IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧ Martingale I ℱ P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, hmem, hτ, ha, hmart, hcau, hKH, -⟩ := hH.exists_simpleGains_cauchySeq hW
  obtain ⟨I, hI, hIp, hIlim, -, _, -, hIc⟩ := exists_continuous_martingale_of_cauchySeq_Lp hmart
    (fun k ↦ hWc.mono fun ω hω ↦ Finance.continuous_simpleGains hω) hmem hcau
  refine ⟨I, ⟨hH.isStronglyPredictable, hIc.mono fun ω hω ↦ hω.1, fun t ↦ ⟨n, τ, a, hτ, ha,
    tendsto_measure_le_lintegral_simpleHolding_sub hH.isStronglyPredictable ha (hKH t), ?_⟩⟩,
    hIp, hI⟩
  exact tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (hIlim t).2

/-- Every Itô integral of a Brownian-integrable integrand agrees almost surely at each time with
a martingale whose `L²(P)` norm at time `t` is the `L²` norm of the integrand for Lebesgue time
on `(0,t]` times `P`. -/
private theorem IsItoIntegral.exists_martingale_ae_eq (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) :
    ∃ Z : ℝ≥0 → Ω → ℝ, Martingale Z ℱ P ∧ ∀ t, I t =ᵐ[P] Z t ∧ MemLp (Z t) 2 P ∧
      eLpNorm (Z t) 2 P = eLpNorm (Function.uncurry H) 2 ((timeMeasure t).prod P) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, hmem, hτ, ha, hmart, hcau, hKH, hiso⟩ := hH.exists_simpleGains_cauchySeq hW
  obtain ⟨Z, hZ, hZlim⟩ := exists_martingale_of_cauchySeq_Lp hmart hmem hcau
  refine ⟨Z, hZ, fun t ↦ ⟨?_, (hZlim t).1, ?_⟩⟩
  · exact hI.ae_eq_of_tendstoInMeasure hW hτ ha
      (tendsto_measure_le_lintegral_simpleHolding_sub hH.isStronglyPredictable ha (hKH t))
      (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (hZlim t).2)
  · -- Pass to the limit in the elementary isometry, in both `L²` spaces.
    have hH₂ := hH.memLp_timeMeasure t
    have hK (k : ℕ) : MemLp (Function.uncurry (Finance.simpleHolding (τ k) (n k) (a k))) 2
        ((timeMeasure t).prod P) := by
      rw [memLp_iff, ← hiso k t]
      exact (hmem k t).eLpNorm_lt_top
    have hKlim := ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hK _ hH₂).2 (hKH t)).norm
    have hGlim := ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun k ↦ hmem k t) _ (hZlim t).1).2
      (hZlim t).2).norm
    simp only [Lp.norm_toLp, hiso] at hKlim hGlim
    exact (ENNReal.toReal_eq_toReal_iff' (hZlim t).1.eLpNorm_ne_top hH₂.eLpNorm_ne_top).1
      (tendsto_nhds_unique hGlim hKlim)

/-- **The martingale property of the Itô integral.** Against a pre-Brownian motion relative to
the filtration, an adapted Itô integral of a Brownian-integrable integrand is a martingale.
Neither path continuity of the integrator nor usual conditions on the filtration are needed. -/
theorem IsItoIntegral.martingale (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hIa : StronglyAdapted ℱ I) : Martingale I ℱ P := by
  obtain ⟨Z, hZ, hIZ⟩ := hI.exists_martingale_ae_eq hW hH
  exact hZ.congr hIa fun t ↦ (hIZ t).1.symm

/-- An Itô integral of a Brownian-integrable integrand against a pre-Brownian motion relative to
the filtration is square integrable at every time. -/
theorem IsItoIntegral.memLp (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    MemLp (I t) 2 P := by
  obtain ⟨Z, -, hIZ⟩ := hI.exists_martingale_ae_eq hW hH
  exact (hIZ t).2.1.ae_eq (hIZ t).1.symm

/-- **The Itô isometry**, in `L²` norms. Against a pre-Brownian motion relative to the
filtration, the `L²(P)` norm at time `t` of an Itô integral of a Brownian-integrable integrand is
the `L²` norm of the integrand for Lebesgue time on `(0,t]` times `P`. -/
theorem IsItoIntegral.eLpNorm_eq (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    eLpNorm (I t) 2 P = eLpNorm (Function.uncurry H) 2 ((timeMeasure t).prod P) := by
  obtain ⟨Z, -, hIZ⟩ := hI.exists_martingale_ae_eq hW hH
  rw [eLpNorm_congr_ae (hIZ t).1, (hIZ t).2.2]

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

namespace IsFilteredPreBrownianReal

variable {K J : ℝ≥0 → Ω → ℝ}

/-- Any almost surely continuous modification of `t ↦ hW.l2Integral t (hH.toPredictableLp t)`
satisfies the elementary-approximation specification `IsItoIntegral`. -/
theorem isItoIntegral_of_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hI_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω))
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) :
    IsItoIntegral ℱ P W H I where
  isStronglyPredictable := hH.isStronglyPredictable
  ae_continuous := hI_cont
  exists_approx t := by
    let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    obtain ⟨n, τ, a, C, _, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
    have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
      MemLp.of_bound ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable (C k)
        (Eventually.of_forall (hb k j hj))
    refine ⟨n, τ, a, fun k ↦ (hτ k).monotoneOn, ha, fun _ hε ↦
      MeasureTheory.tendsto_measure_le_lintegral_enorm_pow_of_tendsto_eLpNorm (n := 2) two_ne_zero
        (g := fun k p ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2)
        (fun k ↦ (((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
          hH.isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
        (by simpa only [Nat.cast_ofNat] using herr t) hε,
      tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_⟩
    exact hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
      (fun _ ↦ hH) (fun _ ↦ hI t) (fun k ↦ (hτ k).monotoneOn) ha ha₂ (herr t)

/-- When `H` has finite expected square energy on every finite horizon (`BrownianIntegrable`), any
process `I` satisfying `IsItoIntegral ℱ P W H I` agrees almost everywhere at each time `t` with
`hW.l2Integral t (hH.toPredictableLp t)`. Neither path continuity of `W` nor usual conditions on
the filtration are needed. -/
theorem itoIntegral_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨m, σ, b, C, _, hσ, hb, hbd, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have hbd₂ (k j : ℕ) (hj : j < m k) : MemLp (b k j) 2 P :=
    MemLp.of_bound ((hb k j hj).mono (ℱ.le _)).aestronglyMeasurable (C k)
      (Eventually.of_forall (hbd k j hj))
  refine hI.ae_eq_of_tendstoInMeasure hW (fun k ↦ (hσ k).monotoneOn) hb (fun _ hε ↦ ?_) ?_
  · exact MeasureTheory.tendsto_measure_le_lintegral_enorm_pow_of_tendsto_eLpNorm (n := 2)
      two_ne_zero (g := fun k p ↦ Finance.simpleHolding (σ k) (m k) (b k) p.1 p.2 - H p.1 p.2)
      (fun k ↦ (((Finance.isStronglyPredictable_simpleHolding (hb k)).sub
        hH.isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
      (by simpa only [Nat.cast_ofNat] using herr t) hε
  · refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
    simpa only [Pi.sub_def] using
      hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
        (fun _ ↦ hH) (fun _ ↦ .rfl) (fun k ↦ (hσ k).monotoneOn) hb hbd₂ (herr t)

/-- **Cross-isometry of the Brownian Itô integral** on `BrownianIntegrable` integrands. -/
theorem itoIntegral_mul_isometry
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) (T : ℝ≥0) :
    ∫ ω, I T ω * J T ω ∂P = ∫ p, H p.1 p.2 * K p.1 p.2 ∂(timeMeasure T).prod P :=
  hW.integral_mul_of_ae_eq_l2Integral hH hK
    (hW.itoIntegral_ae_eq_l2Integral hH hI)
    (hW.itoIntegral_ae_eq_l2Integral hK hJ) T

end IsFilteredPreBrownianReal

/-- **Square-compensation martingale of the Itô integral.** Against a pre-Brownian motion
relative to the filtration, an adapted Itô integral `I` of a Brownian-integrable integrand `H`
makes `I_t² - ∫_{(0, t]} H_s² ds` a true martingale on the original raw filtration. Neither path
continuity of `W` nor usual conditions on the filtration are needed. -/
theorem IsItoIntegral.martingale_sq_sub_integral (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hIa : StronglyAdapted ℱ I) :
    Martingale (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) ℱ P :=
  hW.martingale_sq_sub_integral_of_ae_eq_l2Integral hH hIa
    (hW.itoIntegral_ae_eq_l2Integral hH hI)

/-- **Deterministic-integrand comparison with the Wiener integral.** An Itô integral of a
deterministic integrand against a pre-Brownian motion relative to the filtration agrees almost
surely at each finite horizon with its Wiener integral. -/
theorem IsItoIntegral.ae_eq_wienerIntegral {f : ℝ≥0 → ℝ}
    (hI : IsItoIntegral ℱ P W (fun t _ ↦ f t) I)
    (hW : IsFilteredPreBrownianReal ℱ W P) {T : ℝ≥0} (hf : MemLp f 2 (timeMeasure T)) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    I T =ᵐ[P] hW.toIsPreBrownianReal.wienerIntegral T (hf.toLp f) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨_, hω⟩ := hI.locallyBrownianIntegrable.ae_memLp.exists
  have hH : BrownianIntegrable ℱ P (fun t _ ↦ f t) :=
    ⟨hI.isStronglyPredictable, fun t ↦ (hω t).comp_fst P⟩
  exact hW.ae_eq_wienerIntegral_of_ae_eq_l2Integral hf hH (hW.itoIntegral_ae_eq_l2Integral hH hI)

end TauCeti.Probability
