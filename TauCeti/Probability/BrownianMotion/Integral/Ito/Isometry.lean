/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto
import TauCeti.Probability.BrownianMotion.Integral.Energy.Basic
import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
import TauCeti.Probability.BrownianMotion.Integral.Process
import TauCeti.Probability.BrownianMotion.Integral.Simple
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Martingale.MaximalInequality.Lp

/-!
# Existence of the Itô integral for square-integrable integrands and the Itô isometry

For a pre-Brownian motion `W` relative to a filtration and a predictable integrand `H` with
finite expected square energy on every finite horizon (`TauCeti.BrownianIntegrable`), this file
constructs the Itô integral of `H` against `W`, identifies `IsItoIntegral` with the terminal
`L²` construction `l2Integral`, and proves the Itô isometry.

* `TauCeti.BrownianIntegrable.exists_isItoIntegral`: when `W` has almost surely continuous paths,
  `H` has an Itô integral which is a predictable martingale.
* `TauCeti.Probability.IsItoIntegral.ae_eq_l2Integral`: every Itô integral of an integrand with
  finite expected square energy on `(0, t]` agrees almost surely at `t` with `hW.l2Integral t`.
* `TauCeti.Probability.IsItoIntegral.martingale`: every adapted Itô integral of `H` is a
  martingale.
* `TauCeti.Probability.IsItoIntegral.memLp`, `TauCeti.Probability.IsItoIntegral.eLpNorm_eq` and
  `TauCeti.Probability.IsItoIntegral.integral_sq`: whenever `H` is square integrable on
  `(0, t] × Ω`, every Itô integral `I` of `H` is square integrable at `t`, with
  `E[I_t²] = E ∫_(0,t] H_s² ds`.
* `TauCeti.Probability.IsItoIntegral.tendsto_eLpNorm_iSup_eNorm_simpleGains_sub`: when `W`
  has almost surely continuous paths and `H` is square integrable on `(0, T] × Ω`, elementary
  gains of simple holdings converging to `H` in `L²((timeMeasure T).prod P)` converge uniformly
  on `[0, T]` in `L²(P)` to `I`.

Existence uses bounded simple holdings approximating `H` in `L²` of Lebesgue time times `P` on
every finite horizon and the continuous martingale completion
`MeasureTheory.exists_continuous_martingale_of_cauchySeq_Lp` to select a predictable version with
almost surely continuous paths. The martingale property and fixed-time isometry for every Itô
integral follow directly by identifying `I t` almost surely with `hW.l2Integral t` via
`TauCeti.Probability.IsItoIntegral.ae_eq_l2Integral`, reusing
`TauCeti.Probability.IsFilteredPreBrownianReal.exists_martingale_l2Integral` and the
isometry of `l2Integral`.

Neither usual conditions on the filtration nor path continuity of `W` are needed for the
isometry and the martingale property; only existence and uniform `L²` approximation use
continuous paths. Adaptedness is needed for the martingale property because an Itô integral is
determined only up to indistinguishability, and an arbitrary indistinguishable version need not be
adapted to a raw filtration.

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
    have hH₂ := hH.memLp t
    have hconv : Tendsto (fun k ↦ (hK k t).toLp _) atTop (𝓝 (hH₂.toLp _)) :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun k ↦ hK k t) _ hH₂).2 (hKH t)
    have hdist (k l : ℕ) : dist ((hmem k t).toLp _) ((hmem l t).toLp _) =
        dist ((hK k t).toLp _) ((hK l t).toLp _) := by
      rw [dist_eq_norm, dist_eq_norm, ← MemLp.toLp_sub, ← MemLp.toLp_sub, Lp.norm_toLp,
        Lp.norm_toLp, hW.eLpNorm_simpleGains_sub (hτ k).monotoneOn (hτ l).monotoneOn (ha k)
          (ha l) (ha₂ k) (ha₂ l) t]
    have hcau := hconv.cauchySeq
    rw [Metric.cauchySeq_iff] at hcau ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcau ε hε
    exact ⟨N, fun k hk l hl ↦ hdist k l ▸ hN k hk l hl⟩

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
    fun _ hε ↦ by
      simpa only [Function.uncurry_apply_pair, Pi.sub_apply, Nat.cast_ofNat] using
        TauCeti.tendsto_measure_lintegral_enorm_pow_of_tendsto_eLpNorm two_ne_zero (hKH t) hε,
    ?_⟩⟩, hIp, hI⟩
  exact tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (hIlim t).2

/-- Against a filtered pre-Brownian motion, every Itô integral of an integrand with finite expected
square energy on `(0, t]` agrees almost surely at `t` with `hW.l2Integral t`. -/
theorem IsItoIntegral.ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    I t =ᵐ[P] hW.l2Integral t
      (((ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).2 hH).toLp
        (Function.uncurry H)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  choose n τ a _ _ hτ ha _ herr using fun m : ℕ ↦
    ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P t hI.isStronglyPredictable hH
      (ε := (m : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top m))
  have hhold := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ zero_le) fun m ↦ (herr m).le
  exact tendstoInMeasure_ae_unique
    (hI.tendstoInMeasure_simpleGains hW (fun m ↦ (hτ m).monotoneOn) ha fun _ hε ↦
      TauCeti.tendsto_measure_lintegral_enorm_pow_of_tendsto_eLpNorm two_ne_zero hhold hε)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (hW.tendsto_eLpNorm_simpleGains_l2Integral hI.isStronglyPredictable hH
        (fun m ↦ (hτ m).monotoneOn) ha hhold))

/-- **The martingale property of the Itô integral.** Against a pre-Brownian motion relative to
the filtration, an adapted Itô integral of a Brownian-integrable integrand is a martingale.
Neither path continuity of the integrator nor usual conditions on the filtration are needed. -/
theorem IsItoIntegral.martingale (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hIa : StronglyAdapted ℱ I) : Martingale I ℱ P := by
  obtain ⟨Z, hZ, hZl2, -⟩ := hW.exists_martingale_l2Integral
    fun t ↦ (ℱ.memLp_predictableMeasure_iff P hH.isStronglyPredictable t 2).2 (hH.memLp t)
  exact hZ.congr hIa fun t ↦ (hZl2 t).trans (hI.ae_eq_l2Integral hW (hH.memLp t)).symm

/-- Restricting an integrand in `L²((timeMeasure t).prod P)` to `(0, t]` produces a
`BrownianIntegrable` integrand and preserves the Itô integral up to `t`. -/
private theorem IsItoIntegral.ite_le_brownianIntegrable
    (hI : IsItoIntegral ℱ P W H I) (hW : IsFilteredPreBrownianReal ℱ W P) (t : ℝ≥0)
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    IsItoIntegral ℱ P W (H - fun s ω ↦ if t < s then H s ω else 0)
        (I - fun s ω ↦ I s ω - I (min t s) ω) ∧
      BrownianIntegrable ℱ P (H - fun s ω ↦ if t < s then H s ω else 0) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let H_t : ℝ≥0 → Ω → ℝ := H - fun s ω ↦ if t < s then H s ω else 0
  let I_t : ℝ≥0 → Ω → ℝ := I - fun s ω ↦ I s ω - I (min t s) ω
  have hIt_ito : IsItoIntegral ℱ P W H_t I_t := by
    simpa only [one_mul] using
      hI.sub (hI.ite_lt_mul hW t (ξ := fun _ ↦ 1) stronglyMeasurable_const)
  refine ⟨hIt_ito, hIt_ito.isStronglyPredictable, fun S ↦ ?_⟩
  have hm := (hIt_ito.isStronglyPredictable.mono ℱ.predictable_le_prod).aestronglyMeasurable
    (μ := (timeMeasure S).prod P)
  rw [hm.memLp_two_iff_lintegral_enorm_sq_lt_top, lintegral_prod _ (hm.eNorm.pow_const 2)]
  calc
    _ = ∫⁻ s, ∫⁻ ω, (if s ≤ t then ‖H s ω‖ₑ ^ 2 else 0) ∂P ∂timeMeasure S := by
      refine lintegral_congr fun s ↦ lintegral_congr fun ω ↦ ?_
      simp only [Function.uncurry, H_t, Pi.sub_apply]
      by_cases hs : t < s
      · simp [hs, hs.not_ge]
      · simp [hs, not_lt.1 hs]
    _ = ∫⁻ s in Ioc 0 t, ∫⁻ ω, ‖H s ω‖ₑ ^ 2 ∂P ∂timeMeasure S := by
      rw [← lintegral_indicator measurableSet_Ioc]
      refine lintegral_congr_ae ((ae_mem_Ioc_timeMeasure S).mono fun s hs ↦ ?_)
      by_cases hle : s ≤ t
      · simp [hle, hs.1]
      · simp [hle]
    _ = ∫⁻ s, ∫⁻ ω, ‖H s ω‖ₑ ^ 2 ∂P ∂timeMeasure (min t S) := by
      rw [timeMeasure_restrict]
    _ ≤ ∫⁻ s, ∫⁻ ω, ‖H s ω‖ₑ ^ 2 ∂P ∂timeMeasure t :=
      lintegral_mono' (timeMeasure_mono (min_le_left t S)) le_rfl
    _ = ∫⁻ p, ‖H p.1 p.2‖ₑ ^ 2 ∂(timeMeasure t).prod P :=
      (lintegral_prod _ (hH.aestronglyMeasurable.eNorm.pow_const 2)).symm
    _ < ∞ := hH.aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.1 hH

/-- An Itô integral of an integrand with finite expected square energy on `(0, t]` is square
integrable at `t`. -/
theorem IsItoIntegral.memLp (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) : MemLp (I t) 2 P :=
  (Lp.memLp _).ae_eq (hI.ae_eq_l2Integral hW hH).symm

/-- **The Itô isometry**, in `L²` norms. Against a pre-Brownian motion relative to the
filtration, the `L²(P)` norm at time `t` of an Itô integral of an integrand with finite expected
square energy on `(0, t]` is the `L²` norm of the integrand for Lebesgue time on `(0,t]`
times `P`. -/
theorem IsItoIntegral.eLpNorm_eq (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    eLpNorm (I t) 2 P = eLpNorm (Function.uncurry H) 2 ((timeMeasure t).prod P) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let hHp := (ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).2 hH
  have hnorm : (eLpNorm (hW.l2Integral t (hHp.toLp (Function.uncurry H))) 2 P).toReal =
      (eLpNorm (hHp.toLp (Function.uncurry H)) 2 (ℱ.predictableMeasure P t)).toReal := by
    simpa only [Lp.norm_def] using (hW.l2Integral t).norm_map (hHp.toLp (Function.uncurry H))
  rw [eLpNorm_congr_ae (hI.ae_eq_l2Integral hW hH),
    (ENNReal.toReal_eq_toReal_iff' (Lp.memLp _).eLpNorm_ne_top (Lp.memLp _).eLpNorm_ne_top).1
      hnorm,
    eLpNorm_congr_ae hHp.coeFn_toLp, ℱ.predictableMeasure_def,
    eLpNorm_trim ℱ.predictable_le_prod hI.isStronglyPredictable]

/-- **The Itô isometry.** Against a pre-Brownian motion relative to the filtration, an Itô
integral `I` of an integrand `H` with finite expected square energy on `(0, t]` satisfies
`E[I_t²] = E ∫_(0,t] H_s² ds`. -/
theorem IsItoIntegral.integral_sq (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  have h := congrArg (fun x ↦ x.toReal ^ 2) (hI.eLpNorm_eq hW hH)
  simp only [← integral_norm_sq_eq_toReal_eLpNorm_sq (hI.memLp hW hH).aestronglyMeasurable,
    ← integral_norm_sq_eq_toReal_eLpNorm_sq hH.aestronglyMeasurable, Real.norm_eq_abs, sq_abs] at h
  exact h

/-- **Finite-horizon uniform `L²` convergence of elementary approximants.** Against an almost
surely continuous filtered pre-Brownian motion `W`, any family of left-measurable simple holdings
converging in `L²((timeMeasure T).prod P)` to a square-integrable integrand `H` has elementary
gains whose running supremum error on `[0, T]` converges to zero in `L²(P)`. -/
theorem IsItoIntegral.tendsto_eLpNorm_iSup_eNorm_simpleGains_sub
    (hI : IsItoIntegral ℱ P W H I) (hW : IsFilteredPreBrownianReal ℱ W P)
    (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    {ι : Type*} {l : Filter ι} {T : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure T).prod P))
    {n : ι → ℕ} {τ : ι → ℕ → ℝ≥0} {a : ι → ℕ → Ω → ℝ}
    (hτ : ∀ i, MonotoneOn (τ i) (Iic (n i)))
    (ha : ∀ i j, j < n i → StronglyMeasurable[ℱ (τ i j)] (a i j))
    (hlim : Tendsto (fun i ↦ eLpNorm
      (Function.uncurry (Finance.simpleHolding (τ i) (n i) (a i)) - Function.uncurry H) 2
        ((timeMeasure T).prod P)) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (fun ω ↦
      ⨆ t ≤ T, ‖Finance.simpleGains (τ i) (n i) (a i) W t ω - I t ω‖ₑ) 2 P) l (𝓝 0) := by
  classical
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨hIt_ito, hHt_bi⟩ := hI.ite_le_brownianIntegrable hW T hH
  obtain ⟨Y, hY_ito, -, hY_mart⟩ := hHt_bi.exists_isItoIntegral hW hWc
  have hIY_ind : (I - fun s ω ↦ I s ω - I (min T s) ω) ≡ᵐ[P] Y :=
    isItoIntegral_unique hW hIt_ito hY_ito
  have hIY : ∀ᵐ ω ∂P, ∀ t ≤ T, I t ω = Y t ω :=
    hIY_ind.mono fun ω hω t ht ↦ by simpa [ht] using hω t
  have hMem : ∀ i, ∃ M : ℝ≥0 → Ω → ℝ, Martingale M ℱ P ∧ (∀ᵐ ω ∂P, Continuous fun t ↦ M t ω) ∧
      (MemLp (Function.uncurry (Finance.simpleHolding (τ i) (n i) (a i))) 2
          ((timeMeasure T).prod P) →
        ∀ t ≤ T, ∀ ω, M t ω = Finance.simpleGains (τ i) (n i) (a i) W t ω) := fun i ↦ by
    by_cases hK : MemLp (Function.uncurry (Finance.simpleHolding (τ i) (n i) (a i))) 2
        ((timeMeasure T).prod P)
    · obtain ⟨M, hM, hMc, hMeq⟩ :=
        hW.exists_martingale_simpleGains_eq_on_Iic hWc (hτ i) (ha i) hK
      exact ⟨M, hM, hMc, fun _ ↦ hMeq⟩
    · exact ⟨0, martingale_zero _ ℱ P, .of_forall fun _ ↦ continuous_const, fun h ↦ absurd h hK⟩
  choose M hM_mart hM_cont hM_eq using hMem
  have hK_ev : ∀ᶠ i in l, MemLp (Function.uncurry (Finance.simpleHolding (τ i) (n i) (a i))) 2
      ((timeMeasure T).prod P) :=
    eventually_memLp_of_tendsto_eLpNorm_sub ENNReal.zero_ne_top hH hlim
  have hterm : Tendsto (fun i ↦ eLpNorm (M i T - Y T) 2 P) l (𝓝 0) := by
    refine hlim.congr' ?_
    filter_upwards [hK_ev] with i hK_mem
    have hGI : eLpNorm (Finance.simpleGains (τ i) (n i) (a i) W T - I T) 2 P =
        eLpNorm (Function.uncurry (Finance.simpleHolding (τ i) (n i) (a i)) -
          Function.uncurry H) 2 ((timeMeasure T).prod P) :=
      ((isItoIntegral_simpleGains hWc (hτ i) (ha i)).sub hI).eLpNorm_eq hW (hK_mem.sub hH)
    refine hGI.symm.trans (eLpNorm_congr_ae ?_)
    filter_upwards [hIY] with ω hω
    simp [hM_eq i hK_mem T le_rfl ω, hω T le_rfl]
  have hdoob := MeasureTheory.Martingale.tendsto_eLpNorm_iSup_eNorm_sub hY_mart hM_mart
    (hY_ito.ae_continuous.mono fun _ hc t _ ↦ hc.continuousAt.continuousWithinAt)
    (fun i ↦ (hM_cont i).mono fun _ hc t _ ↦ hc.continuousAt.continuousWithinAt)
    (by norm_num : (1 : ℝ≥0∞) < 2) (by norm_num) hterm
  refine hdoob.congr' ?_
  filter_upwards [hK_ev] with i hK_mem
  refine eLpNorm_congr_ae (hIY.mono fun ω hω ↦ ?_)
  refine iSup_congr fun t ↦ iSup_congr fun ht ↦ ?_
  rw [hM_eq i hK_mem t ht ω, hω t ht]

end TauCeti.Probability
