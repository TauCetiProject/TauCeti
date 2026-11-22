/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.Lebesgue.Norm
import TauCeti.Probability.BrownianMotion.Integral.Energy.Basic
import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Martingale.LpLimit
import TauCeti.Topology.Order.LeftRight

/-!
# Existence of the Itô integral for square-integrable integrands and the Itô isometry

For a pre-Brownian motion `W` relative to a filtration and a predictable integrand `H` with
finite expected square energy on every finite horizon (`TauCeti.BrownianIntegrable`), this file
constructs the Itô integral of `H` against `W` and proves the Itô isometry.

* `TauCeti.BrownianIntegrable.exists_isItoIntegral`: when `W` has almost surely continuous paths,
  `H` has an Itô integral which is a predictable martingale.
* `TauCeti.Probability.IsItoIntegral.martingale`: every adapted Itô integral of `H` is a
  martingale.
* `TauCeti.Probability.IsItoIntegral.memLp`, `TauCeti.Probability.IsItoIntegral.eLpNorm_eq` and
  `TauCeti.Probability.IsItoIntegral.integral_sq`: whenever `H` is square integrable on
  `(0, t] × Ω`, every Itô integral `I` of `H` is square integrable at `t`, with
  `E[I_t²] = E ∫_(0,t] H_s² ds`.
* `TauCeti.Probability.IsItoIntegral.tendsto_measure_exists_le_norm_simpleGains_sub_lt`: when `W`
  has almost surely continuous paths, the elementary gains of any simple holdings converging to `H`
  in pathwise square energy in probability on `(0, T]` converge uniformly on `[0, T]` in outer
  probability to every Itô integral `I`.

The integral is the limit of the elementary integrals of bounded simple holdings approximating
`H` in `L²` of Lebesgue time times `P` on every finite horizon. By the elementary isometry
`TauCeti.Probability.IsFilteredPreBrownianReal.eLpNorm_simpleGains`, these elementary integrals
are Cauchy in `L²(P)` at every time. Their fixed-time limit is a martingale, and, when `W` has
continuous paths, the continuous martingale completion
`MeasureTheory.exists_continuous_martingale_of_cauchySeq_Lp` selects a predictable version with
almost surely continuous paths. Any Itô integral agrees almost surely at each time with this
fixed-time limit, by `TauCeti.Probability.IsItoIntegral.ae_eq_of_tendstoInMeasure`, which gives
the martingale property and the isometry for every Itô integral.

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

/-- The elementary isometry for the difference of two simple holdings with square-integrable
heights: the `L²(P)` distance of their elementary integrals at `t` is the `L²` distance of the
holdings for Lebesgue time on `(0,t]` times `P`. -/
private theorem eLpNorm_simpleGains_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ σ : ℕ → ℝ≥0} {n m : ℕ} {a b : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n)) (hσ : MonotoneOn σ (Iic m))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j < m, StronglyMeasurable[ℱ (σ j)] (b j))
    (ha₂ : ∀ j < n, MemLp (a j) 2 P) (hb₂ : ∀ j < m, MemLp (b j) 2 P) (t : ℝ≥0) :
    eLpNorm (Finance.simpleGains τ n a W t - Finance.simpleGains σ m b W t) 2 P =
      eLpNorm (Function.uncurry (Finance.simpleHolding τ n a) -
        Function.uncurry (Finance.simpleHolding σ m b)) 2 ((timeMeasure t).prod P) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨N, ρ, c, -, hρ, hc, hhold, hgain⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sub ℱ hτ hσ ha hb
  have memLp_eval {ρ' : ℕ → ℝ≥0} {N' : ℕ} {d : ℕ → Ω → ℝ}
      (hd : ∀ j < N', MemLp (d j) 2 P) (u : ℝ≥0) :
      MemLp (fun ω ↦ Finance.simpleHolding ρ' N' d u ω) 2 P := by
    simp only [Finance.simpleHolding_def]
    refine memLp_finsetSum _ fun j hj ↦ ?_
    by_cases hu : u ∈ Ioc (ρ' j) (ρ' (j + 1))
    · simpa only [indicator_of_mem hu] using hd j (Finset.mem_range.mp hj)
    · simpa only [indicator_of_notMem hu] using (memLp_const (0 : ℝ) : MemLp (fun _ ↦ (0 : ℝ)) 2 P)
  -- Each height on the common grid is a value of the difference of the two holdings.
  have hc₂ (j : ℕ) (hj : j < N) : MemLp (c j) 2 P := by
    have hmem : ρ (j + 1) ∈ Ioc (ρ j) (ρ (j + 1)) :=
      ⟨hρ (mem_Iic.mpr hj.le) (mem_Iic.mpr hj) (Nat.lt_succ_self j), le_rfl⟩
    have hceq : c j = fun ω ↦
        Finance.simpleHolding τ n a (ρ (j + 1)) ω -
          Finance.simpleHolding σ m b (ρ (j + 1)) ω :=
      funext fun ω ↦ by
        rw [← Finance.simpleHolding_of_mem_Ioc (a := c) hρ.monotoneOn hj hmem ω, hhold]
    rw [hceq]
    exact (memLp_eval ha₂ _).sub (memLp_eval hb₂ _)
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
    have hH₂ := hH.memLp t
    have hconv : Tendsto (fun k ↦ (hK k t).toLp _) atTop (𝓝 (hH₂.toLp _)) :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun k ↦ hK k t) _ hH₂).2 (hKH t)
    have hdist (k l : ℕ) : dist ((hmem k t).toLp _) ((hmem l t).toLp _) =
        dist ((hK k t).toLp _) ((hK l t).toLp _) := by
      rw [dist_eq_norm, dist_eq_norm, ← MemLp.toLp_sub, ← MemLp.toLp_sub, Lp.norm_toLp,
        Lp.norm_toLp, eLpNorm_simpleGains_sub hW (hτ k).monotoneOn (hτ l).monotoneOn (ha k)
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
      (fun _ hε ↦ by
        simpa only [Function.uncurry_apply_pair, Pi.sub_apply, Nat.cast_ofNat] using
          TauCeti.tendsto_measure_lintegral_enorm_pow_of_tendsto_eLpNorm two_ne_zero (hKH t) hε)
      (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (hZlim t).2)
  · -- Pass to the limit in the elementary isometry, in both `L²` spaces.
    have hH₂ := hH.memLp t
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

/-- Restricting an integrand in `L²((timeMeasure t).prod P)` to `(0, t]` produces a
`BrownianIntegrable` integrand and preserves the Itô integral value at `t`. -/
private theorem IsItoIntegral.exists_martingale_ae_eq_of_memLp
    (hI : IsItoIntegral ℱ P W H I) (hW : IsFilteredPreBrownianReal ℱ W P)
    {t : ℝ≥0} (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    MemLp (I t) 2 P ∧
      eLpNorm (I t) 2 P = eLpNorm (Function.uncurry H) 2 ((timeMeasure t).prod P) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let H_t : ℝ≥0 → Ω → ℝ := H - fun s ω ↦ if t < s then H s ω else 0
  let I_t : ℝ≥0 → Ω → ℝ := I - fun s ω ↦ I s ω - I (min t s) ω
  have hIt_ito : IsItoIntegral ℱ P W H_t I_t := by
    simpa only [one_mul] using
      hI.sub (hI.ite_lt_mul hW t (ξ := fun _ ↦ 1) stronglyMeasurable_const)
  have hHt_bi : BrownianIntegrable ℱ P H_t := by
    refine ⟨hIt_ito.isStronglyPredictable, fun S ↦ ?_⟩
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
  obtain ⟨Z, -, hIZ⟩ := hIt_ito.exists_martingale_ae_eq hW hHt_bi
  have hIt_eq : I_t t = I t := by ext ω; simp [I_t]
  have hIZt := hIZ t
  rw [hIt_eq] at hIZt
  have hH_eq : eLpNorm (Function.uncurry H_t) 2 ((timeMeasure t).prod P) =
      eLpNorm (Function.uncurry H) 2 ((timeMeasure t).prod P) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae (ae_mem_Ioc_timeMeasure t)]
      with p hp
    simp [Function.uncurry, H_t, not_lt.2 hp.2]
  exact ⟨hIZt.2.1.ae_eq hIZt.1.symm, (eLpNorm_congr_ae hIZt.1).trans (hIZt.2.2.trans hH_eq)⟩

/-- An Itô integral of an integrand with finite expected square energy on `(0, t]` is square
integrable at `t`. -/
theorem IsItoIntegral.memLp (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) : MemLp (I t) 2 P :=
  (hI.exists_martingale_ae_eq_of_memLp hW hH).1

/-- **The Itô isometry**, in `L²` norms. Against a pre-Brownian motion relative to the
filtration, the `L²(P)` norm at time `t` of an Itô integral of an integrand with finite expected
square energy on `(0, t]` is the `L²` norm of the integrand for Lebesgue time on `(0,t]`
times `P`. -/
theorem IsItoIntegral.eLpNorm_eq (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) {t : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    eLpNorm (I t) 2 P = eLpNorm (Function.uncurry H) 2 ((timeMeasure t).prod P) :=
  (hI.exists_martingale_ae_eq_of_memLp hW hH).2

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

/-- Comparing two simple holdings on `[0, T]` via a common grid clipped at `T`: large difference
of their elementary gains on `[0, T]` requires large pathwise square-energy difference on `(0, T]`,
or an event of outer probability at most `γ / ε²`. -/
private theorem measure_exists_le_norm_simpleGains_sub_simpleGains_lt
    (hW : IsFilteredPreBrownianReal ℱ W P) (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    {T : ℝ≥0} {n₁ n₂ : ℕ} {τ₁ τ₂ : ℕ → ℝ≥0} {a₁ a₂ : ℕ → Ω → ℝ}
    (hτ₁ : MonotoneOn τ₁ (Iic n₁)) (hτ₂ : MonotoneOn τ₂ (Iic n₂))
    (ha₁ : ∀ j < n₁, StronglyMeasurable[ℱ (τ₁ j)] (a₁ j))
    (ha₂ : ∀ j < n₂, StronglyMeasurable[ℱ (τ₂ j)] (a₂ j))
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 ≤ γ) :
    P {ω | ∃ t ≤ T, ε < ‖Finance.simpleGains τ₁ n₁ a₁ W t ω -
        Finance.simpleGains τ₂ n₂ a₂ W t ω‖} ≤
      ENNReal.ofReal (γ / ε ^ 2) + P {ω | ENNReal.ofReal γ <
        ∫⁻ s, ‖Finance.simpleHolding τ₁ n₁ a₁ s ω -
          Finance.simpleHolding τ₂ n₂ a₂ s ω‖ₑ ^ 2 ∂timeMeasure T} := by
  obtain ⟨N, ρ, c, -, hρ, hc, hhold, hgains⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sub ℱ hτ₁ hτ₂ ha₁ ha₂
  let ρ' (j : ℕ) := min (ρ j) T
  let c' (j : ℕ) := if ρ j ≤ T then c j else 0
  have hρ' : MonotoneOn ρ' (Iic N) :=
    fun j hj k hk hjk ↦ min_le_min_right T (hρ.monotoneOn hj hk hjk)
  have hc' : ∀ j < N, StronglyMeasurable[ℱ (ρ' j)] (c' j) :=
    fun j hj ↦ Finance.stronglyMeasurable_ite_le_min hc T hj
  have hgain_eq (t : ℝ≥0) (ht : t ≤ T) (ω : Ω) :
      Finance.simpleGains ρ' N c' W t ω =
        Finance.simpleGains τ₁ n₁ a₁ W t ω - Finance.simpleGains τ₂ n₂ a₂ W t ω := by
    rw [← hgains W t ω, Finance.simpleGains_eq_sum_ite_le hρ',
      Finance.simpleGains_eq_sum_ite_le hρ.monotoneOn]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hmin (u : ℝ≥0) : min (min u T) t = min u t := by rw [min_assoc, min_eq_right ht]
    dsimp only [ρ', c']
    rw [hmin, hmin]
    by_cases hjt : ρ j ≤ t
    · simp [hjt, hjt.trans ht]
    · have htj : t ≤ ρ j := (not_le.1 hjt).le
      have hjN : j < N := Finset.mem_range.1 hj
      have htj1 : t ≤ ρ (j + 1) := htj.trans (hρ.monotoneOn hjN.le hjN (Nat.le_succ j))
      simp [hjt, min_eq_right htj, min_eq_right htj1]
  have henergy_eq (ω : Ω) : ENNReal.ofReal (elementaryEnergy ρ' c' N ω) =
      ∫⁻ s, ‖Finance.simpleHolding τ₁ n₁ a₁ s ω -
        Finance.simpleHolding τ₂ n₂ a₂ s ω‖ₑ ^ 2 ∂timeMeasure T := by
    rw [ofReal_elementaryEnergy_min_ite hρ.monotoneOn T ω]
    exact lintegral_congr fun s ↦ by rw [hhold s ω]
  calc
    P {ω | ∃ t ≤ T, ε < ‖Finance.simpleGains τ₁ n₁ a₁ W t ω -
          Finance.simpleGains τ₂ n₂ a₂ W t ω‖}
        ≤ P {ω | ∃ t, ε < |Finance.simpleGains ρ' N c' W t ω|} :=
      measure_mono fun ω ⟨t, ht, hlt⟩ ↦ ⟨t, by simpa only [hgain_eq t ht ω, Real.norm_eq_abs]⟩
    _ ≤ ENNReal.ofReal (γ / ε ^ 2) + P {ω | γ < elementaryEnergy ρ' c' N ω} :=
      hW.measure_exists_abs_simpleGains_gt_le hWc hρ' hc' hε hγ
    _ ≤ _ := add_le_add le_rfl (measure_mono fun ω (hω : γ < _) ↦ by
      simp only [mem_ofPred_eq] at hω ⊢
      rw [← henergy_eq ω]
      exact (ENNReal.ofReal_lt_ofReal_iff (hγ.trans_lt hω)).2 hω)

/-- **Finite-horizon uniform convergence of elementary gains in outer probability.** Against an
almost surely continuous filtered pre-Brownian motion `W`, any family of left-measurable simple
holdings converging to `H` in pathwise square energy in probability on `(0, T]` has elementary
gains converging uniformly on `[0, T]` in outer probability to every Itô integral `I` of `H`. -/
theorem IsItoIntegral.tendsto_measure_exists_le_norm_simpleGains_sub_lt
    (hI : IsItoIntegral ℱ P W H I) (hW : IsFilteredPreBrownianReal ℱ W P)
    (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    {ι : Type*} {l : Filter ι} {T : ℝ≥0} {n : ι → ℕ} {τ : ι → ℕ → ℝ≥0} {a : ι → ℕ → Ω → ℝ}
    (hτ : ∀ i, MonotoneOn (τ i) (Iic (n i)))
    (ha : ∀ i j, j < n i → StronglyMeasurable[ℱ (τ i j)] (a i j))
    (hE : ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun i ↦ P {ω | δ ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ i) (n i) (a i) s ω - H s ω‖ₑ ^ 2
        ∂timeMeasure T}) l (𝓝 0))
    {ε : ℝ≥0} (hε : 0 < ε) :
    Tendsto (fun i ↦ P {ω | ∃ t ≤ T,
      (ε : ℝ) < ‖Finance.simpleGains (τ i) (n i) (a i) W t ω - I t ω‖}) l (𝓝 0) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hE₂, _⟩ := hI.exists_approx T
  let G₂ (m : ℕ) := Finance.simpleGains (τ₂ m) (n₂ m) (a₂ m) W
  let K₂ (m : ℕ) := Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m)
  -- Step 1: Extract a rapidly uniformly Cauchy subsequence of `G₂` on `[0, T]`.
  have hcauchy (m : ℕ) : ∃ N, ∀ p ≥ N, ∀ q ≥ N,
      P {ω | ∃ t ≤ T, (2⁻¹ ^ m : ℝ) < ‖G₂ p t ω - G₂ q t ω‖} ≤ (2⁻¹ ^ m : ℝ≥0∞) := by
    have hlim : Tendsto (fun p : ℕ × ℕ ↦ P {ω | ∃ t ≤ T, (2⁻¹ ^ m : ℝ) <
        ‖G₂ p.1 t ω - G₂ p.2 t ω‖}) (atTop ×ˢ atTop) (𝓝 0) := by
      refine tendsto_measure_of_le_ofReal_div_sq_add (ε := (2⁻¹ ^ m : ℝ)) (fun δ hδ ↦ ?_)
        fun δ hδ p ↦ measure_exists_le_norm_simpleGains_sub_simpleGains_lt hW hWc
          (hτ₂ p.1) (hτ₂ p.2) (ha₂ p.1) (ha₂ p.2) (by positivity) hδ.le
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_measure_lintegral_enorm_sub_sq (l := atTop ×ˢ atTop)
          (f := fun p ↦ K₂ p.1) (g := fun p ↦ K₂ p.2) (h := fun _ ↦ H)
          (.of_forall fun p ↦ .of_forall fun ω ↦
            (((Finance.isStronglyPredictable_simpleHolding (ha₂ p.1)).stronglyMeasurable_path ω).sub
              (hI.isStronglyPredictable.stronglyMeasurable_path ω)).eNorm.pow_const 2
              |>.aemeasurable)
          (fun _ hγ ↦ (hE₂ _ hγ).comp tendsto_fst)
          (fun _ hγ ↦ (hE₂ _ hγ).comp tendsto_snd) (ENNReal.ofReal_pos.2 hδ))
        (fun _ ↦ zero_le) fun _ ↦ measure_mono fun _ (hω : ENNReal.ofReal δ < _) ↦ hω.le
    obtain ⟨U, hU, hUU⟩ :=
      mem_prod_self_iff.1 (hlim (gt_mem_nhds (show (0 : ℝ≥0∞) < 2⁻¹ ^ m from
        ENNReal.pow_pos (by norm_num) m)))
    obtain ⟨N, hN⟩ := mem_atTop_sets.1 hU
    exact ⟨N, fun p hp q hq ↦ (hUU (show (p, q) ∈ U ×ˢ U from ⟨hN p hp, hN q hq⟩)).le⟩
  choose N hN using hcauchy
  let k : ℕ → ℕ := Nat.rec (N 0) fun m km ↦ max (km + 1) (N (m + 1))
  have hk_ge (m : ℕ) : N m ≤ k m := by
    cases m with
    | zero => exact le_rfl
    | succ m => exact le_max_right _ _
  have hk_succ (m : ℕ) : N m ≤ k (m + 1) :=
    (hk_ge m).trans (Nat.le_succ _ |>.trans (le_max_left _ _))
  have hk_mono : StrictMono k := strictMono_nat_of_lt_succ fun m ↦
    (Nat.lt_succ_self (k m)).trans_le (le_max_left _ _)
  have hbc : ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ∀ t ≤ T, ‖G₂ (k (m + 1)) t ω - G₂ (k m) t ω‖ ≤ 2⁻¹ ^ m := by
    refine (ae_eventually_notMem (ne_top_of_le_ne_top (by
      rw [ENNReal.tsum_geometric]; norm_num) (tsum_le_tsum fun m ↦
      hN m (k (m + 1)) (hk_succ m) (k m) (hk_ge m)))).mono fun ω hω ↦ hω.mono fun m hm t ht ↦ ?_
    have hm' : ¬ ∃ t ≤ T, (2⁻¹ ^ m : ℝ) < ‖G₂ (k (m + 1)) t ω - G₂ (k m) t ω‖ := hm
    push Not at hm'
    exact hm' t ht
  -- Step 2: Identify the uniform limit with `I` on `[0, T]` via a countable dense set `S`.
  obtain ⟨S, hSc, hST, hS⟩ := TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt (α := ℝ) T
  have hW_meas : ∀ s, AEStronglyMeasurable (W s) P :=
    fun s ↦ ((hW.martingale.stronglyAdapted s).mono (ℱ.le s)).aestronglyMeasurable
  have hG₂_meas (m : ℕ) (s : ℝ≥0) : AEStronglyMeasurable (G₂ m s) P :=
    Finance.aestronglyMeasurable_simpleGains
      (fun j hj ↦ ((ha₂ m j hj).mono (ℱ.le _)).aestronglyMeasurable) fun _ _ ↦ hW_meas _
  have hS_lim : ∀ᵐ ω ∂P, ∀ s ∈ S, Tendsto (fun m ↦ G₂ (k m) s ω) atTop (𝓝 (I s ω)) := by
    rw [ae_ball_iff hSc]
    intro s hs
    have hcau : ∀ᵐ ω ∂P, CauchySeq (fun m ↦ G₂ (k m) s ω) := hbc.mono fun ω hω ↦ by
      obtain ⟨M, hM⟩ := eventually_atTop.1 hω
      have hshift : CauchySeq (fun m ↦ G₂ (k (m + M)) s ω) :=
        cauchySeq_of_le_geometric 2⁻¹ 1 (by norm_num) fun m ↦ by
          simpa only [one_mul, Real.dist_eq, abs_sub_comm, Real.norm_eq_abs, Nat.add_right_comm]
            using (hM (m + M) (Nat.le_add_left M m) s (hST hs)).trans
              (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right m M))
      rw [Metric.cauchySeq_iff] at hshift ⊢
      intro δ hδ
      obtain ⟨K, hK⟩ := hshift δ hδ
      exact ⟨K + M, fun p hp q hq ↦ by
        simpa only [Nat.sub_add_cancel (le_trans (Nat.le_add_left M K) hp),
          Nat.sub_add_cancel (le_trans (Nat.le_add_left M K) hq)] using
          hK (p - M) (Nat.le_sub_of_add_le hp) (q - M) (Nat.le_sub_of_add_le hq)⟩
    have hlim_in : TendstoInMeasure P (fun m ↦ G₂ (k m) s) atTop (I s) :=
      (hI.tendstoInMeasure_simpleGains_of_le hW (hST hs) hτ₂ ha₂ hE₂).comp
        hk_mono.tendsto_atTop
    let L (ω : Ω) := limUnder atTop fun m ↦ G₂ (k m) s ω
    have hae_L : ∀ᵐ ω ∂P, Tendsto (fun m ↦ G₂ (k m) s ω) atTop (𝓝 (L ω)) :=
      hcau.mono fun ω hω ↦ hω.tendsto_limUnder
    have hIL : I s =ᵐ[P] L := tendstoInMeasure_ae_unique hlim_in
      (tendstoInMeasure_of_tendsto_ae (fun m ↦ hG₂_meas _ s) hae_L)
    filter_upwards [hae_L, hIL] with ω hω hωL
    exact hωL ▸ hω
  have hsub_lim (η : ℝ) (hη : 0 < η) :
      Tendsto (fun m ↦ P {ω | ∃ t ≤ T, η < ‖G₂ (k m) t ω - I t ω‖}) atTop (𝓝 0) := by
    have hunif : ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ∀ s ∈ S, ‖G₂ (k m) s ω - I s ω‖ ≤ η := by
      filter_upwards [hbc, hS_lim] with ω hωbc hωS
      obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hωbc
      obtain ⟨M₁, hM₁⟩ := exists_nat_one_div_lt (by positivity : 0 < η / 2)
      refine eventually_atTop.2 ⟨max M₀ M₁, fun m hm s hs ↦ ?_⟩
      have hm₀ : M₀ ≤ m := (le_max_left _ _).trans hm
      have hm₁ : M₁ ≤ m := (le_max_right _ _).trans hm
      have hdiff (p : ℕ) (hmp : m ≤ p) : ‖G₂ (k p) s ω - G₂ (k m) s ω‖ ≤ 2 * (2⁻¹ ^ m : ℝ) := by
        have htele : G₂ (k p) s ω - G₂ (k m) s ω =
            ∑ j ∈ Finset.Ico m p, (G₂ (k (j + 1)) s ω - G₂ (k j) s ω) := by
          calc
            G₂ (k p) s ω - G₂ (k m) s ω
                = G₂ (k (m + (p - m))) s ω - G₂ (k (m + 0)) s ω := by
                  rw [Nat.add_sub_of_le hmp, add_zero]
            _ = ∑ i ∈ Finset.range (p - m), (G₂ (k (m + (i + 1))) s ω - G₂ (k (m + i)) s ω) :=
                  (Finset.sum_range_sub (fun i ↦ G₂ (k (m + i)) s ω) (p - m)).symm
            _ = ∑ j ∈ Finset.Ico m p, (G₂ (k (j + 1)) s ω - G₂ (k j) s ω) := by
                  rw [Finset.sum_Ico_eq_sum_range]
                  refine Finset.sum_congr rfl fun i _ ↦ by rw [Nat.add_assoc]
        rw [htele]
        calc
          ‖∑ j ∈ Finset.Ico m p, (G₂ (k (j + 1)) s ω - G₂ (k j) s ω)‖
              ≤ ∑ j ∈ Finset.Ico m p, ‖G₂ (k (j + 1)) s ω - G₂ (k j) s ω‖ :=
            norm_sum_le _ _
          _ ≤ ∑ j ∈ Finset.Ico m p, (2⁻¹ ^ j : ℝ) :=
            Finset.sum_le_sum fun j hj ↦
              hM₀ j (hm₀.trans (Finset.mem_Ico.1 hj).1) s (hST hs)
          _ = (2⁻¹ ^ m : ℝ) * ∑ j ∈ Finset.range (p - m), (2⁻¹ ^ j : ℝ) := by
            rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ ↦ by rw [pow_add]
          _ ≤ (2⁻¹ ^ m : ℝ) * 2 :=
            mul_le_mul_of_nonneg_left (by simpa only [one_div] using sum_geometric_two_le (p - m))
              (by positivity)
          _ = 2 * (2⁻¹ ^ m : ℝ) := mul_comm _ _
      have hlim_norm : Tendsto (fun p ↦ ‖G₂ (k p) s ω - G₂ (k m) s ω‖) atTop
          (𝓝 ‖I s ω - G₂ (k m) s ω‖) :=
        ((hωS s hs).sub tendsto_const_nhds).norm
      have hbound : ‖G₂ (k m) s ω - I s ω‖ ≤ 2 * (2⁻¹ ^ m : ℝ) := by
        rw [norm_sub_rev]
        exact le_of_tendsto hlim_norm (eventually_atTop.2 ⟨m, hdiff⟩)
      have hpow : (2⁻¹ ^ m : ℝ) ≤ 1 / ((m : ℝ) + 1) := by
        rw [inv_pow, one_div]
        gcongr
        exact_mod_cast Nat.lt_two_pow_self (n := m)
      have hsmall : 2 * (2⁻¹ ^ m : ℝ) < η := by
        calc
          2 * (2⁻¹ ^ m : ℝ) ≤ 2 * (1 / ((m : ℝ) + 1)) := by gcongr
          _ ≤ 2 * (1 / ((M₁ : ℝ) + 1)) := by gcongr
          _ < 2 * (η / 2) := by gcongr
          _ = η := mul_div_cancel₀ η two_ne_zero
      exact hbound.trans hsmall.le
    let A (m : ℕ) : Set Ω := ⋃ j ≥ m, ⋃ s ∈ S, {ω | η < ‖G₂ (k j) s ω - I s ω‖}
    have hA_meas (m : ℕ) : NullMeasurableSet (A m) P :=
      .iUnion fun j ↦ .iUnion fun _ ↦ .biUnion hSc fun s _ ↦
        nullMeasurableSet_lt aemeasurable_const
          ((hG₂_meas (k j) s).sub (hI.aestronglyMeasurable hW_meas s)).norm.aemeasurable
    have hA_anti : Antitone A := fun m₁ m₂ hm ↦ iUnion₂_mono' fun j hj ↦ ⟨j, hm.trans hj, le_rfl⟩
    have hA_null : P (⋂ m, A m) = 0 := by
      refine measure_mono_null (t := {ω | ¬ ∀ᶠ m in atTop, ∀ s ∈ S, ‖G₂ (k m) s ω - I s ω‖ ≤ η})
        (fun ω hω hunifω ↦ ?_) (ae_iff.1 hunif)
      obtain ⟨M, hM⟩ := eventually_atTop.1 hunifω
      obtain ⟨j, hj, s, hs, hlt⟩ := by
        simpa only [A, mem_iUnion, mem_ofPred_eq] using mem_iInter.1 hω M
      exact (hM j hj s hs).not_gt hlt
    have hA_lim : Tendsto (fun m ↦ P (A m)) atTop (𝓝 0) :=
      hA_null ▸ tendsto_measure_iInter_atTop hA_meas hA_anti ⟨0, measure_ne_top P _⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hA_lim (fun _ ↦ zero_le)
      fun m ↦ measure_mono_ae ?_
    filter_upwards [hWc, hI.ae_continuous] with ω hωW hωI ⟨t, ht, hlt⟩
    have hcont : Continuous fun u ↦ ‖G₂ (k m) u ω - I u ω‖ :=
      ((Finance.continuous_simpleGains hωW).sub hωI).norm
    obtain ⟨s, hs, hlt'⟩ := hS (fun u _ ↦ hcont.continuousAt.continuousWithinAt) ht hlt
    exact mem_iUnion₂.2 ⟨m, le_rfl, mem_iUnion₂.2 ⟨s, hs, hlt'⟩⟩
  -- Step 3: Approximate `I` by `G₂ (k m)` uniformly on `[0, T]`, and compare `G i` to `G₂ (k m)`.
  rw [ENNReal.tendsto_nhds_zero]
  intro c hc
  let c' : ℝ≥0∞ := min c 1
  have hc'0 : 0 < c' := lt_min hc one_pos
  have hc'top : c' ≠ ∞ := (min_le_right c 1 |>.trans_lt ENNReal.one_lt_top).ne
  have hc'4 : 0 < c' / 4 := ENNReal.div_pos hc'0.ne' (by norm_num)
  let ε₂ : ℝ := (ε : ℝ) / 2
  have hε₂ : 0 < ε₂ := half_pos hε
  let γ : ℝ := c'.toReal * ε₂ ^ 2 / 4
  have hγ : 0 < γ := by
    have : 0 < c'.toReal := ENNReal.toReal_pos hc'0.ne' hc'top
    positivity
  let γ' : ℝ≥0∞ := ENNReal.ofReal γ / 4
  have hγ' : 0 < γ' := ENNReal.div_pos (ENNReal.ofReal_pos.2 hγ).ne' (by norm_num)
  obtain ⟨m, hm1, hm2⟩ := (((hsub_lim ε₂ hε₂).eventually (gt_mem_nhds hc'4)).and
    (((hE₂ γ' hγ').comp hk_mono.tendsto_atTop).eventually (gt_mem_nhds hc'4))).exists
  filter_upwards [(hE γ' hγ').eventually (gt_mem_nhds hc'4)] with i hi
  have hsub_set : {ω | ∃ t ≤ T, (ε : ℝ) < ‖Finance.simpleGains (τ i) (n i) (a i) W t ω - I t ω‖} ⊆
      {ω | ∃ t ≤ T, ε₂ < ‖Finance.simpleGains (τ i) (n i) (a i) W t ω - G₂ (k m) t ω‖} ∪
        {ω | ∃ t ≤ T, ε₂ < ‖G₂ (k m) t ω - I t ω‖} := by
    rintro ω ⟨t, ht, hlt⟩
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_exists, not_and, not_lt] at hnot
    have htri := (norm_sub_le_norm_sub_add_norm_sub _ (G₂ (k m) t ω) _).trans
      (add_le_add (hnot.1 t ht) (hnot.2 t ht))
    linarith [show ε₂ + ε₂ = (ε : ℝ) by ring]
  have henergy_set : {ω | ENNReal.ofReal γ < ∫⁻ s, ‖Finance.simpleHolding (τ i) (n i) (a i) s ω -
        K₂ (k m) s ω‖ₑ ^ 2 ∂timeMeasure T} ⊆
      {ω | γ' ≤ ∫⁻ s, ‖Finance.simpleHolding (τ i) (n i) (a i) s ω - H s ω‖ₑ ^ 2
          ∂timeMeasure T} ∪
        {ω | γ' ≤ ∫⁻ s, ‖K₂ (k m) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure T} := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hnot
    have hsm : AEMeasurable (fun s ↦ ‖K₂ (k m) s ω - H s ω‖ₑ ^ 2) (timeMeasure T) :=
      (((Finance.isStronglyPredictable_simpleHolding (ha₂ (k m))).stronglyMeasurable_path ω).sub
        (hI.isStronglyPredictable.stronglyMeasurable_path ω)).eNorm.pow_const 2 |>.aemeasurable
    have hle : ∫⁻ s, ‖Finance.simpleHolding (τ i) (n i) (a i) s ω - K₂ (k m) s ω‖ₑ ^ 2
        ∂timeMeasure T ≤
        2 * ∫⁻ s, ‖Finance.simpleHolding (τ i) (n i) (a i) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure T +
          2 * ∫⁻ s, ‖K₂ (k m) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure T := by
      rw [← mul_add]
      refine (lintegral_congr fun s ↦ by rw [eNorm_sub_rev]).trans_le ?_
      exact (lintegral_enorm_sub_sq_le_two_mul hsm).trans_eq (by simp only [add_comm])
    have hlt_gam : ∫⁻ s, ‖Finance.simpleHolding (τ i) (n i) (a i) s ω - K₂ (k m) s ω‖ₑ ^ 2
        ∂timeMeasure T < ENNReal.ofReal γ := by
      calc
        _ ≤ 2 * ∫⁻ s, ‖Finance.simpleHolding (τ i) (n i) (a i) s ω - H s ω‖ₑ ^ 2
              ∂timeMeasure T +
            2 * ∫⁻ s, ‖K₂ (k m) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure T := hle
        _ < 2 * γ' + 2 * γ' := ENNReal.add_lt_add
          (ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hnot.1)
          (ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hnot.2)
        _ = ENNReal.ofReal γ := by
          dsimp only [γ']
          rw [← mul_add, ← two_mul, ← mul_assoc]
          norm_num
          exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
    exact hlt_gam.not_ge (Set.mem_ofPred.1 hω).le
  have hofReal_le : ENNReal.ofReal (γ / ε₂ ^ 2) ≤ c' / 4 := by
    have hquot : γ / ε₂ ^ 2 = c'.toReal / 4 := by dsimp [γ]; field_simp
    rw [hquot, ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_toReal hc'top]
    norm_num
  have hG_diff := (measure_exists_le_norm_simpleGains_sub_simpleGains_lt hW hWc (hτ i)
    (hτ₂ (k m)) (ha i) (ha₂ (k m)) hε₂ hγ.le).trans
    (add_le_add hofReal_le ((measure_mono henergy_set).trans (measure_union_le _ _)))
  have hc4_sum : c' / 4 + c' / 4 + c' / 4 + c' / 4 = c' := by
    calc
      c' / 4 + c' / 4 + c' / 4 + c' / 4 = (c' + c' + c' + c') / 4 := by
        simp only [add_assoc, ENNReal.div_add_div_same]
      _ = c' * 4 / 4 := by ring_nf
      _ = c' := ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  calc
    P {ω | ∃ t ≤ T, (ε : ℝ) < ‖Finance.simpleGains (τ i) (n i) (a i) W t ω - I t ω‖}
        ≤ P {ω | ∃ t ≤ T, ε₂ < ‖Finance.simpleGains (τ i) (n i) (a i) W t ω - G₂ (k m) t ω‖} +
          P {ω | ∃ t ≤ T, ε₂ < ‖G₂ (k m) t ω - I t ω‖} :=
      (measure_mono hsub_set).trans (measure_union_le _ _)
    _ ≤ (c' / 4 + (P {ω | γ' ≤ ∫⁻ s, ‖Finance.simpleHolding (τ i) (n i) (a i) s ω - H s ω‖ₑ ^ 2
            ∂timeMeasure T} +
          P {ω | γ' ≤ ∫⁻ s, ‖K₂ (k m) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure T})) +
        P {ω | ∃ t ≤ T, ε₂ < ‖G₂ (k m) t ω - I t ω‖} :=
      add_le_add hG_diff le_rfl
    _ ≤ c' / 4 + c' / 4 + c' / 4 + c' / 4 := by
      have hm2' : P {ω | γ' ≤ ∫⁻ s, ‖K₂ (k m) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure T} ≤ c' / 4 :=
        hm2.le
      exact (add_le_add (add_le_add le_rfl (add_le_add hi.le hm2')) hm1.le).trans_eq
        (by simp only [add_assoc])
    _ ≤ c := hc4_sum.le.trans (min_le_left _ _)

end TauCeti.Probability
