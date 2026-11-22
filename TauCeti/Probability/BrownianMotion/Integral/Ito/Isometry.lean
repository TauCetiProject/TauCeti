/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.Probability.BrownianMotion.Integral.Energy.Basic
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Martingale.LpLimit
import TauCeti.Probability.Martingale.MaximalInequality.Basic

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
  `TauCeti.Probability.IsItoIntegral.integral_sq`: every Itô integral `I` of `H` is square
  integrable at each time `t`, with `E[I_t²] = E ∫_(0,t] H_s² ds`.
* `TauCeti.Probability.IsItoIntegral.tendsto_measure_exists_le_norm_simpleGains_sub_lt`: when `W`
  has almost surely continuous paths, the elementary gains of any `L²`-approximating simple
  holdings on `(0, T]` converge uniformly on `[0, T]` in outer probability to the Itô integral `I`.

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

/-- **Finite-horizon uniform convergence of elementary gains in outer probability.** Against an
almost surely continuous filtered pre-Brownian motion `W`, any family of square-integrable
left-measurable simple holdings approximating `H` in `L²((timeMeasure T).prod P)` has elementary
gains converging uniformly on `[0, T]` in outer probability to every Itô integral `I` of `H`. -/
theorem IsItoIntegral.tendsto_measure_exists_le_norm_simpleGains_sub_lt
    (hI : IsItoIntegral ℱ P W H I) (hW : IsFilteredPreBrownianReal ℱ W P)
    (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} {τ : ι → ℕ → ℝ≥0} {a : ι → ℕ → Ω → ℝ}
    (hτ : ∀ i, MonotoneOn (τ i) (Iic (n i)))
    (ha : ∀ i j, j < n i → StronglyMeasurable[ℱ (τ i j)] (a i j))
    (ha₂ : ∀ i j, j < n i → MemLp (a i j) 2 P) {T : ℝ≥0}
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure T).prod P))
    (hKH : Tendsto (fun i ↦ eLpNorm (Function.uncurry (Finance.simpleHolding (τ i) (n i) (a i))
      - Function.uncurry H) 2 ((timeMeasure T).prod P)) l (𝓝 0))
    {ε : ℝ≥0} (hε : 0 < ε) :
    Tendsto (fun i ↦ P {ω | ∃ t ≤ T,
      (ε : ℝ) < ‖Finance.simpleGains (τ i) (n i) (a i) W t ω - I t ω‖}) l (𝓝 0) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  -- Restrict `H` and `I` to `(0, T]` to construct a continuous martingale realization `J`.
  let H_T : ℝ≥0 → Ω → ℝ := H - fun t ω ↦ if T < t then H t ω else 0
  let I_T : ℝ≥0 → Ω → ℝ := I - fun t ω ↦ I t ω - I (min T t) ω
  have hIT_ito : IsItoIntegral ℱ P W H_T I_T := by
    simpa only [one_mul] using
      hI.sub (hI.ite_lt_mul hW T (ξ := fun _ ↦ 1) stronglyMeasurable_const)
  have hHT_bi : BrownianIntegrable ℱ P H_T := by
    refine ⟨hIT_ito.isStronglyPredictable, fun S ↦ ?_⟩
    have hm := (hIT_ito.isStronglyPredictable.mono ℱ.predictable_le_prod).aestronglyMeasurable
      (μ := (timeMeasure S).prod P)
    rw [hm.memLp_two_iff_lintegral_enorm_sq_lt_top, lintegral_prod _ (hm.eNorm.pow_const 2)]
    calc
      _ = ∫⁻ t, ∫⁻ ω, (if t ≤ T then ‖H t ω‖ₑ ^ 2 else 0) ∂P ∂timeMeasure S := by
        refine lintegral_congr fun t ↦ lintegral_congr fun ω ↦ ?_
        simp only [Function.uncurry, H_T, Pi.sub_apply]
        by_cases ht : T < t
        · simp [ht, ht.not_ge]
        · simp [ht, not_lt.1 ht]
      _ = ∫⁻ t in Ioc 0 T, ∫⁻ ω, ‖H t ω‖ₑ ^ 2 ∂P ∂timeMeasure S := by
        rw [← lintegral_indicator measurableSet_Ioc]
        refine lintegral_congr_ae ((ae_mem_Ioc_timeMeasure S).mono fun t ht ↦ ?_)
        by_cases hle : t ≤ T
        · simp [hle, ht.1]
        · simp [hle]
      _ = ∫⁻ t, ∫⁻ ω, ‖H t ω‖ₑ ^ 2 ∂P ∂timeMeasure (min T S) := by
        rw [timeMeasure_restrict]
      _ ≤ ∫⁻ t, ∫⁻ ω, ‖H t ω‖ₑ ^ 2 ∂P ∂timeMeasure T :=
        lintegral_mono' (timeMeasure_mono (min_le_left T S)) le_rfl
      _ = ∫⁻ p, ‖H p.1 p.2‖ₑ ^ 2 ∂(timeMeasure T).prod P :=
        (lintegral_prod _ (hH.aestronglyMeasurable.eNorm.pow_const 2)).symm
      _ < ∞ := hH.aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.1 hH
  obtain ⟨J, hJ_ito, -, hJ_mart⟩ := hHT_bi.exists_isItoIntegral hW hWc
  have hIJ : I_T ≡ᵐ[P] J := isItoIntegral_unique hW hIT_ito hJ_ito
  -- Each simple holding is Brownian-integrable, and its gains form an a.s. continuous martingale.
  have hK_bi (i : ι) : BrownianIntegrable ℱ P (Finance.simpleHolding (τ i) (n i) (a i)) := by
    refine ⟨Finance.isStronglyPredictable_simpleHolding (ha i), fun S ↦ ?_⟩
    simp only [Function.uncurry_def, Finance.simpleHolding_def]
    refine memLp_finsetSum _ fun j hj ↦ ?_
    have hj' : j < n i := Finset.mem_range.1 hj
    have hind : (fun p : ℝ≥0 × Ω ↦ (Ioc (τ i j) (τ i (j + 1))).indicator
        (fun _ ↦ a i j p.2) p.1) =
        (Ioc (τ i j) (τ i (j + 1)) ×ˢ univ).indicator (fun p : ℝ≥0 × Ω ↦ a i j p.2) := by
      ext p; by_cases hp : p.1 ∈ Ioc (τ i j) (τ i (j + 1)) <;> simp [hp]
    rw [hind]
    exact ((ha₂ i j hj').comp_snd (timeMeasure S)).indicator
      (measurableSet_Ioc.prod MeasurableSet.univ).nullMeasurableSet
  have hG_mart (i : ι) : Martingale (Finance.simpleGains (τ i) (n i) (a i) W) ℱ P := by
    refine hW.martingale.simpleGains (hτ i) (ha i) fun j hj t ↦ ?_
    by_cases hjt : τ i j ≤ t
    · have hle : τ i j ≤ min (τ i (j + 1)) t :=
        le_min (hτ i hj.le hj (Nat.le_succ j)) hjt
      rw [min_eq_left hjt]
      exact (hW.memLp_mul_sub hle (ha i j hj) (ha₂ i j hj)).integrable one_le_two
    · have htj : t ≤ τ i j := (not_le.1 hjt).le
      have hle : t ≤ τ i (j + 1) := htj.trans (hτ i hj.le hj (Nat.le_succ j))
      simp [min_eq_right htj, min_eq_right hle]
  -- Apply the Itô isometry to `G i - J` at horizon `T`.
  have heLp2 (i : ι) : eLpNorm (Finance.simpleGains (τ i) (n i) (a i) W T - J T) 2 P =
      eLpNorm (Function.uncurry (Finance.simpleHolding (τ i) (n i) (a i)) -
        Function.uncurry H) 2 ((timeMeasure T).prod P) := by
    have hdiff_ito : IsItoIntegral ℱ P W (Finance.simpleHolding (τ i) (n i) (a i) - H_T)
        (Finance.simpleGains (τ i) (n i) (a i) W - J) :=
      (isItoIntegral_simpleGains hWc (hτ i) (ha i)).sub hJ_ito
    have hdiff_bi : BrownianIntegrable ℱ P (Finance.simpleHolding (τ i) (n i) (a i) - H_T) := by
      rw [show Finance.simpleHolding (τ i) (n i) (a i) - H_T =
          fun t ω ↦ Finance.simpleHolding (τ i) (n i) (a i) t ω + (-1) * H_T t ω from by
        funext t ω; simp [sub_eq_add_neg]]
      exact (hK_bi i).add (hHT_bi.const_mul (-1))
    rw [show Finance.simpleGains (τ i) (n i) (a i) W T - J T =
        (Finance.simpleGains (τ i) (n i) (a i) W - J) T from rfl,
      hdiff_ito.eLpNorm_eq hW hdiff_bi T]
    refine eLpNorm_congr_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae (ae_mem_Ioc_timeMeasure T)]
      with p hp
    have hle : ¬ T < p.1 := not_lt.2 hp.2
    simp [Function.uncurry, H_T, hle]
  have hlim1 : Tendsto (fun i ↦ eLpNorm (Finance.simpleGains (τ i) (n i) (a i) W T - J T) 1 P)
      l (𝓝 0) :=
    TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm one_le_two
      (hKH.congr fun i ↦ (heLp2 i).symm)
  have hmax := hJ_mart.tendsto_measure_exists_le_norm_sub_lt hG_mart
    (hJ_ito.ae_continuous.mono fun _ hc t _ ↦ hc.continuousAt.continuousWithinAt)
    (fun i ↦ hWc.mono fun _ hc t _ ↦
      (Finance.continuous_simpleGains hc).continuousAt.continuousWithinAt)
    hlim1 hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmax (fun _ ↦ zero_le)
    fun i ↦ measure_mono_ae (hIJ.mono fun ω hω ⟨t, ht, hlt⟩ ↦ ⟨t, ht, ?_⟩)
  have hIt : I t ω = J t ω := by
    have h := hω t
    simpa only [I_T, Pi.sub_apply, min_eq_right ht, sub_sub_cancel] using h
  rwa [← hIt]

end TauCeti.Probability
