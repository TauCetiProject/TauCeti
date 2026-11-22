/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.L2
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Probability.BrownianMotion.Integral.Energy.Basic
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Martingale.LpLimit

/-!
# Existence of the Itô integral for square-integrable integrands and the Itô isometry

For a pre-Brownian motion `W` relative to a filtration and a predictable integrand `H` with
finite expected square energy on every finite horizon (`TauCeti.BrownianIntegrable`), this file
constructs the Itô integral of `H` against `W` and proves the Itô isometry.

* `TauCeti.BrownianIntegrable.exists_isItoIntegral`: when `W` has almost surely continuous paths,
  `H` has an Itô integral which is a predictable martingale.
* `TauCeti.Probability.IsItoIntegral.martingale`: every adapted Itô integral of `H` is a
  martingale.
* `TauCeti.Probability.IsFilteredPreBrownianReal.itoIntegral_isometry`,
  `TauCeti.Probability.IsItoIntegral.memLp`, `TauCeti.Probability.IsItoIntegral.eLpNorm_eq`,
  `TauCeti.Probability.IsItoIntegral.integral_sq`,
  `TauCeti.Probability.IsItoIntegral.eLpNorm_sub_eq`,
  `TauCeti.Probability.IsItoIntegral.integral_sub_sq`, and
  `TauCeti.Probability.IsItoIntegral.continuous_toLp`: every Itô integral `I` of `H` is square
  integrable at each time `t`, continuous in `L²(P)`, with `E[I_t²] = E ∫_(0,t] H_s² ds` and
  `E[(I_t - I_s)²] = E ∫_(s,t] H_u² du` for `s ≤ t` (and combined with the martingale property
  in `itoIntegral_isometry`).

The integral is the limit of the elementary integrals of bounded simple holdings approximating
`H` in `L²` of Lebesgue time times `P` on every finite horizon. By the elementary isometry
`TauCeti.Probability.IsFilteredPreBrownianReal.eLpNorm_simpleGains`, these elementary integrals
are Cauchy in `L²(P)` at every time. Their fixed-time limit is a martingale, and, when `W` has
continuous paths, the continuous martingale completion
`MeasureTheory.exists_continuous_martingale_of_cauchySeq_Lp` selects a predictable version with
almost surely continuous paths. Square integrability and the Itô isometry follow directly from
the fixed-time `L²` identification `ae_eq_l2Integral_of_isItoIntegral` and `eLpNorm_l2Integral`,
while `IsItoIntegral.martingale` uses `ae_eq_of_tendstoInMeasure`.

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
horizon have elementary martingales which are Cauchy in `L²(P)` at every time. -/
private theorem _root_.TauCeti.BrownianIntegrable.exists_simpleGains_cauchySeq
    (hH : BrownianIntegrable ℱ P H) (hW : IsFilteredPreBrownianReal ℱ W P) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ)
      (hmem : ∀ k t, MemLp (Finance.simpleGains (τ k) (n k) (a k) W t) 2 P),
      (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      (∀ k, Martingale (Finance.simpleGains (τ k) (n k) (a k) W) ℱ P) ∧
      (∀ t, CauchySeq fun k ↦ (hmem k t).toLp (Finance.simpleGains (τ k) (n k) (a k) W t)) ∧
      ∀ t, Tendsto (fun k ↦ eLpNorm (Function.uncurry (Finance.simpleHolding (τ k) (n k) (a k))
        - Function.uncurry H) 2 ((timeMeasure t).prod P)) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, haC, hKH⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (k : ℕ) := Finance.memLp_of_bound_stronglyMeasurable (P := P) (p := 2) (ha k) (haC k)
  have hmem (k : ℕ) (t : ℝ≥0) : MemLp (Finance.simpleGains (τ k) (n k) (a k) W t) 2 P :=
    hW.memLp_simpleGains (hτ k).monotoneOn (ha k) (ha₂ k) t
  have hK (k : ℕ) (t : ℝ≥0) : MemLp (Function.uncurry (Finance.simpleHolding (τ k) (n k) (a k)))
      2 ((timeMeasure t).prod P) :=
    MemLp.of_bound (((Finance.isStronglyPredictable_simpleHolding (ha k)).mono
        ℱ.predictable_le_prod).aestronglyMeasurable) (max (C k) 0)
      (ae_of_all _ fun p ↦
        Finance.norm_simpleHolding_le (hτ k).monotoneOn p.1 p.2 fun j hj ↦ haC k j hj p.2)
  refine ⟨n, τ, a, C, hmem, fun k ↦ (hτ k).monotoneOn, ha, haC, fun k ↦ ?_, fun t ↦ ?_, hKH⟩
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

/-- Shared continuous-martingale completion returning both the constructed Itô integral and a
bounded simple-holding sequence whose elementary integrals converge almost surely uniformly on
every finite horizon. -/
private theorem _root_.TauCeti.BrownianIntegrable.exists_isItoIntegral_approx
    (hH : BrownianIntegrable ℱ P H) (hW : IsFilteredPreBrownianReal ℱ W P)
    (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω) :
    ∃ (I : ℝ≥0 → Ω → ℝ) (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧ Martingale I ℱ P ∧
      (∀ T : ℝ≥0, Tendsto (fun k ↦ eLpNorm
        (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2) 2
          ((timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        TendstoUniformlyOn (fun k t ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω)
          (I · ω) atTop (Iic T) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, hmem, hτ, ha, haC, hmart, hcau, hKH⟩ :=
    hH.exists_simpleGains_cauchySeq hW
  obtain ⟨I, hI, hIp, hIlim, -, φ, hφ, hIc⟩ := exists_continuous_martingale_of_cauchySeq_Lp hmart
    (fun k ↦ hWc.mono fun ω hω ↦ Finance.continuous_simpleGains hω) hmem hcau
  refine ⟨I, fun k ↦ n (φ k), fun k ↦ τ (φ k), fun k ↦ a (φ k), fun k ↦ C (φ k),
    fun k ↦ hτ (φ k), fun k ↦ ha (φ k), fun k ↦ haC (φ k),
    ⟨hH.isStronglyPredictable, hIc.mono fun ω hω ↦ hω.1, fun t ↦ ⟨n, τ, a, hτ, ha,
      tendsto_measure_le_lintegral_enorm_sq_sub
        (fun k ↦ Finance.isStronglyPredictable_simpleHolding (ha k))
        (fun _ ↦ hH.isStronglyPredictable) (hKH t),
      tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (hIlim t).2⟩⟩,
    hIp, hI, fun T ↦ (hKH T).comp hφ.tendsto_atTop, hIc.mono fun _ hω ↦ hω.2⟩

/-- **Existence of the Itô integral for square-integrable integrands.** Against a pre-Brownian
motion relative to the filtration with almost surely continuous paths, every predictable
integrand with finite expected square energy on every finite horizon has an Itô integral which
is a predictable martingale. No usual conditions on the filtration are assumed. -/
theorem _root_.TauCeti.BrownianIntegrable.exists_isItoIntegral (hH : BrownianIntegrable ℱ P H)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω) :
    ∃ I, IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧ Martingale I ℱ P := by
  obtain ⟨I, -, -, -, -, -, -, -, hIito, hIp, hI, -, -⟩ := hH.exists_isItoIntegral_approx hW hWc
  exact ⟨I, hIito, hIp, hI⟩

/-- Every Itô integral of a `BrownianIntegrable` integrand against an almost surely continuous
filtered pre-Brownian motion is approximated almost surely uniformly on every finite horizon by a
single sequence of bounded simple holdings whose holdings converge in `L²` on every horizon. -/
theorem IsFilteredPreBrownianReal.exists_seq_simpleHolding_tendstoUniformlyOn
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, MonotoneOn (τ k) (Set.Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      (∀ T : ℝ≥0, Tendsto (fun k ↦ eLpNorm
        (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2) 2
          ((timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        TendstoUniformlyOn (fun k t ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω)
          (I · ω) atTop (Set.Iic T) := by
  obtain ⟨I₀, n, τ, a, C, hτ, ha, hb, hI₀ito, -, -, hKlim, hpath⟩ :=
    hH.exists_isItoIntegral_approx hW hcont
  refine ⟨n, τ, a, C, hτ, ha, hb, hKlim, hpath.mp ((isItoIntegral_unique hW hI hI₀ito).mono
    fun ω heq hω T ↦ ?_)⟩
  -- Pointwise path indistinguishability rewrites the target path `I · ω` to `I₀ · ω`.
  have hfun : (fun t ↦ I t ω) = fun t ↦ I₀ t ω := funext heq
  simpa only [hfun] using hω T

/-- **The martingale property of the Itô integral.** Against a pre-Brownian motion relative to
the filtration, an adapted Itô integral of a Brownian-integrable integrand is a martingale.
Neither path continuity of the integrator nor usual conditions on the filtration are needed. -/
theorem IsItoIntegral.martingale (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hIa : StronglyAdapted ℱ I) : Martingale I ℱ P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, -, hmem, hτ, ha, -, hmart, hcau, hKH⟩ :=
    hH.exists_simpleGains_cauchySeq hW
  obtain ⟨Z, hZ, hZlim⟩ := exists_martingale_of_cauchySeq_Lp hmart hmem hcau
  exact hZ.congr hIa fun t ↦ (hI.ae_eq_of_tendstoInMeasure hW hτ ha
    (tendsto_measure_le_lintegral_enorm_sq_sub
      (fun k ↦ Finance.isStronglyPredictable_simpleHolding (ha k))
      (fun _ ↦ hH.isStronglyPredictable) (hKH t))
    (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (hZlim t).2)).symm

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
    eLpNorm (I t) 2 P = eLpNorm (Function.uncurry H) 2 ((timeMeasure t).prod P) :=
  (eLpNorm_congr_ae (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t)).trans
    (hW.eLpNorm_l2Integral t hH.isStronglyPredictable (hH.memLp_predictableMeasure t))

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

/-- **The Itô increment isometry**, in `L²` norms. For `s ≤ t`, the `L²(P)` norm of `I t - I s`
equals the `L²` norm of the integrand for Lebesgue time on `(s, t]` times `P`. -/
theorem IsItoIntegral.eLpNorm_sub_eq (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    {s t : ℝ≥0} (hst : s ≤ t) :
    eLpNorm (I t - I s) 2 P =
      eLpNorm (Function.uncurry H) 2 (((timeMeasure t).restrict (Ioc s t)).prod P) :=
  (eLpNorm_congr_ae ((hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).sub
    (hW.ae_eq_l2Integral_of_isItoIntegral hH hI s))).trans
    (hW.eLpNorm_l2Integral_sub_of_le hH hst)

/-- **The Itô increment isometry.** For `s ≤ t`, an Itô integral `I` of a `BrownianIntegrable`
integrand `H` satisfies `E[(I_t - I_s)²] = E ∫_(s, t] H_u² du`. -/
theorem IsItoIntegral.integral_sub_sq (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, (I t ω - I s ω) ^ 2 ∂P =
      ∫ p, H p.1 p.2 ^ 2 ∂((timeMeasure t).restrict (Ioc s t)).prod P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hH₂ : AEStronglyMeasurable (Function.uncurry H)
      (((timeMeasure t).restrict (Ioc s t)).prod P) :=
    ((hH.isStronglyPredictable.mono ℱ.predictable_le_prod).aestronglyMeasurable).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hI₂ : AEStronglyMeasurable (I t - I s) P :=
    ((hI.memLp hW hH t).sub (hI.memLp hW hH s)).aestronglyMeasurable
  have h := congrArg (fun x ↦ x.toReal ^ 2) (hI.eLpNorm_sub_eq hW hH hst)
  simp only [← integral_norm_sq_eq_toReal_eLpNorm_sq hI₂,
    ← integral_norm_sq_eq_toReal_eLpNorm_sq hH₂, Pi.sub_apply, Real.norm_eq_abs, sq_abs] at h
  exact h

/-- An Itô integral of a `BrownianIntegrable` integrand defines a continuous `L²(P)`-valued
curve in time. -/
theorem IsItoIntegral.continuous_toLp (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) :
    Continuous fun t : ℝ≥0 ↦ (hI.memLp hW hH t).toLp (I t) := by
  have hEq : (fun t : ℝ≥0 ↦ (hI.memLp hW hH t).toLp (I t)) =
      fun t : ℝ≥0 ↦ hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) :=
    funext fun t ↦ Lp.ext ((hI.memLp hW hH t).coeFn_toLp.trans
      (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t))
  rw [hEq]
  exact hW.continuous_l2Integral hH

/-- **Combined Itô isometry and martingale theorem.** Against a pre-Brownian motion relative to
the filtration, an adapted Itô integral `I` of a `BrownianIntegrable` integrand `H` is a
square-integrable martingale satisfying `E[I_t²] = E ∫_(0,t] H_s² ds` and
`E[(I_t - I_s)²] = E ∫_(s, t] H_u² du` for all `s ≤ t`. -/
theorem IsFilteredPreBrownianReal.itoIntegral_isometry
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) (hIa : StronglyAdapted ℱ I) :
    Martingale I ℱ P ∧ (∀ t : ℝ≥0, MemLp (I t) 2 P) ∧
      (∀ t : ℝ≥0, ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∫ ω, (I t ω - I s ω) ^ 2 ∂P =
          ∫ p, H p.1 p.2 ^ 2 ∂((timeMeasure t).restrict (Ioc s t)).prod P) :=
  ⟨hI.martingale hW hH hIa, hI.memLp hW hH, hI.integral_sq hW hH,
    fun _ _ hst ↦ hI.integral_sub_sq hW hH hst⟩

end TauCeti.Probability
