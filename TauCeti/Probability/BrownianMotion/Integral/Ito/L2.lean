/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Deterministic
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto
import TauCeti.Probability.BrownianMotion.Integral.Restriction
import TauCeti.Probability.BrownianMotion.Integral.Simple
import TauCeti.Probability.BrownianMotion.Integral.Square
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Martingale.LpLimit
import TauCeti.Probability.Martingale.MaximalInequality.Basic
import TauCeti.Probability.Process.AccumulatedEnergy

/-!
# L² theory of the Itô stochastic integral

For a `TauCeti.BrownianIntegrable` integrand `H` and a filtered pre-Brownian motion `W`, the
characterization in `TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry` identifies any Itô
integral `I` satisfying `TauCeti.Probability.IsItoIntegral ℱ P W H I` almost surely at each finite
horizon `T` with the terminal `L²` integral `hW.l2Integral T`. This characterization yields:

* `TauCeti.Probability.IsFilteredPreBrownianReal.integral_eq_zero_of_isItoIntegral` and
  `integral_mul_of_isItoIntegral`: zero mean and cross-isometry.
* `TauCeti.Probability.IsFilteredPreBrownianReal.ae_eq_mul_sub_of_isItoIntegral_indicator_Ioc` and
  `indist_mul_sub_of_isItoIntegral_indicator_Ioc`: the `ℱ s`-measurable multiplier rule on `(s, u]`.
* `TauCeti.Probability.IsFilteredPreBrownianReal.tendsto_eLpNorm_sub_of_isItoIntegral` and
  `continuous_toLp_of_isItoIntegral`: `L²(P)` time continuity of the integral process.
* `TauCeti.Probability.IsFilteredPreBrownianReal.ae_eq_wienerIntegral_of_isItoIntegral` and
  `isItoIntegral_iff_ae_eq_wienerIntegral`: identification with the deterministic Wiener integral.
* `TauCeti.Probability.IsFilteredPreBrownianReal.tendsto_measure_exists_le_simpleGains_sub_lt`:
  Doob uniform approximation on `[0, T]` by elementary gains.
* `TauCeti.Probability.IsFilteredPreBrownianReal.martingale_sq_sub_of_isItoIntegral`,
  `setIntegral_sub_sq_of_isItoIntegral`, `condExp_sub_sq_of_isItoIntegral`,
  `withDensity_sq_predictableMeasure_Ioc_prod`, and
  `eq_withDensity_sq_predictableMeasure_of_Ioc_prod`: square compensation, conditional square
  increments on predictable rectangles, and identification of the integral's finite-horizon
  predictable measure with `(ℱ.predictableMeasure P T).withDensity (fun p ↦ ‖H p.1 p.2‖ₑ ^ 2)`.

Except where path continuity of `W` is required for Doob uniform approximation or unbounded
indistinguishability on `(s, u]`, none of these results assume path continuity of `W` or usual
conditions on `ℱ`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, §2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W H K I J : ℝ≥0 → Ω → ℝ}

/-! ### Moments and multiplier rule -/

/-- Every Itô integral of a Brownian-integrable process has expectation zero at each horizon. -/
theorem integral_eq_zero_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    ∫ ω, I t ω ∂P = 0 :=
  (integral_congr_ae (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t)).trans
    (hW.integral_l2Integral t _)

/-- **Itô cross-isometry.** The covariance of two Brownian-integrable Itô integrals at horizon `t`
equals the time-product inner product of their integrands on `(0, t]`. -/
theorem integral_mul_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) (t : ℝ≥0) :
    ∫ ω, I t ω * J t ω ∂P = ∫ p, H p.fst p.snd * K p.fst p.snd ∂(timeMeasure t).prod P := by
  let f := (hH.memLp_predictableMeasure t).toLp (Function.uncurry H)
  let g := (hK.memLp_predictableMeasure t).toLp (Function.uncurry K)
  calc ∫ ω, I t ω * J t ω ∂P
      = ⟪hW.l2Integral t f, hW.l2Integral t g⟫_ℝ := by
        rw [real_inner_comm, L2.inner_def]
        exact integral_congr_ae <| (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).mp <|
          (hW.ae_eq_l2Integral_of_isItoIntegral hK hJ t).mono fun _ hJω hIω ↦ by
            simp [f, g, hIω, hJω]
    _ = ∫ p, H p.fst p.snd * K p.fst p.snd ∂ℱ.predictableMeasure P t := by
        rw [(hW.l2Integral t).inner_map_map, real_inner_comm, L2.inner_def]
        exact integral_congr_ae <| (hH.memLp_predictableMeasure t).coeFn_toLp.mp <|
          (hK.memLp_predictableMeasure t).coeFn_toLp.mono fun ⟨_, _⟩ hpK hpH ↦ by
            simp only [RCLike.inner_apply, conj_trivial, f, g, hpH, hpK,
              Function.uncurry_apply_pair]
    _ = ∫ p, H p.fst p.snd * K p.fst p.snd ∂(timeMeasure t).prod P :=
        ℱ.integral_predictableMeasure P
          (hH.isStronglyPredictable.mul hK.isStronglyPredictable) t

/-- **Multiplier rule on `(s, u]` (fixed-time `L²` form).** For a square-integrable
`ℱ s`-measurable random variable `ξ` (in particular any bounded `ℱ s`-measurable random variable),
any Itô integral of `(Ioc s u).indicator (fun _ ↦ ξ ω)` agrees almost surely at each time `t`
with `ξ * (W (min u t) - W (min s t))`. Path continuity of `W` is not required. -/
theorem ae_eq_mul_sub_of_isItoIntegral_indicator_Ioc (hW : IsFilteredPreBrownianReal ℱ W P)
    {s u : ℝ≥0} (hsu : s ≤ u) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ)
    (hξ₂ : MemLp ξ 2 P)
    (hI : IsItoIntegral ℱ P W (fun t ω ↦ (Ioc s u).indicator (fun _ ↦ ξ ω) t) I) (t : ℝ≥0) :
    I t =ᵐ[P] fun ω ↦ ξ ω * (W (min u t) ω - W (min s t) ω) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hbi := TauCeti.brownianIntegrable_indicator_Ioc hξ hξ₂ (ℱ := ℱ) (P := P) (s := s) (u := u)
  have hL := (hW.ae_eq_l2Integral_of_isItoIntegral hbi hI t).trans
    (hW.coeFn_l2Integral_indicator_Ioc t s u hξ (hbi.memLp_predictableMeasure t))
  filter_upwards [hL] with ω hω
  rw [hω]
  by_cases hst : s ≤ t
  · simp [min_eq_left hst, max_eq_right (le_min hsu hst)]
  · have hts : t ≤ s := (not_le.mp hst).le
    simp [min_eq_right hts, min_eq_right (hts.trans hsu), max_eq_left hts]

/-- **Multiplier rule on `(s, u]` (indistinguishable process form).** When `W` has almost surely
continuous paths, any Itô integral of an `ℱ s`-measurable random variable `ξ` held on `(s, u]` is
indistinguishable from `t ↦ ξ * (W (min u t) - W (min s t))`. No moment condition on `ξ` is
needed. -/
theorem indist_mul_sub_of_isItoIntegral_indicator_Ioc (hW : IsFilteredPreBrownianReal ℱ W P)
    (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω) {s u : ℝ≥0} (hsu : s ≤ u) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ)
    (hI : IsItoIntegral ℱ P W (fun t ω ↦ (Ioc s u).indicator (fun _ ↦ ξ ω) t) I) :
    I ≡ᵐ[P] fun t ω ↦ ξ ω * (W (min u t) ω - W (min s t) ω) :=
  isItoIntegral_unique hW hI (isItoIntegral_indicator_Ioc hWc hsu hξ)

/-! ### L² continuity, deterministic bridge, and Doob uniform approximation -/

private theorem tendsto_indicator_Ioc_prod_ae (P : Measure Ω) [SFinite P] (T t : ℝ≥0)
    (f : ℝ≥0 × Ω → ℝ) :
    ∀ᵐ p ∂((timeMeasure T).prod P),
      Tendsto (fun s ↦ (Ioc 0 s ×ˢ (univ : Set Ω)).indicator f p)
        (𝓝 t) (𝓝 ((Ioc 0 t ×ˢ (univ : Set Ω)).indicator f p)) := by
  have hnull : ((timeMeasure T).prod P) ({t} ×ˢ (univ : Set Ω)) = 0 := by
    rw [Measure.prod_prod, timeMeasure_singleton, zero_mul]
  filter_upwards [compl_mem_ae_iff.mpr hnull] with p hp
  have hne : p.fst ≠ t := fun h ↦ hp ⟨h, mem_univ _⟩
  rcases hne.lt_or_gt with hlt | hgt
  · by_cases h0 : 0 < p.fst
    · have hmem : p ∈ Ioc 0 t ×ˢ (univ : Set Ω) := ⟨⟨h0, hlt.le⟩, mem_univ _⟩
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioi_mem_nhds hlt] with s hs
      have hmem' : p ∈ Ioc 0 s ×ˢ (univ : Set Ω) := ⟨⟨h0, hs.le⟩, mem_univ _⟩
      simp [hmem, hmem']
    · have hle : p.fst ≤ 0 := not_lt.mp h0
      refine tendsto_const_nhds.congr fun s ↦ ?_
      simp [hle]
  · have hnot : p ∉ Ioc 0 t ×ˢ (univ : Set Ω) := fun h ↦ hgt.not_ge h.1.2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Iio_mem_nhds hgt] with s hs
    have hnot' : p ∉ Ioc 0 s ×ˢ (univ : Set Ω) := fun h ↦ hs.not_ge h.1.2
    simp [hnot, hnot']

/-- **L² time continuity of the Itô integral.** Against a pre-Brownian motion, every Itô integral
of a Brownian-integrable integrand is continuous in `L²(P)` as a function of time. -/
theorem tendsto_eLpNorm_sub_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    Tendsto (fun s ↦ eLpNorm (I s - I t) 2 P) (𝓝 t) (𝓝 0) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let T : ℝ≥0 := t + 1
  let K (u : ℝ≥0) : ℝ≥0 × Ω → ℝ := (Ioc 0 u ×ˢ univ).indicator (Function.uncurry H)
  have hKp (u : ℝ≥0) : StronglyMeasurable[ℱ.predictable] (K u) :=
    hH.isStronglyPredictable.indicator (measurableSet_predictable_Ioc_prod 0 u MeasurableSet.univ)
  have hKm (u : ℝ≥0) : MemLp (K u) 2 (ℱ.predictableMeasure P T) :=
    (hH.memLp_predictableMeasure T).indicator
      (measurableSet_predictable_Ioc_prod 0 u (𝓕 := ℱ) MeasurableSet.univ).nullMeasurableSet
  -- Stage 1: represent every `I u` (`u ≤ t + 1`) on the common ambient horizon `T = t + 1`.
  have hIeq {u : ℝ≥0} (hu : u ≤ T) :
      I u =ᵐ[P] hW.l2Integral T ((hKm u).toLp (K u)) := by
    have hL : hW.l2Integral T ((hKm u).toLp (K u)) =
        hW.l2Integral u ((hH.memLp_predictableMeasure u).toLp (Function.uncurry H)) := by
      refine hW.l2Integral_eq_of_ae_eq_of_ae_eq_zero hu _ _ ?_ ?_
      · filter_upwards [(ℱ.predictableMeasure_mono P hu).absolutelyContinuous.ae_eq
          (hKm u).coeFn_toLp,
          (hH.memLp_predictableMeasure u).coeFn_toLp,
          ℱ.ae_mem_Ioc_prod_predictableMeasure P u] with p hKp hHp hmem
        dsimp only [K] at hKp
        rw [hKp, hHp, indicator_of_mem hmem]
      · filter_upwards [(hKm u).coeFn_toLp] with p hKp hgt
        dsimp only [K] at hKp
        rw [hKp, indicator_of_notMem]
        exact fun h ↦ hgt.not_ge h.1.2
    rw [hL]
    exact hW.ae_eq_l2Integral_of_isItoIntegral hH hI u
  -- Stage 2: transport the `L²(P)` difference to `L²((timeMeasure T).prod P)` on `𝓝 t`.
  have hcongr : ∀ᶠ s in 𝓝 t,
      eLpNorm (I s - I t) 2 P = eLpNorm (K s - K t) 2 ((timeMeasure T).prod P) := by
    filter_upwards [Iio_mem_nhds (lt_add_one t)] with s hs
    rw [eLpNorm_congr_ae ((hIeq hs.le).sub (hIeq (le_of_lt (lt_add_one t))))]
    exact hW.eLpNorm_l2Integral_sub T (hKp s) (hKp t) (hKm s) (hKm t)
  refine Tendsto.congr' (EventuallyEq.symm hcongr) ?_
  -- Stage 3: apply dominated convergence using the null slice `{t} ×ˢ univ`.
  refine TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (C := 2) (by norm_num)
    (Eventually.of_forall fun s ↦ ((hKp s).mono ℱ.predictable_le_prod).aestronglyMeasurable)
    (hH.memLp_timeMeasure T)
    (Eventually.of_forall fun s ↦ Eventually.of_forall fun p ↦ by
      calc ‖K s p - K t p‖ₑ ≤ ‖K s p‖ₑ + ‖K t p‖ₑ := eNorm_sub_le
        _ ≤ ‖H p.1 p.2‖ₑ + ‖H p.1 p.2‖ₑ :=
          add_le_add (eNorm_indicator_le_eNorm_self _ _) (eNorm_indicator_le_eNorm_self _ _)
        _ = (2 : ℝ≥0) * ‖H p.1 p.2‖ₑ := by rw [ENNReal.coe_ofNat, two_mul])
    (tendsto_indicator_Ioc_prod_ae P T t (Function.uncurry H))

/-- **L² continuity in `Lp ℝ 2 P`.** The `L²` class `t ↦ I t` of an Itô integral of a
Brownian-integrable integrand varies continuously with `t`. -/
theorem continuous_toLp_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) :
    Continuous fun t ↦ (hI.memLp hW hH t).toLp (I t) := by
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  rw [ContinuousAt, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  exact (hW.tendsto_eLpNorm_sub_of_isItoIntegral hH hI t).congr fun s ↦
    eLpNorm_congr_ae (((hI.memLp hW hH s).coeFn_toLp.sub (hI.memLp hW hH t).coeFn_toLp).symm)

/-- **Deterministic L² bridge.** For a measurable deterministic integrand `h` in `L²` on every
finite horizon, any Itô integral agrees almost surely at each horizon `T` with the Wiener
integral of `h`. -/
theorem ae_eq_wienerIntegral_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {h : ℝ≥0 → ℝ} (hm : Measurable h) (hLp : ∀ T : ℝ≥0, MemLp h 2 (timeMeasure T))
    (hI : IsItoIntegral ℱ P W (fun t _ ↦ h t) I) (T : ℝ≥0) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    I T =ᵐ[P] hW.toIsPreBrownianReal.wienerIntegral T ((hLp T).toLp h) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let hbi := TauCeti.brownianIntegrable_fst (ℱ := ℱ) (P := P) hm hLp
  refine (hW.ae_eq_l2Integral_of_isItoIntegral hbi hI T).trans ?_
  rw [hW.l2Integral_uncurry_eq_wienerIntegral T (hLp T) (hbi.memLp_predictableMeasure T)]

/-- **Deterministic L² characterization.** For a measurable deterministic integrand `h` in `L²` on
every finite horizon, an almost surely continuous process `I` is an Itô integral of `h` if and
only if `I T` agrees almost surely with the Wiener integral of `h` at every horizon `T`. -/
theorem isItoIntegral_iff_ae_eq_wienerIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {h : ℝ≥0 → ℝ} (hm : Measurable h) (hLp : ∀ T : ℝ≥0, MemLp h 2 (timeMeasure T))
    (hIcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    IsItoIntegral ℱ P W (fun t _ ↦ h t) I ↔
      ∀ T : ℝ≥0, I T =ᵐ[P] hW.toIsPreBrownianReal.wienerIntegral T ((hLp T).toLp h) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let hbi := TauCeti.brownianIntegrable_fst (ℱ := ℱ) (P := P) hm hLp
  rw [hW.isItoIntegral_iff_ae_eq_l2Integral hbi hIcont]
  refine forall_congr' fun T ↦ ?_
  rw [hW.l2Integral_uncurry_eq_wienerIntegral T (hLp T) (hbi.memLp_predictableMeasure T)]

/-- **Doob uniform approximation for elementary gains.** If simple holdings with square-integrable
left-measurable heights converge in `L²` on `(0, T] × Ω` to a Brownian-integrable integrand `H`,
then against an almost surely continuous pre-Brownian motion their elementary gains converge
uniformly on `[0, T]` in outer probability to any Itô integral of `H`. -/
theorem tendsto_measure_exists_le_simpleGains_sub_lt (hW : IsFilteredPreBrownianReal ℱ W P)
    (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    {n : ℕ → ℕ} {τ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (n k)))
    (ha : ∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j))
    (ha₂ : ∀ k j, j < n k → MemLp (a k j) 2 P)
    {T ε : ℝ≥0} (hε : 0 < ε)
    (hlim : Tendsto (fun k ↦ eLpNorm (Function.uncurry (Finance.simpleHolding (τ k) (n k) (a k)) -
      Function.uncurry H) 2 ((timeMeasure T).prod P)) atTop (𝓝 0)) :
    Tendsto (fun k ↦ P {ω | ∃ t ≤ T, (ε : ℝ) <
      |Finance.simpleGains (τ k) (n k) (a k) W t ω - I t ω|}) atTop (𝓝 0) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨J, hJI, -, hJmart⟩ := hH.exists_isItoIntegral hW hWc
  have hIJ : I ≡ᵐ[P] J := isItoIntegral_unique hW hI hJI
  have hset_congr (k : ℕ) :
      P {ω | ∃ t ≤ T, (ε : ℝ) < |Finance.simpleGains (τ k) (n k) (a k) W t ω - I t ω|} =
      P {ω | ∃ t ≤ T, (ε : ℝ) < |Finance.simpleGains (τ k) (n k) (a k) W t ω - J t ω|} :=
    measure_congr <| hIJ.mono fun ω hω ↦ by simp [hω]
  simp_rw [hset_congr]
  have hMmart (k : ℕ) : Martingale (Finance.simpleGains (τ k) (n k) (a k) W) ℱ P :=
    hW.martingale.simpleGains (hτ k) (ha k) fun j hj t ↦
      (hW.martingale_mul_sub_min (hτ k hj.le hj (Nat.le_succ j)) (ha k j hj)
        ((ha₂ k j hj).integrable one_le_two)).integrable t
  have hL2 : Tendsto (fun k ↦ eLpNorm (Finance.simpleGains (τ k) (n k) (a k) W T - J T) 2 P)
      atTop (𝓝 0) := by
    refine hlim.congr fun k ↦ ?_
    have hKm := Finance.memLp_simpleHolding_predictableMeasure (ha k) (ha₂ k) T
    rw [← hW.eLpNorm_l2Integral_sub T (Finance.isStronglyPredictable_simpleHolding (ha k))
      hH.isStronglyPredictable hKm (hH.memLp_predictableMeasure T)]
    exact eLpNorm_congr_ae
      ((hW.coeFn_l2Integral_simpleHolding (hτ k) (ha k) T hKm).sub
        (hW.ae_eq_l2Integral_of_isItoIntegral hH hJI T).symm)
  have hL1 : Tendsto (fun k ↦ eLpNorm (Finance.simpleGains (τ k) (n k) (a k) W T - J T) 1 P)
      atTop (𝓝 0) :=
    _root_.TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm one_le_two hL2
  simpa only [Real.norm_eq_abs] using hJmart.tendsto_measure_exists_le_norm_sub_lt hMmart
    (hJI.ae_continuous.mono fun _ hω t _ ↦ hω.continuousAt.continuousWithinAt)
    (fun _ ↦ hWc.mono fun _ hω t _ ↦
      (Finance.continuous_simpleGains hω).continuousAt.continuousWithinAt)
    hL1 hε

/-! ### L² square compensation, conditional increments, and predictable measure -/

private theorem exists_martingale_sq_sub_ae_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) :
    ∃ Z : ℝ≥0 → Ω → ℝ, Martingale Z ℱ P ∧ (∀ t, Z t =ᵐ[P] I t) ∧ (∀ t, MemLp (Z t) 2 P) ∧
      Martingale (fun t ω ↦ Z t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  -- Choose `L²`-approximating simple holdings whose gains converge in `L²` to a martingale
  -- `Z =ᵐ I`.
  obtain ⟨n, τ, a, Z, hτ, ha, ha₂, hlim, hZ, hZmem, hZlim, hZL⟩ :=
    hW.exists_simpleHolding_martingale_approx hH
  have hIZ (t : ℝ≥0) : Z t =ᵐ[P] I t :=
    (hZL t).trans (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).symm
  let B (k : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    ∑ j ∈ Finset.range (n k), a k j ω ^ 2 * (↑(min (τ k (j + 1)) t) - ↑(min (τ k j) t))
  -- Pass the elementary square-compensated martingales `M_k^2 - B_k` to the limit in `L¹(P)`.
  refine ⟨Z, hZ, hIZ, hZmem, martingale_of_tendsto_eLpNorm_one
    (fun k ↦ hW.martingale_sq_simpleGains_sub (hτ k) (ha k) (ha₂ k))
    (fun t ↦ (hZ.stronglyAdapted t).pow 2 |>.sub
      (hH.isStronglyPredictable.stronglyAdapted_integral_sq_timeMeasure t)) fun t ↦ ?_⟩
  have hsq_lim : Tendsto (fun k ↦ eLpNorm
      (fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - Z t ω ^ 2) 1 P) atTop (𝓝 0) :=
    TauCeti.tendsto_eLpNorm_sq_sub_one (hZmem t).eLpNorm_ne_top (hZlim t)
  -- Control `‖B_k t - ∫ H^2‖₁` by the `L¹` product-norm difference of the squared integrands.
  have henergy_lim : Tendsto (fun k ↦ eLpNorm
      (fun ω ↦ B k t ω - ∫ s, H s ω ^ 2 ∂timeMeasure t) 1 P) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (TauCeti.tendsto_eLpNorm_sq_sub_one (hH.memLp_timeMeasure t).eLpNorm_ne_top (hlim t))
      (fun _ ↦ zero_le) fun k ↦ ?_
    simp_rw [B, ← Finance.integral_sq_simpleHolding_timeMeasure (hτ k) t]
    have hKmem (ω : Ω) : Integrable (fun s ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω ^ 2)
        (timeMeasure t) := by
      simp only [Finance.simpleHolding_def]
      exact (memLp_finsetSum _ fun j _ ↦
        (memLp_const (a k j ω)).indicator measurableSet_Ioc.nullMeasurableSet).integrable_sq
    have hHmem : ∀ᵐ ω ∂P, Integrable (fun s ↦ H s ω ^ 2) (timeMeasure t) :=
      hH.locallyBrownianIntegrable.ae_memLp.mono fun ω hω ↦ by
        simpa only [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using (hω t).integrable_sq
    have hdiff_sm : AEStronglyMeasurable (fun p : ℝ≥0 × Ω ↦
        Finance.simpleHolding (τ k) (n k) (a k) p.fst p.snd ^ 2 - H p.fst p.snd ^ 2)
        ((timeMeasure t).prod P) :=
      ((((Finance.isStronglyPredictable_simpleHolding (ha k)).mono
        ℱ.predictable_le_prod).pow 2).sub
        ((hH.isStronglyPredictable.mono ℱ.predictable_le_prod).pow 2)).aestronglyMeasurable
    exact TauCeti.eLpNorm_integral_sub_integral_le_eLpNorm_prod
      (Eventually.of_forall hKmem) hHmem hdiff_sm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hsq_lim.add henergy_lim) (fun _ ↦ zero_le) fun k ↦ ?_
  have hsplit : ((fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - B k t ω) -
      (fun ω ↦ Z t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t)) =
      (fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - Z t ω ^ 2) -
        (fun ω ↦ B k t ω - ∫ s, H s ω ^ 2 ∂timeMeasure t) := by ext ω; simp; ring
  rw [hsplit]; exact eLpNorm_sub_le le_rfl

/-- **L² Itô square compensation (quadratic variation bracket).** For a Brownian-integrable
integrand and a strongly adapted Itô integral `I`, the process
`I t ^ 2 - ∫ s, H s ^ 2 ∂timeMeasure t` is a true martingale on the raw filtration.
Path continuity of `W` is not required. -/
theorem martingale_sq_sub_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (hI_adapt : StronglyAdapted ℱ I) :
    Martingale (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨Z, -, hZI, -, hMZ⟩ := exists_martingale_sq_sub_ae_eq hW hH hI
  exact hMZ.congr
    (fun t ↦ (hI_adapt t).pow 2 |>.sub
      (hH.isStronglyPredictable.stronglyAdapted_integral_sq_timeMeasure t))
    fun t ↦ (hZI t).mono fun ω hω ↦ by dsimp only; rw [hω]

/-- **Set-integral square increment on predictable rectangles.** For any Itô integral `I` of a
Brownian-integrable integrand `H`, the second moment of `I t - I s` over an `ℱ s`-measurable
event `A` equals the integral of the elapsed square energy `∫_(s, t] H_r² dr` over `A`. Neither
strong adaptedness of `I` nor path continuity of `W` is required. -/
theorem setIntegral_sub_sq_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, (I t ω - I s ω) ^ 2 ∂P =
      ∫ ω in A, ((∫ r, H r ω ^ 2 ∂timeMeasure t) - ∫ r, H r ω ^ 2 ∂timeMeasure s) ∂P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨Z, hZ, hZI, hZmem, hMZ⟩ := exists_martingale_sq_sub_ae_eq hW hH hI
  have hI_Z : ∫ ω in A, (I t ω - I s ω) ^ 2 ∂P = ∫ ω in A, (Z t ω - Z s ω) ^ 2 ∂P :=
    setIntegral_congr_ae (ℱ.le s A hA) <|
      (hZI t).mp <| (hZI s).mono fun ω hωs hωt _ ↦ by rw [hωt, hωs]
  have hMeq := hMZ.setIntegral_eq hst hA
  have hZt2 : IntegrableOn (fun ω ↦ Z t ω ^ 2) A P := (hZmem t).integrable_sq.integrableOn
  have hZs2 : IntegrableOn (fun ω ↦ Z s ω ^ 2) A P := (hZmem s).integrable_sq.integrableOn
  have hAt : IntegrableOn (fun ω ↦ ∫ r, H r ω ^ 2 ∂timeMeasure t) A P :=
    ((hH.memLp_timeMeasure t).integrable_sq).integral_prod_right.integrableOn
  have hAs : IntegrableOn (fun ω ↦ ∫ r, H r ω ^ 2 ∂timeMeasure s) A P :=
    ((hH.memLp_timeMeasure s).integrable_sq).integral_prod_right.integrableOn
  rw [hI_Z, hZ.setIntegral_sub_sq hst (hZmem t) hA, integral_sub hZt2 hZs2, integral_sub hAt hAs]
  rw [integral_sub hZt2 hAt, integral_sub hZs2 hAs] at hMeq
  linarith

/-- **Conditional square-increment identity.** For any Itô integral `I` of a Brownian-integrable
integrand `H`, `E[(I t - I s)² | ℱ s] = E[∫_(s, t] H_r² dr | ℱ s]` almost surely for `s ≤ t`. -/
theorem condExp_sub_sq_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω ↦ (I t ω - I s ω) ^ 2 | ℱ s] =ᵐ[P]
      P[fun ω ↦ (∫ r, H r ω ^ 2 ∂timeMeasure t) - ∫ r, H r ω ^ 2 ∂timeMeasure s | ℱ s] := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hA_int (u : ℝ≥0) : Integrable (fun ω ↦ ∫ r, H r ω ^ 2 ∂timeMeasure u) P :=
    ((hH.memLp_timeMeasure u).integrable_sq).integral_prod_right
  have hdiff_int :
      Integrable (fun ω ↦ (∫ r, H r ω ^ 2 ∂timeMeasure t) - ∫ r, H r ω ^ 2 ∂timeMeasure s) P :=
    (hA_int t).sub (hA_int s)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s)
    ((hI.memLp hW hH t).sub (hI.memLp hW hH s)).integrable_sq
    (fun _ _ _ ↦ integrable_condExp.integrableOn)
    (fun A hA _ ↦ ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  rw [setIntegral_condExp (ℱ.le s) hdiff_int hA]
  exact (hW.setIntegral_sub_sq_of_isItoIntegral hH hI hst hA).symm

/-- **Finite-horizon predictable measure on predictable rectangles.** For any Itô integral `I`
of a Brownian-integrable integrand `H` and any `T : ℝ≥0`, the squared-integrand measure
`(ℱ.predictableMeasure P T).withDensity (fun p ↦ ‖H p.1 p.2‖ₑ ^ 2)` assigns to every
predictable rectangle `Ioc s t ×ˢ A` (`s ≤ t`, `A ∈ ℱ s`) the value
`ENNReal.ofReal (∫ ω in A, (I (min t T) ω - I (min s T) ω) ^ 2 ∂P)`. -/
theorem withDensity_sq_predictableMeasure_Ioc_prod (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    ((ℱ.predictableMeasure P T).withDensity fun p ↦ ‖H p.1 p.2‖ₑ ^ 2) (Ioc s t ×ˢ A) =
      ENNReal.ofReal (∫ ω in A, (I (min t T) ω - I (min s T) ω) ^ 2 ∂P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  set ν : Measure (ℝ≥0 × Ω) := (ℱ.predictableMeasure P T).withDensity fun p ↦ ‖H p.1 p.2‖ₑ ^ 2
  have hν_ae : ∀ᵐ p ∂ν, p ∈ Ioc 0 T ×ˢ (univ : Set Ω) :=
    withDensity_absolutelyContinuous _ _ (ℱ.ae_mem_Ioc_prod_predictableMeasure P T)
  rw [← Measure.measure_inter_eq_of_ae hν_ae, Set.prod_inter_prod, univ_inter, Set.Ioc_inter_Ioc,
    max_eq_right zero_le, min_comm T t]
  rcases le_or_gt s T with hsT | hTs
  · let t' := min t T
    have hst' : s ≤ t' := le_min hst hsT
    have ht'T : t' ≤ T := min_le_right t T
    have hIeq : ∫ ω in A, (I t' ω - I s ω) ^ 2 ∂P =
        ∫ p in Ioc s t' ×ˢ A, H p.1 p.2 ^ 2 ∂ℱ.predictableMeasure P T :=
      (hW.setIntegral_sub_sq_of_isItoIntegral hH hI hst' hA).trans
        (hH.setIntegral_sq_timeMeasure_sub hst' ht'T hA)
    have hpred_nonneg : 0 ≤ᵐ[(ℱ.predictableMeasure P T).restrict (Ioc s t' ×ˢ A)]
        fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2 := Eventually.of_forall fun _ ↦ sq_nonneg _
    have hpred_int : Integrable (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2)
        ((ℱ.predictableMeasure P T).restrict (Ioc s t' ×ˢ A)) :=
      (hH.memLp_predictableMeasure T).integrable_sq.integrableOn
    rw [min_eq_left hsT, hIeq, withDensity_apply _ (measurableSet_predictable_Ioc_prod s t' hA),
      ofReal_integral_eq_lintegral_ofReal hpred_int hpred_nonneg]
    refine setLIntegral_congr_fun (measurableSet_predictable_Ioc_prod s t' hA) fun p _ ↦ ?_
    rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm]
  · simp only [min_eq_right hTs.le, min_eq_right (hTs.le.trans hst),
      Ioc_eq_empty_of_le hTs.le, empty_prod, measure_empty, sub_self,
      zero_pow (by norm_num : 2 ≠ 0), integral_zero, ENNReal.ofReal_zero]

/-- **Uniqueness of the finite-horizon predictable measure.** Any measure on `ℱ.predictable`
vanishing on `{0} ×ˢ univ` whose value on every predictable rectangle `Ioc s t ×ˢ A` (`s ≤ t`,
`A ∈ ℱ s`) equals `ENNReal.ofReal (∫ ω in A, (I (min t T) ω - I (min s T) ω) ^ 2 ∂P)`
coincides with `(ℱ.predictableMeasure P T).withDensity (fun p ↦ ‖H p.1 p.2‖ₑ ^ 2)`. -/
theorem eq_withDensity_sq_predictableMeasure_of_Ioc_prod
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) ℱ.predictable)
    (hzero : μ ({0} ×ˢ (univ : Set Ω)) = 0)
    (hrect : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → ∀ ⦃A : Set Ω⦄, MeasurableSet[ℱ s] A →
      μ (Ioc s t ×ˢ A) = ENNReal.ofReal (∫ ω in A, (I (min t T) ω - I (min s T) ω) ^ 2 ∂P)) :
    μ = (ℱ.predictableMeasure P T).withDensity fun p ↦ ‖H p.1 p.2‖ₑ ^ 2 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let ν : Measure (ℝ≥0 × Ω) := (ℱ.predictableMeasure P T).withDensity fun p ↦ ‖H p.1 p.2‖ₑ ^ 2
  have hν_fin : ν univ < ∞ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hlt := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      ENNReal.ofNat_ne_top (hH.memLp_predictableMeasure T).eLpNorm_lt_top
    simpa only [Function.uncurry_def, ENNReal.toReal_ofNat, ENNReal.rpow_two] using hlt
  obtain ⟨v, hv, hcover⟩ := ℱ.isCountablySpanning_elementarySets
  refine (Measure.ext_of_generateFrom_of_iUnion ℱ.elementarySets v
    ℱ.predictable_eq_generateFrom_elementarySets ℱ.isPiSystem_elementarySets
    hcover hv (fun n ↦ (measure_mono (subset_univ _)).trans_lt hν_fin |>.ne) fun u hu ↦ ?_).symm
  rcases (ℱ.mem_elementarySets_iff.mp hu) with ⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩
  · have hμ0 : μ ({(⊥ : ℝ≥0)} ×ˢ A) = 0 :=
      measure_mono_null (prod_mono_right (subset_univ A))
        (by simpa only [NNReal.bot_eq_zero] using hzero)
    have hν0 : ν ({(⊥ : ℝ≥0)} ×ˢ A) = 0 := by
      have h0 : ℱ.predictableMeasure P T ({(⊥ : ℝ≥0)} ×ˢ A) = 0 := by
        simpa only [NNReal.bot_eq_zero] using ℱ.predictableMeasure_singleton_zero_prod P T hA
      exact withDensity_absolutelyContinuous _ _ h0
    exact hν0.trans hμ0.symm
  · rcases le_or_gt s t with hst | hts
    · exact (hW.withDensity_sq_predictableMeasure_Ioc_prod hH hI T hst hA).trans
        (hrect hst hA).symm
    · simp only [Ioc_eq_empty_of_le hts.le, empty_prod, measure_empty]

end TauCeti.Probability.IsFilteredPreBrownianReal
