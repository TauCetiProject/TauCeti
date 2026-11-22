/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Deterministic
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto
import TauCeti.Probability.BrownianMotion.Integral.Restriction
import TauCeti.Probability.BrownianMotion.Integral.Simple
import TauCeti.Probability.BrownianMotion.Integral.Square
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Martingale.LpLimit
import TauCeti.Probability.Martingale.MaximalInequality.Basic
import TauCeti.Probability.Process.AccumulatedEnergy

/-!
# L² theory of the Itô stochastic integral

For a `TauCeti.BrownianIntegrable` integrand `H` and a filtered pre-Brownian motion `W`, any
Itô integral `I` satisfying `TauCeti.Probability.IsItoIntegral ℱ P W H I` agrees almost surely at
each finite horizon `T` with the terminal `L²` integral `hW.l2Integral T`. This characterization
yields:

* `TauCeti.Probability.IsFilteredPreBrownianReal.isItoIntegral_iff_ae_eq_l2Integral`,
  `integral_eq_zero_of_isItoIntegral`, `integral_mul_of_isItoIntegral`: L² characterization,
  zero mean, and cross-isometry.
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

/-! ### Characterization, moments, and multiplier rule -/

/-- **L² characterization of Itô integrals.** For a Brownian-integrable integrand `H`, an almost
surely continuous process `I` is an Itô integral of `H` if and only if `I T` agrees almost surely
with the terminal `L²` integral `hW.l2Integral T` at every horizon `T`. Path continuity of `W` is
not required. -/
theorem isItoIntegral_iff_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hIcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)) :
    IsItoIntegral ℱ P W H I ↔
      ∀ T : ℝ≥0, I T =ᵐ[P]
        hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) := by
  refine ⟨fun hI T ↦ hW.ae_eq_l2Integral_of_isItoIntegral hH hI T, fun hT ↦ ?_⟩
  obtain ⟨n, τ, a, -, hmem, hτ, ha, -, -, -, -, hE, hLp⟩ := hW.exists_simpleHolding_approx hH
  refine ⟨hH.isStronglyPredictable, hIcont, fun T ↦
    ⟨n, τ, a, hτ, ha, hE T,
      (tendstoInMeasure_of_tendsto_Lp (hLp T)).congr
        (fun k ↦ (hmem k T).coeFn_toLp) (hT T).symm⟩⟩

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
          (hK.memLp_predictableMeasure t).coeFn_toLp.mono fun _ hpK hpH ↦ by
            simp only [RCLike.inner_apply, conj_trivial, f, g, hpH, hpK]; rfl
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
  have hcongr : ∀ᶠ s in 𝓝 t,
      eLpNorm (I s - I t) 2 P = eLpNorm (K s - K t) 2 ((timeMeasure T).prod P) := by
    filter_upwards [Iio_mem_nhds (lt_add_one t)] with s hs
    rw [eLpNorm_congr_ae ((hIeq hs.le).sub (hIeq (le_of_lt (lt_add_one t))))]
    exact hW.eLpNorm_l2Integral_sub T (hKp s) (hKp t) (hKm s) (hKm t)
  refine Tendsto.congr' (EventuallyEq.symm hcongr) ?_
  have hnull : ((timeMeasure T).prod P) {p : ℝ≥0 × Ω | p.fst = t} = 0 := by
    have ht0 : timeMeasure T {t} = 0 := by
      rw [timeMeasure_apply T (measurableSet_singleton t)]
      exact (Set.subsingleton_singleton.image _ |>.anti
        (Set.image_mono inter_subset_left)).measure_zero _
    have hset : {p : ℝ≥0 × Ω | p.fst = t} = {t} ×ˢ univ := by ext p; simp
    rw [hset, Measure.prod_prod, ht0, zero_mul]
  refine TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (C := 2) (by norm_num)
    (Eventually.of_forall fun s ↦ ((hKp s).mono ℱ.predictable_le_prod).aestronglyMeasurable)
    (hH.memLp_timeMeasure T)
    (Eventually.of_forall fun s ↦ Eventually.of_forall fun p ↦ by
      calc ‖K s p - K t p‖ₑ ≤ ‖K s p‖ₑ + ‖K t p‖ₑ := eNorm_sub_le
        _ ≤ ‖H p.1 p.2‖ₑ + ‖H p.1 p.2‖ₑ :=
          add_le_add (eNorm_indicator_le_eNorm_self _ _) (eNorm_indicator_le_eNorm_self _ _)
        _ = (2 : ℝ≥0) * ‖H p.1 p.2‖ₑ := by rw [ENNReal.coe_ofNat, two_mul])
    (?_)
  filter_upwards [compl_mem_ae_iff.mpr hnull] with p hp
  have hne : p.fst ≠ t := hp
  rcases hne.lt_or_gt with hlt | hgt
  · by_cases h0 : 0 < p.fst
    · have hmem : p ∈ Ioc 0 t ×ˢ (univ : Set Ω) := ⟨⟨h0, hlt.le⟩, mem_univ _⟩
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioi_mem_nhds hlt] with s hs
      have hmem' : p ∈ Ioc 0 s ×ˢ (univ : Set Ω) := ⟨⟨h0, hs.le⟩, mem_univ _⟩
      simp [K, hmem, hmem']
    · have hle : p.fst ≤ 0 := not_lt.mp h0
      refine tendsto_const_nhds.congr fun s ↦ ?_
      simp [K, hle]
  · have hnot : p ∉ Ioc 0 t ×ˢ (univ : Set Ω) := fun h ↦ hgt.not_ge h.1.2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Iio_mem_nhds hgt] with s hs
    have hnot' : p ∉ Ioc 0 s ×ˢ (univ : Set Ω) := fun h ↦ hs.not_ge h.1.2
    simp [K, hnot, hnot']

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
  rw [← hW.l2Integral_compMeasurePreserving_fst T ((hLp T).toLp h),
    Lp.toLp_compMeasurePreserving (hLp T) (ℱ.measurePreserving_fst_predictableMeasure P T)]
  rfl

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
  rw [← hW.l2Integral_compMeasurePreserving_fst T ((hLp T).toLp h),
    Lp.toLp_compMeasurePreserving (hLp T) (ℱ.measurePreserving_fst_predictableMeasure P T)]
  rfl

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
  have hMmart (k : ℕ) : Martingale (Finance.simpleGains (τ k) (n k) (a k) W) ℱ P := by
    have hsum : Finance.simpleGains (τ k) (n k) (a k) W = ∑ j ∈ Finset.range (n k),
        fun t ω ↦ a k j ω * (W (min (τ k (j + 1)) t) ω - W (min (τ k j) t) ω) := by
      ext t ω; simp [Finance.simpleGains_def, Finset.sum_apply]
    rw [hsum]
    refine Finset.sum_induction _ (Martingale · ℱ P) (fun _ _ ↦ Martingale.add)
      (martingale_zero _ ℱ P) fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    exact hW.martingale_mul_sub_min (hτ k hj'.le hj' (Nat.le_succ j)) (ha k j hj')
      ((ha₂ k j hj').integrable one_le_two)
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
  have hA_adapt : StronglyAdapted ℱ (fun t ω ↦ ∫ s, H s ω ^ 2 ∂timeMeasure t) :=
    hH.isStronglyPredictable.isStronglyPredictable_integral_sq_timeMeasure
      |>.isStronglyProgressive.stronglyAdapted
  obtain ⟨n, τ, a, Z, hτ, ha, ha₂, hlim, hZ, hZmem, hZlim, hZL⟩ :=
    hW.exists_simpleHolding_martingale_approx hH
  have hIZ (t : ℝ≥0) : Z t =ᵐ[P] I t :=
    (hZL t).trans (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).symm
  let B (k : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    ∑ j ∈ Finset.range (n k), a k j ω ^ 2 * (↑(min (τ k (j + 1)) t) - ↑(min (τ k j) t))
  refine ⟨Z, hZ, hIZ, hZmem, martingale_of_tendsto_eLpNorm_one
    (fun k ↦ hW.martingale_sq_simpleGains_sub (hτ k) (ha k) (ha₂ k))
    (fun t ↦ (hZ.stronglyAdapted t).pow 2 |>.sub (hA_adapt t)) fun t ↦ ?_⟩
  have hsq_lim : Tendsto (fun k ↦ eLpNorm
      (fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - Z t ω ^ 2) 1 P) atTop (𝓝 0) :=
    TauCeti.tendsto_eLpNorm_sq_sub_one (hZmem t).eLpNorm_ne_top (hZlim t)
  have henergy_lim : Tendsto (fun k ↦ eLpNorm
      (fun ω ↦ B k t ω - ∫ s, H s ω ^ 2 ∂timeMeasure t) 1 P) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (TauCeti.tendsto_eLpNorm_sq_sub_one (hH.memLp_timeMeasure t).eLpNorm_ne_top (hlim t))
      (fun _ ↦ zero_le) fun k ↦ ?_
    simp_rw [B, Finance.simpleHolding_energy_eq_integral_sq (hτ k) t]
    have hKmem (ω : Ω) : Integrable (fun s ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω ^ 2)
        (timeMeasure t) := by
      simp only [Finance.simpleHolding_def]
      exact (memLp_finsetSum _ fun j _ ↦
        (memLp_const (a k j ω)).indicator measurableSet_Ioc.nullMeasurableSet).integrable_sq
    have hHmem : ∀ᵐ ω ∂P, Integrable (fun s ↦ H s ω ^ 2) (timeMeasure t) :=
      hH.locallyBrownianIntegrable.ae_memLp.mono fun ω hω ↦ by
        simpa only [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using (hω t).integrable_sq
    have hBA_sm : AEStronglyMeasurable
        (fun ω ↦ (∫ s, Finance.simpleHolding (τ k) (n k) (a k) s ω ^ 2 ∂timeMeasure t) -
          ∫ s, H s ω ^ 2 ∂timeMeasure t) P :=
      ((((Finance.isStronglyPredictable_simpleHolding (ha k))
        |>.isStronglyPredictable_integral_sq_timeMeasure.isStronglyProgressive.stronglyAdapted t
        |>.mono (ℱ.le t)).sub ((hA_adapt t).mono (ℱ.le t)))).aestronglyMeasurable
    have hdiff_sm : AEStronglyMeasurable (fun p : ℝ≥0 × Ω ↦
        Finance.simpleHolding (τ k) (n k) (a k) p.fst p.snd ^ 2 - H p.fst p.snd ^ 2)
        ((timeMeasure t).prod P) :=
      ((((Finance.isStronglyPredictable_simpleHolding (ha k)).mono
        ℱ.predictable_le_prod).pow 2).sub
        ((hH.isStronglyPredictable.mono ℱ.predictable_le_prod).pow 2)).aestronglyMeasurable
    exact TauCeti.eLpNorm_integral_sub_integral_le_eLpNorm_prod
      (Eventually.of_forall hKmem) hHmem hBA_sm hdiff_sm
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
  have hA_adapt : StronglyAdapted ℱ (fun t ω ↦ ∫ s, H s ω ^ 2 ∂timeMeasure t) :=
    hH.isStronglyPredictable.isStronglyPredictable_integral_sq_timeMeasure
      |>.isStronglyProgressive.stronglyAdapted
  obtain ⟨Z, -, hZI, -, hMZ⟩ := exists_martingale_sq_sub_ae_eq hW hH hI
  exact hMZ.congr (fun t ↦ (hI_adapt t).pow 2 |>.sub (hA_adapt t)) fun t ↦
    (hZI t).mono fun ω hω ↦ by dsimp only; rw [hω]

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
  have hZmul : ∫ ω in A, Z s ω * Z t ω ∂P = ∫ ω in A, Z s ω ^ 2 ∂P := by
    have hAs := hA
    have hZs_sm : StronglyMeasurable[ℱ s] (A.indicator (Z s)) :=
      (hZ.stronglyAdapted s).indicator hAs
    have hmul_int : Integrable (A.indicator (Z s) * Z t) P := by
      have hZs_ind : MemLp (A.indicator (Z s)) 2 P :=
        (hZmem s).indicator (ℱ.le s A hAs).nullMeasurableSet
      exact hZs_ind.integrable_mul (hZmem t)
    have hce : P[A.indicator (Z s) * Z t | ℱ s] =ᵐ[P] A.indicator (Z s) * Z s := by
      have h1 := condExp_mul_of_stronglyMeasurable_left hZs_sm hmul_int (hZ.integrable t)
      exact h1.trans (EventuallyEq.mul EventuallyEq.rfl (hZ.condExp_ae_eq hst))
    have hi : ∫ ω in A, Z s ω * Z t ω ∂P = ∫ ω in A, Z s ω ^ 2 ∂P := by
      have h1 := (integral_condExp (ℱ.le s)).symm.trans (integral_congr_ae hce)
      simp only [Pi.mul_apply, ← Set.indicator_mul_left,
        integral_indicator (ℱ.le s A hAs), ← sq] at h1
      exact h1
    exact hi
  have hMeq := hMZ.setIntegral_eq hst hA
  have hZts : ∫ ω in A, (Z t ω ^ 2 - Z s ω ^ 2) ∂P =
      ∫ ω in A, ((∫ r, H r ω ^ 2 ∂timeMeasure t) - ∫ r, H r ω ^ 2 ∂timeMeasure s) ∂P := by
    have hZt2 : IntegrableOn (fun ω ↦ Z t ω ^ 2) A P := (hZmem t).integrable_sq.integrableOn
    have hZs2 : IntegrableOn (fun ω ↦ Z s ω ^ 2) A P := (hZmem s).integrable_sq.integrableOn
    have hAt : IntegrableOn (fun ω ↦ ∫ r, H r ω ^ 2 ∂timeMeasure t) A P :=
      ((hH.memLp_timeMeasure t).integrable_sq).integral_prod_right.integrableOn
    have hAs : IntegrableOn (fun ω ↦ ∫ r, H r ω ^ 2 ∂timeMeasure s) A P :=
      ((hH.memLp_timeMeasure s).integrable_sq).integral_prod_right.integrableOn
    rw [integral_sub hZt2 hZs2, integral_sub hAt hAs]
    rw [integral_sub hZt2 hAt, integral_sub hZs2 hAs] at hMeq
    linarith
  have hI_Z : ∫ ω in A, (I t ω - I s ω) ^ 2 ∂P = ∫ ω in A, (Z t ω - Z s ω) ^ 2 ∂P :=
    setIntegral_congr_ae (ℱ.le s A hA) <|
      (hZI t).mp <| (hZI s).mono fun ω hωs hωt _ ↦ by rw [hωt, hωs]
  rw [hI_Z]
  have hZt2 : IntegrableOn (fun ω ↦ Z t ω ^ 2) A P := (hZmem t).integrable_sq.integrableOn
  have hZs2 : IntegrableOn (fun ω ↦ Z s ω ^ 2) A P := (hZmem s).integrable_sq.integrableOn
  have hZst : IntegrableOn (fun ω ↦ Z s ω * Z t ω) A P :=
    ((hZmem s).integrable_mul (hZmem t)).integrableOn
  have hsub1 : IntegrableOn (fun ω ↦ Z t ω ^ 2 - Z s ω ^ 2) A P := hZt2.sub hZs2
  have hsub2 : IntegrableOn (fun ω ↦ 2 * (Z s ω * Z t ω - Z s ω ^ 2)) A P :=
    (hZst.sub hZs2).const_mul 2
  have hexp : (fun ω ↦ (Z t ω - Z s ω) ^ 2) =
      fun ω ↦ (Z t ω ^ 2 - Z s ω ^ 2) - 2 * (Z s ω * Z t ω - Z s ω ^ 2) := by
    ext ω; ring
  rw [hexp, integral_sub hsub1 hsub2, integral_const_mul, integral_sub hZst hZs2,
    hZmul, sub_self, mul_zero, sub_zero, hZts]

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

private theorem setIntegral_sq_timeMeasure_sub [SFinite P] (hH : BrownianIntegrable ℱ P H)
    {s t T : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, ((∫ r, H r ω ^ 2 ∂timeMeasure t) - ∫ r, H r ω ^ 2 ∂timeMeasure s) ∂P =
      ∫ p in Ioc s t ×ˢ A, H p.fst p.snd ^ 2 ∂ℱ.predictableMeasure P T := by
  have hA_amb : MeasurableSet A := ℱ.le s A hA
  have hsT : s ≤ T := hst.trans htT
  have hpred : Integrable (fun p : ℝ≥0 × Ω ↦
      (Ioc s t ×ˢ A).indicator (fun p ↦ H p.1 p.2 ^ 2) p) ((timeMeasure T).prod P) :=
    (hH.memLp_timeMeasure T).integrable_sq.indicator (measurableSet_Ioc.prod hA_amb)
  have hsec : ∀ᵐ ω ∂P,
      ((∫ r, H r ω ^ 2 ∂timeMeasure t) - ∫ r, H r ω ^ 2 ∂timeMeasure s) =
        ∫ r, (Ioc s t).indicator (fun r ↦ H r ω ^ 2) r ∂timeMeasure T := by
    filter_upwards [hH.locallyBrownianIntegrable.ae_memLp] with ω hω
    have hH2 (u : ℝ≥0) : Integrable (fun r ↦ H r ω ^ 2) (timeMeasure u) := by
      simpa only [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using (hω u).integrable_sq
    have ht_res : timeMeasure t = (timeMeasure T).restrict (Ioc 0 t) :=
      (timeMeasure_restrict_of_le htT).symm
    have hs_res : timeMeasure s = (timeMeasure T).restrict (Ioc 0 s) :=
      (timeMeasure_restrict_of_le hsT).symm
    have hsplit : Ioc 0 t = Ioc 0 s ∪ Ioc s t :=
      (Ioc_union_Ioc_eq_Ioc bot_le hst).symm
    have hdisj : Disjoint (Ioc 0 s) (Ioc s t) := Ioc_disjoint_Ioc_of_le le_rfl
    rw [ht_res, hs_res, ← integral_indicator measurableSet_Ioc,
      ← integral_indicator measurableSet_Ioc, hsplit,
      indicator_union_of_disjoint hdisj,
      integral_add ((hH2 T).indicator measurableSet_Ioc) ((hH2 T).indicator measurableSet_Ioc),
      add_sub_cancel_left]
  have hI1 : ∫ ω in A, ((∫ r, H r ω ^ 2 ∂timeMeasure t) - ∫ r, H r ω ^ 2 ∂timeMeasure s) ∂P =
      ∫ ω, ∫ r, (Ioc s t ×ˢ A).indicator (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2) (r, ω)
        ∂timeMeasure T ∂P := by
    rw [← integral_indicator hA_amb]
    refine integral_congr_ae (hsec.mono fun ω hω ↦ ?_)
    by_cases hAω : ω ∈ A
    · simp only [indicator_of_mem hAω, hω]
      refine integral_congr_ae (Eventually.of_forall fun r ↦ ?_)
      by_cases hr : r ∈ Ioc s t <;> simp [hr, hAω]
    · simp only [indicator_of_notMem hAω]
      have h0 : (fun r ↦ (Ioc s t ×ˢ A).indicator
          (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2) (r, ω)) = 0 := by
        ext r; simp [hAω]
      simp [h0]
  have hmeas_ind : StronglyMeasurable[ℱ.predictable]
      ((Ioc s t ×ˢ A).indicator (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2)) :=
    (hH.isStronglyPredictable.pow 2).indicator (measurableSet_predictable_Ioc_prod s t hA)
  rw [hI1, ← integral_prod_symm _ hpred,
    ← ℱ.integral_predictableMeasure P hmeas_ind T,
    integral_indicator (measurableSet_predictable_Ioc_prod s t hA)]

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
  rcases le_or_gt s T with hsT | hTs
  · let t' := min t T
    have hst' : s ≤ t' := le_min hst hsT
    have ht'T : t' ≤ T := min_le_right t T
    have hIeq : ∫ ω in A, (I t' ω - I s ω) ^ 2 ∂P =
        ∫ p in Ioc s t' ×ˢ A, H p.1 p.2 ^ 2 ∂ℱ.predictableMeasure P T :=
      (hW.setIntegral_sub_sq_of_isItoIntegral hH hI hst' hA).trans
        (setIntegral_sq_timeMeasure_sub hH hst' ht'T hA)
    have hrect : Ioc s t ×ˢ A ∩ (Ioc 0 T ×ˢ univ) = Ioc s t' ×ˢ A ∩ (Ioc 0 T ×ˢ univ) := by
      ext ⟨r, ω⟩
      simp only [mem_inter_iff, mem_prod, mem_Ioc, mem_univ, and_true, t']
      exact ⟨fun ⟨⟨⟨hsr, hrt⟩, hω⟩, h0r, hrT⟩ ↦
          ⟨⟨⟨hsr, le_min hrt hrT⟩, hω⟩, h0r, hrT⟩,
        fun ⟨⟨⟨hsr, hrt⟩, hω⟩, h0r, hrT⟩ ↦
          ⟨⟨⟨hsr, hrt.trans (min_le_left t T)⟩, hω⟩, h0r, hrT⟩⟩
    have hdens_eq :
        ((ℱ.predictableMeasure P T).withDensity fun p ↦ ‖H p.1 p.2‖ₑ ^ 2) (Ioc s t ×ˢ A) =
          ((ℱ.predictableMeasure P T).withDensity fun p ↦ ‖H p.1 p.2‖ₑ ^ 2) (Ioc s t' ×ˢ A) := by
      rw [withDensity_apply _ (measurableSet_predictable_Ioc_prod s t hA),
        withDensity_apply _ (measurableSet_predictable_Ioc_prod s t' hA),
        ← lintegral_indicator (measurableSet_predictable_Ioc_prod s t hA),
        ← lintegral_indicator (measurableSet_predictable_Ioc_prod s t' hA)]
      refine lintegral_congr_ae ?_
      filter_upwards [ℱ.ae_mem_Ioc_prod_predictableMeasure P T] with p hpT
      by_cases hp : p ∈ Ioc s t ×ˢ A
      · have hp' : p ∈ Ioc s t' ×ˢ A := (Set.ext_iff.mp hrect p |>.mp ⟨hp, hpT⟩).1
        rw [indicator_of_mem hp, indicator_of_mem hp']
      · have hp' : p ∉ Ioc s t' ×ˢ A := fun h ↦ hp (Set.ext_iff.mp hrect p |>.mpr ⟨h, hpT⟩).1
        rw [indicator_of_notMem hp, indicator_of_notMem hp']
    rw [hdens_eq, min_eq_left hsT, hIeq,
      withDensity_apply _ (measurableSet_predictable_Ioc_prod s t' hA)]
    have hpred_nonneg : 0 ≤ᵐ[(ℱ.predictableMeasure P T).restrict (Ioc s t' ×ˢ A)]
        fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2 := Eventually.of_forall fun _ ↦ sq_nonneg _
    have hpred_int : Integrable (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2)
        ((ℱ.predictableMeasure P T).restrict (Ioc s t' ×ˢ A)) :=
      (hH.memLp_predictableMeasure T).integrable_sq.integrableOn
    rw [ofReal_integral_eq_lintegral_ofReal hpred_int hpred_nonneg]
    refine setLIntegral_congr_fun (measurableSet_predictable_Ioc_prod s t' hA) fun p _ ↦ ?_
    rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm]
  · simp only [min_eq_right hTs.le, min_eq_right (hTs.le.trans hst), sub_self,
      zero_pow (by norm_num : 2 ≠ 0), integral_zero, ENNReal.ofReal_zero]
    rw [withDensity_apply _ (measurableSet_predictable_Ioc_prod s t hA),
      ← lintegral_indicator (measurableSet_predictable_Ioc_prod s t hA)]
    refine lintegral_eq_zero_iff' (AEMeasurable.indicator
      ((hH.isStronglyPredictable.measurable.eNorm.pow_const 2).aemeasurable)
      (measurableSet_predictable_Ioc_prod s t hA)) |>.2 ?_
    filter_upwards [ℱ.ae_mem_Ioc_prod_predictableMeasure P T] with p hpT
    have hnot : p ∉ Ioc s t ×ˢ A := fun h ↦ (hTs.trans h.1.1).not_ge hpT.1.2
    simp [indicator_of_notMem hnot]

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
    change (∫⁻ a, ‖Function.uncurry H a‖ₑ ^ 2 ∂ℱ.predictableMeasure P T) < ∞
    rw [← _root_.TauCeti.eLpNorm_two_sq_eq_lintegral
      (hH.memLp_predictableMeasure T).aestronglyMeasurable]
    exact ENNReal.pow_lt_top (hH.memLp_predictableMeasure T).eLpNorm_lt_top
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
