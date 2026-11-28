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
import TauCeti.MeasureTheory.Function.LpSeminorm.SquaredNorm
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
horizon `T` with the terminal `L²` integral `hW.l2Integral T`. Extending
`TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry`, this module establishes:

* `TauCeti.Probability.IsItoIntegral.continuous_toLp` and
  `TauCeti.Probability.IsItoIntegral.tendsto_eLpNorm_sub`: `L²(P)` time continuity of the integral
  process.
* `TauCeti.Probability.IsItoIntegral.integral_eq_zero`: zero expectation at every horizon.
* `TauCeti.Probability.IsFilteredPreBrownianReal.ae_eq_mul_sub_of_isItoIntegral_indicator_Ioc` and
  `indist_mul_sub_of_isItoIntegral_indicator_Ioc`: the `ℱ s`-measurable multiplier rule on `(s, u]`.
* `TauCeti.Probability.IsFilteredPreBrownianReal.ae_eq_wienerIntegral_of_isItoIntegral` and
  `isItoIntegral_iff_ae_eq_wienerIntegral`: identification with the deterministic Wiener integral.
* `TauCeti.Probability.IsFilteredPreBrownianReal.tendsto_measure_exists_le_simpleGains_sub_lt`:
  Doob uniform approximation on `[0, T]` by elementary gains.
* `TauCeti.Probability.IsItoIntegral.martingale_sq_sub`,
  `TauCeti.Probability.IsItoIntegral.setIntegral_sub_sq`,
  `TauCeti.Probability.IsItoIntegral.condExp_sub_sq`,
  `TauCeti.Probability.IsFilteredPreBrownianReal.withDensity_sq_predictableMeasure_Ioc_prod`, and
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

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W H I : ℝ≥0 → Ω → ℝ}

/-! ### `L²(P)` continuity, zero expectation, and multiplier rule -/

namespace IsItoIntegral

/-- **`L²(P)` time continuity**: the `L²(P)` class `t ↦ (hI.memLp hW hH t).toLp (I t)` of a
continuous Itô integral of a `BrownianIntegrable` integrand varies continuously in `t`, without
assuming path continuity of `W`. -/
theorem continuous_toLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) :
    Continuous fun t : ℝ≥0 ↦ (hI.memLp hW hH t).toLp (I t) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine continuous_iff_continuousAt.2 fun t₀ ↦ tendsto_iff_edist_tendsto_0.2 ?_
  have hne_fst : ∀ᵐ t ∂timeMeasure (t₀ + 1), t ≠ t₀ := by
    simp only [ae_iff, ne_eq, not_not, ofPred_eq_eq_singleton,
      timeMeasure_apply _ (measurableSet_singleton t₀)]
    by_cases h0 : t₀ ∈ Ioc 0 (t₀ + 1) <;> simp [h0]
  have hne : ∀ᵐ p ∂(timeMeasure (t₀ + 1)).prod P, p.1 ≠ t₀ :=
    (Measure.quasiMeasurePreserving_fst (μ := timeMeasure (t₀ + 1)) (ν := P)).ae hne_fst
  have hlim : Tendsto (fun t ↦ eLpNorm
      (fun p : ℝ≥0 × Ω ↦ (uIoc t₀ t).indicator (H · p.2) p.1 - 0) 2
        ((timeMeasure (t₀ + 1)).prod P)) (𝓝 t₀) (𝓝 0) := by
    refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
      (.of_forall fun t ↦ (hH.memLp_timeMeasure (t₀ + 1)).aestronglyMeasurable.indicator
        ((measurableSet_uIoc (a := t₀) (b := t)).prod MeasurableSet.univ) |>.congr
          (.of_forall fun p ↦ by
            by_cases hp : p.1 ∈ uIoc t₀ t <;> simp [Function.uncurry_def, hp]))
      (hH.memLp_timeMeasure (t₀ + 1))
      (.of_forall fun t ↦ .of_forall fun p ↦ by
        simpa only [Pi.zero_apply, sub_zero, ENNReal.coe_one, one_mul, Function.uncurry_def] using
          eNorm_indicator_le_eNorm_self (H · p.2) p.1)
      (hne.mono fun p hp ↦ tendsto_const_nhds.congr' <| by
        rcases lt_or_gt_of_ne hp with hlt | hgt
        · filter_upwards [eventually_gt_nhds hlt] with t ht
          rw [Set.indicator_of_notMem (by simp [Set.mem_uIoc, hlt.not_gt, ht.not_gt])]
        · filter_upwards [eventually_lt_nhds hgt] with t ht
          rw [Set.indicator_of_notMem (by simp [Set.mem_uIoc, hgt.not_ge, ht.not_ge])])
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (.of_forall fun _ ↦ zero_le)
    (Eventually.mono (Iio_mem_nhds (lt_add_one t₀)) fun t (ht : t < t₀ + 1) ↦ ?_)
  rw [Lp.edist_toLp_toLp]
  simp only [sub_zero]
  rcases le_total t₀ t with hle | hle
  · rw [hI.eLpNorm_sub_eq hW hH hle, uIoc_of_le hle]
    exact eLpNorm_mono_measure _ (Measure.prod_mono (timeMeasure_mono ht.le) le_rfl)
  · rw [← eLpNorm_neg, neg_sub, hI.eLpNorm_sub_eq hW hH hle, uIoc_of_ge hle]
    exact eLpNorm_mono_measure _ (Measure.prod_mono (timeMeasure_mono le_self_add) le_rfl)

/-- Every continuous Itô integral of a `BrownianIntegrable` integrand has expectation zero at every
horizon, without assuming path continuity of `W` or adaptation of `I`. -/
theorem integral_eq_zero (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    ∫ ω, I T ω ∂P = 0 :=
  (integral_congr_ae (hI.ae_eq_l2Integral hW hH T)).trans (hW.integral_l2Integral T _)

end IsItoIntegral

/-- **L² time continuity of the Itô integral.** Against a pre-Brownian motion, every Itô integral
of a Brownian-integrable integrand is continuous in `L²(P)` as a function of time. -/
theorem IsItoIntegral.tendsto_eLpNorm_sub (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    Tendsto (fun s ↦ eLpNorm (I s - I t) 2 P) (𝓝 t) (𝓝 0) := by
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp
    ((IsItoIntegral.continuous_toLp hW hH hI).continuousAt (x := t)).tendsto
  exact h.congr fun s ↦ eLpNorm_congr_ae
    ((hI.memLp hW hH s).coeFn_toLp.sub (hI.memLp hW hH t).coeFn_toLp)

/-- **Multiplier rule on `(s, u]` (fixed-time `L²` form).** For a square-integrable
`ℱ s`-measurable random variable `ξ` (in particular any bounded `ℱ s`-measurable random variable),
any Itô integral of `(Ioc s u).indicator (fun _ ↦ ξ ω)` agrees almost surely at each time `t`
with `ξ * (W (min u t) - W (min s t))`. Path continuity of `W` is not required. -/
theorem IsFilteredPreBrownianReal.ae_eq_mul_sub_of_isItoIntegral_indicator_Ioc
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {s u : ℝ≥0} (hsu : s ≤ u) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ)
    (hξ₂ : MemLp ξ 2 P)
    (hI : IsItoIntegral ℱ P W (fun t ω ↦ (Ioc s u).indicator (fun _ ↦ ξ ω) t) I) (t : ℝ≥0) :
    I t =ᵐ[P] fun ω ↦ ξ ω * (W (min u t) ω - W (min s t) ω) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hbi := TauCeti.brownianIntegrable_indicator_Ioc hξ hξ₂ (ℱ := ℱ) (P := P) (s := s) (u := u)
  have hL := (hI.ae_eq_l2Integral hW hbi t).trans
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
theorem IsFilteredPreBrownianReal.indist_mul_sub_of_isItoIntegral_indicator_Ioc
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω) {s u : ℝ≥0} (hsu : s ≤ u) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ)
    (hI : IsItoIntegral ℱ P W (fun t ω ↦ (Ioc s u).indicator (fun _ ↦ ξ ω) t) I) :
    I ≡ᵐ[P] fun t ω ↦ ξ ω * (W (min u t) ω - W (min s t) ω) :=
  isItoIntegral_unique hW hI (IsItoIntegral.indicator_Ioc hsu hWc hξ)

/-! ### Deterministic bridge and Doob uniform approximation -/

/-- **Deterministic L² bridge.** For a measurable deterministic integrand `h` in `L²` on every
finite horizon, any Itô integral agrees almost surely at each horizon `T` with the Wiener
integral of `h`. -/
theorem IsFilteredPreBrownianReal.ae_eq_wienerIntegral_of_isItoIntegral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {h : ℝ≥0 → ℝ} (hm : Measurable h) (hLp : ∀ T : ℝ≥0, MemLp h 2 (timeMeasure T))
    (hI : IsItoIntegral ℱ P W (fun t _ ↦ h t) I) (T : ℝ≥0) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    I T =ᵐ[P] hW.toIsPreBrownianReal.wienerIntegral T ((hLp T).toLp h) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let hbi := TauCeti.brownianIntegrable_fst (ℱ := ℱ) (P := P) hm hLp
  refine (hI.ae_eq_l2Integral hW hbi T).trans ?_
  rw [hW.l2Integral_uncurry_eq_wienerIntegral T (hLp T) (hbi.memLp_predictableMeasure T)]

/-- **Deterministic L² characterization.** For a measurable deterministic integrand `h` in `L²` on
every finite horizon, an almost surely continuous process `I` is an Itô integral of `h` if and
only if `I T` agrees almost surely with the Wiener integral of `h` at every horizon `T`. -/
theorem IsFilteredPreBrownianReal.isItoIntegral_iff_ae_eq_wienerIntegral
    (hW : IsFilteredPreBrownianReal ℱ W P)
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
theorem IsFilteredPreBrownianReal.tendsto_measure_exists_le_simpleGains_sub_lt
    (hW : IsFilteredPreBrownianReal ℱ W P)
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
    simpa only [Function.uncurry_def, Pi.sub_def] using
      (hJI.eLpNorm_simpleGains_sub_eq hW hH (hτ k) (ha k) (ha₂ k) T).symm
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
    (hZL t).trans (hI.ae_eq_l2Integral hW hH t).symm
  let B (k : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    ∑ j ∈ Finset.range (n k), a k j ω ^ 2 * (↑(min (τ k (j + 1)) t) - ↑(min (τ k j) t))
  -- Pass the elementary square-compensated martingales `M_k^2 - B_k` to the limit in `L¹(P)`.
  refine ⟨Z, hZ, hIZ, hZmem, martingale_of_tendsto_eLpNorm_one
    (fun k ↦ hW.martingale_sq_simpleGains_sub (hτ k) (ha k) (ha₂ k))
    (fun t ↦ (hZ.stronglyAdapted t).pow 2 |>.sub
      (hH.isStronglyPredictable.stronglyAdapted_integral_sq_timeMeasure t)) fun t ↦ ?_⟩
  have hsq_lim : Tendsto (fun k ↦ eLpNorm
      (fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - Z t ω ^ 2) 1 P) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, sq_abs] using tendsto_eLpNorm_norm_sq_sub (hZmem t) (hZlim t)
  -- Control `‖B_k t - ∫ H^2‖₁` by the `L¹` product-norm difference of the squared integrands.
  have henergy_lim : Tendsto (fun k ↦ eLpNorm
      (fun ω ↦ B k t ω - ∫ s, H s ω ^ 2 ∂timeMeasure t) 1 P) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [Real.norm_eq_abs, sq_abs] using
        tendsto_eLpNorm_norm_sq_sub (hH.memLp_timeMeasure t) (hlim t))
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
theorem IsItoIntegral.martingale_sq_sub (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
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
theorem IsItoIntegral.setIntegral_sub_sq (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
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
theorem IsItoIntegral.condExp_sub_sq (hI : IsItoIntegral ℱ P W H I)
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
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
  exact (hI.setIntegral_sub_sq hW hH hst hA).symm

/-- **Finite-horizon predictable measure on predictable rectangles.** For any Itô integral `I`
of a Brownian-integrable integrand `H` and any `T : ℝ≥0`, the squared-integrand measure
`(ℱ.predictableMeasure P T).withDensity (fun p ↦ ‖H p.1 p.2‖ₑ ^ 2)` assigns to every
predictable rectangle `Ioc s t ×ˢ A` (`s ≤ t`, `A ∈ ℱ s`) the value
`ENNReal.ofReal (∫ ω in A, (I (min t T) ω - I (min s T) ω) ^ 2 ∂P)`. -/
theorem IsFilteredPreBrownianReal.withDensity_sq_predictableMeasure_Ioc_prod
    (hW : IsFilteredPreBrownianReal ℱ W P)
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
      (hI.setIntegral_sub_sq hW hH hst' hA).trans
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
theorem IsFilteredPreBrownianReal.eq_withDensity_sq_predictableMeasure_of_Ioc_prod
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

end TauCeti.Probability
