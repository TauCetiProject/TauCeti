/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.Stopping
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Probability.BrownianMotion.Integral.Elementary
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Associativity
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Martingale.CountableStopping
import TauCeti.Probability.Process.Stopping
import TauCeti.Probability.Process.StoppingApproximation

/-!
# The continuous Brownian Itô integral on the expected square-energy domain

For a predictable integrand `H` in `TauCeti.BrownianIntegrable ℱ P H`, this module constructs a
predictable continuous martingale `I` satisfying `TauCeti.IsItoIntegral ℱ P W H I` whenever `W` is
a filtered pre-Brownian motion with almost-surely continuous paths, and establishes the `L²`
isometry, martingale property, and optional stopping identity for arbitrary continuous Itô
integrals of `H`.

Except for `BrownianIntegrable.exists_isItoIntegral`, which selects a continuous representative
from elementary Brownian gains and therefore uses sample-path continuity of `W`, all properties of
a given Itô integral (`memLp`, `eLpNorm_eq`, `integral_sq`, `martingale`, `stoppedProcess`, and
`stoppedProcess_indist`) hold for any `IsFilteredPreBrownianReal ℱ W P` on a raw filtration without
assuming path continuity of `W`, completeness, or right continuity of `ℱ`.

## Main results

* `TauCeti.BrownianIntegrable.exists_isItoIntegral`: existence of a predictable continuous
  martingale Itô integral for `BrownianIntegrable` integrands.
* `TauCeti.IsItoIntegral.memLp`, `eLpNorm_eq`, `integral_sq`: square integrability and the Itô
  isometry at every finite horizon.
* `TauCeti.IsItoIntegral.martingale`: every adapted continuous Itô integral of a
  `BrownianIntegrable` integrand is a true martingale.
* `TauCeti.IsItoIntegral.stoppedProcess`, `stoppedProcess_indist`: stopping a continuous Itô
  integral at an arbitrary stopping time `τ` yields a continuous Itô integral of the cutoff
  integrand `H · 1_{[0, τ]}`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti

/-! ### Elementary `L²` isometry at arbitrary observation times -/

namespace Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}

/-- Elementary Brownian gains with square-integrable left-measurable heights belong to `L²(P)` at
every observation time `T`. -/
theorem memLp_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) (T : ℝ≥0) :
    MemLp (Finance.simpleGains τ n a W T) 2 P := by
  have heq : Finance.simpleGains τ n a W T =
      fun ω ↦ ∑ i ∈ range n, a i ω * (W (min (τ (i + 1)) T) ω - W (min (τ i) T) ω) := by
    ext ω
    exact Finance.simpleGains_def τ n a W T ω
  rw [heq]
  exact hW.memLp_sum_mul_sub_min (range n)
    (fun i hi ↦ hτ (Finset.mem_range.mp hi).le (Finset.mem_range.mp hi) (Nat.le_succ i))
    (fun i hi ↦ ha i (Finset.mem_range.mp hi))
    (fun i hi ↦ ha₂ i (Finset.mem_range.mp hi)) T

/-- Lower-integral form of the elementary Brownian isometry at an arbitrary observation time `T`. -/
theorem lintegral_enorm_sq_simpleGains_timeMeasure (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) (T : ℝ≥0) :
    ∫⁻ ω, ‖Finance.simpleGains τ n a W T ω‖ₑ ^ 2 ∂P =
      ∫⁻ p, ‖Finance.simpleHolding τ n a p.1 p.2‖ₑ ^ 2
        ∂(Probability.timeMeasure T).prod P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hm : Measurable (fun p : ℝ≥0 × Ω ↦ ‖Finance.simpleHolding τ n a p.1 p.2‖ₑ ^ 2) :=
    ((Finance.isStronglyPredictable_simpleHolding ha).mono ℱ.predictable_le_prod).measurable.eNorm
      |>.pow_const 2
  rw [lintegral_prod_symm _ hm.aemeasurable]
  simp_rw [Finance.lintegral_enorm_sq_simpleHolding_timeMeasure hτ, Real.enorm_sq_eq_ofReal_sq]
  have hsum := hW.memLp_simpleGains hτ ha ha₂ T
  have hdisj : ((Finset.range n : Finset ℕ) : Set ℕ).Pairwise
      fun i j ↦ τ (i + 1) ≤ τ j ∨ τ (j + 1) ≤ τ i := by
    intro i hi j hj hij
    rcases hij.lt_or_gt with h | h
    · exact Or.inl (hτ (Finset.mem_range.mp hi) (Finset.mem_range.mp hj).le h)
    · exact Or.inr (hτ (Finset.mem_range.mp hj) (Finset.mem_range.mp hi).le h)
  have hmeas (i : ℕ) (hi : i < n) : Measurable (fun ω ↦ ENNReal.ofReal (a i ω ^ 2)) :=
    (((ha i hi).mono (ℱ.le _)).measurable.pow_const 2).ennreal_ofReal
  rw [← ofReal_integral_eq_lintegral_ofReal hsum.integrable_sq (ae_of_all _ fun _ ↦ sq_nonneg _)]
  simp_rw [Finance.simpleGains_def]
  rw [hW.integral_sq_sum_mul_sub_min (range n)
      (fun i hi ↦ hτ (Finset.mem_range.mp hi).le (Finset.mem_range.mp hi) (Nat.le_succ i)) hdisj
      (fun i hi ↦ ha i (Finset.mem_range.mp hi))
      (fun i hi ↦ ha₂ i (Finset.mem_range.mp hi)) T,
    lintegral_finsetSum _ (fun i hi ↦ (hmeas i (Finset.mem_range.mp hi)).mul_const _),
    ENNReal.ofReal_sum_of_nonneg (fun i hi ↦ mul_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)
      (sub_nonneg.mpr (NNReal.coe_le_coe.mpr
        (min_le_min_right T
          (hτ (Finset.mem_range.mp hi).le (Finset.mem_range.mp hi) (Nat.le_succ i))))))]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  have hlen : ENNReal.ofReal (((min (τ (i + 1)) T : ℝ≥0) : ℝ) - ((min (τ i) T : ℝ≥0) : ℝ)) =
      ENNReal.ofReal (((min (τ (i + 1)) T : ℝ≥0) : ℝ) - (τ i : ℝ)) := by
    by_cases hle : τ i ≤ T
    · rw [min_eq_left hle]
    · have hgt : T ≤ τ i := le_of_not_ge hle
      have hgt' : T ≤ τ (i + 1) := hgt.trans (hτ hi'.le hi' (Nat.le_succ i))
      have hnonpos : (T : ℝ) - τ i ≤ 0 := sub_nonpos.mpr (NNReal.coe_le_coe.mpr hgt)
      rw [min_eq_right hgt, min_eq_right hgt', sub_self, ENNReal.ofReal_zero,
        ENNReal.ofReal_eq_zero.mpr hnonpos]
  rw [lintegral_mul_const _ (hmeas i hi'),
    ← ofReal_integral_eq_lintegral_ofReal (ha₂ i hi').integrable_sq
      (ae_of_all _ fun _ ↦ sq_nonneg _),
    ENNReal.ofReal_mul (integral_nonneg fun _ ↦ sq_nonneg _), Nat.succ_eq_add_one, hlen]

/-- `L²`-seminorm form of the elementary Brownian isometry at an arbitrary observation time `T`. -/
theorem eLpNorm_simpleGains_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) (T : ℝ≥0) :
    eLpNorm (Finance.simpleGains τ n a W T) 2 P =
      eLpNorm (Function.uncurry (Finance.simpleHolding τ n a)) 2
        ((Probability.timeMeasure T).prod P) := by
  have hg : AEStronglyMeasurable (Finance.simpleGains τ n a W T) P :=
    (hW.memLp_simpleGains hτ ha ha₂ T).aestronglyMeasurable
  have hh : AEStronglyMeasurable (Function.uncurry (Finance.simpleHolding τ n a))
      ((Probability.timeMeasure T).prod P) :=
    ((Finance.isStronglyPredictable_simpleHolding ha).mono ℱ.predictable_le_prod)
      |>.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hg,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hh]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, Function.uncurry_def,
    hW.lintegral_enorm_sq_simpleGains_timeMeasure hτ ha ha₂ T]

end Probability.IsFilteredPreBrownianReal

/-! ### Expected-energy helpers and `L²` martingale completion -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H I J : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-- `BrownianIntegrable` expressed with `Probability.timeMeasure T`. -/
theorem BrownianIntegrable.memLp_timeMeasure (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    MemLp (Function.uncurry H) 2 ((Probability.timeMeasure T).prod P) := by
  simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using hH.memLp T

/-- Convergence of predictable integrands in `L²((timeMeasure T).prod P)` implies convergence of
their pathwise square energies on `(0, T]` in `P`-measure. -/
theorem tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm [IsFiniteMeasure P]
    {F : ℕ → ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    (hF : ∀ k, IsStronglyPredictable ℱ (F k)) (hH : IsStronglyPredictable ℱ H)
    (hlim : Tendsto (fun k ↦ eLpNorm (fun p ↦ F k p.1 p.2 - H p.1 p.2) 2
      ((Probability.timeMeasure T).prod P)) atTop (𝓝 0))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖F k s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure T}) atTop (𝓝 0) := by
  let δ : ℝ≥0∞ := min ε 1
  have hδ0 : δ ≠ 0 := (lt_min hε zero_lt_one).ne'
  have hδ_top : δ ≠ ∞ := (min_le_right ε 1).trans_lt ENNReal.one_lt_top |>.ne
  let E (k : ℕ) (ω : Ω) : ℝ≥0∞ := ∫⁻ s, ‖F k s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure T
  have hm (k : ℕ) : Measurable (fun p : ℝ≥0 × Ω ↦ ‖F k p.1 p.2 - H p.1 p.2‖ₑ ^ 2) :=
    (((hF k).sub hH).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2
  have hmean (k : ℕ) : ∫⁻ ω, E k ω ∂P =
      eLpNorm (fun p ↦ F k p.1 p.2 - H p.1 p.2) 2 ((Probability.timeMeasure T).prod P) ^ 2 := by
    rw [← lintegral_prod_symm _ (hm k).aemeasurable]
    have hpow := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      (((hF k).sub hH).mono ℱ.predictable_le_prod).aestronglyMeasurable
      (μ := (Probability.timeMeasure T).prod P)
    simpa only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat, Function.uncurry_def,
      Pi.sub_def] using hpow.symm
  have hEm (k : ℕ) : Measurable (E k) := (hm k).lintegral_prod_left'
  have hbound (k : ℕ) : P {ω | ε ≤ E k ω} ≤ δ⁻¹ * ∫⁻ ω, E k ω ∂P := by
    have hsub : {ω | ε ≤ E k ω} ⊆ {ω | δ ≤ E k ω} := fun _ hω ↦ (min_le_left ε 1).trans hω
    refine (measure_mono hsub).trans ?_
    have hmarkov := mul_meas_ge_le_lintegral₀ (μ := P) (hEm k).aemeasurable δ
    calc
      P {ω | δ ≤ E k ω} = δ⁻¹ * (δ * P {ω | δ ≤ E k ω}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hδ0 hδ_top, one_mul]
      _ ≤ δ⁻¹ * ∫⁻ ω, E k ω ∂P := by gcongr
  have hzero : Tendsto (fun k ↦ δ⁻¹ * ∫⁻ ω, E k ω ∂P) atTop (𝓝 0) := by
    simp_rw [hmean]
    have hsq : Tendsto (fun k ↦ eLpNorm (fun p ↦ F k p.1 p.2 - H p.1 p.2) 2
        ((Probability.timeMeasure T).prod P) ^ 2) atTop (𝓝 0) := by
      simpa [Function.comp_def] using ((ENNReal.continuous_pow 2).tendsto 0).comp hlim
    simpa using ENNReal.Tendsto.const_mul hsq (Or.inr (ENNReal.inv_ne_top.mpr hδ0))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
    (fun _ ↦ zero_le) hbound

private theorem eLpNorm_simpleGains_sub_eq
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    {n₁ n₂ : ℕ} {τ₁ τ₂ : ℕ → ℝ≥0} {a₁ a₂ : ℕ → Ω → ℝ} {C₁ C₂ : ℝ}
    (hτ₁ : MonotoneOn τ₁ (Iic n₁)) (hτ₂ : MonotoneOn τ₂ (Iic n₂))
    (ha₁ : ∀ i < n₁, StronglyMeasurable[ℱ (τ₁ i)] (a₁ i))
    (ha₂ : ∀ j < n₂, StronglyMeasurable[ℱ (τ₂ j)] (a₂ j))
    (hb₁ : ∀ i < n₁, ∀ ω, ‖a₁ i ω‖ ≤ C₁) (hb₂ : ∀ j < n₂, ∀ ω, ‖a₂ j ω‖ ≤ C₂) (T : ℝ≥0) :
    eLpNorm (Finance.simpleGains τ₁ n₁ a₁ W T - Finance.simpleGains τ₂ n₂ a₂ W T) 2 P =
      eLpNorm (fun p ↦ Finance.simpleHolding τ₁ n₁ a₁ p.1 p.2 -
        Finance.simpleHolding τ₂ n₂ a₂ p.1 p.2) 2 ((Probability.timeMeasure T).prod P) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, b, -, hτ, hbm, hbb, hhold, hgains⟩ :=
    Finance.exists_simpleHolding_simpleGains_sub ℱ hτ₁ hτ₂ ha₁ ha₂
  have hb₂' (j : ℕ) (hj : j < n) : MemLp (b j) 2 P := by
    refine (memLp_const (n₁ * C₁ + n₂ * C₂)).mono'
      ((hbm j hj).mono (ℱ.le _)).aestronglyMeasurable (.of_forall fun ω ↦ (hbb j hj ω).trans ?_)
    have h1 : (∑ i ∈ range n₁, ‖a₁ i ω‖) ≤ n₁ * C₁ := by
      simpa using sum_le_card_nsmul (range n₁) (fun i ↦ ‖a₁ i ω‖) C₁
        (fun i hi ↦ hb₁ i (Finset.mem_range.mp hi) ω)
    have h2 : (∑ i ∈ range n₂, ‖a₂ i ω‖) ≤ n₂ * C₂ := by
      simpa using sum_le_card_nsmul (range n₂) (fun i ↦ ‖a₂ i ω‖) C₂
        (fun i hi ↦ hb₂ i (Finset.mem_range.mp hi) ω)
    exact add_le_add h1 h2
  have hgain_eq : Finance.simpleGains τ₁ n₁ a₁ W T - Finance.simpleGains τ₂ n₂ a₂ W T =
      Finance.simpleGains τ n b W T := by
    ext ω
    exact (hgains W T ω).symm
  have hhold_eq : (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding τ₁ n₁ a₁ p.1 p.2 -
      Finance.simpleHolding τ₂ n₂ a₂ p.1 p.2) =
      Function.uncurry (Finance.simpleHolding τ n b) := by
    ext ⟨t, ω⟩
    exact (hhold t ω).symm
  rw [hgain_eq, hhold_eq]
  exact hW.eLpNorm_simpleGains_eq hτ.monotoneOn hbm hb₂' T

private theorem cauchySeq_simpleGains_toLp
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    {n : ℕ → ℕ} {τ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ} {C : ℕ → ℝ}
    (hτ : ∀ m, MonotoneOn (τ m) (Iic (n m)))
    (ha : ∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j))
    (hb : ∀ m j, j < n m → ∀ ω, ‖a m j ω‖ ≤ C m)
    (herr : ∀ T, Tendsto (fun m ↦ eLpNorm
      (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
        ((Probability.timeMeasure T).prod P)) atTop (𝓝 0))
    (hmem : ∀ m T, MemLp (Finance.simpleGains (τ m) (n m) (a m) W T) 2 P) (T : ℝ≥0) :
    CauchySeq (fun m ↦ (hmem m T).toLp (Finance.simpleGains (τ m) (n m) (a m) W T)) := by
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  have hhalf : (0 : ℝ≥0∞) < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((herr T).eventually (gt_mem_nhds hhalf))
  refine ⟨N, fun m hm m' hm' ↦ ?_⟩
  rw [Lp.edist_toLp_toLp,
    eLpNorm_simpleGains_sub_eq hW (hτ m) (hτ m') (ha m) (ha m') (hb m) (hb m') T]
  let f (k : ℕ) (p : ℝ≥0 × Ω) : ℝ := Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2
  have hsub : (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 -
      Finance.simpleHolding (τ m') (n m') (a m') p.1 p.2) = f m - f m' := by
    ext p
    simp [f, sub_sub_sub_cancel_right]
  rw [hsub]
  exact (eLpNorm_sub_le (by norm_num)).trans_lt
    ((ENNReal.add_lt_add (hN m hm) (hN m' hm')).trans_eq (ENNReal.add_halves ε))

private theorem exists_martingale_l2
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) :
    ∃ (Z : ℝ≥0 → Ω → ℝ) (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      Martingale Z ℱ P ∧
      (∀ m, StrictMonoOn (τ m) (Iic (n m))) ∧
      (∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j)) ∧
      (∀ m j, j < n m → ∀ ω, ‖a m j ω‖ ≤ C m) ∧
      (∀ T, Tendsto (fun m ↦ eLpNorm
        (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
          ((Probability.timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      ∀ T, MemLp (Z T) 2 P ∧
        eLpNorm (Z T) 2 P =
          eLpNorm (Function.uncurry H) 2 ((Probability.timeMeasure T).prod P) ∧
        Tendsto (fun m ↦ eLpNorm (Finance.simpleGains (τ m) (n m) (a m) W T - Z T) 2 P)
          atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    (memLp_const (C m)).mono' ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable
      (.of_forall (hb m j hj))
  have hMm (m : ℕ) : Martingale (Finance.simpleGains (τ m) (n m) (a m) W) ℱ P :=
    hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, .of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hb m j hj ω⟩
  have hmem (m : ℕ) (T : ℝ≥0) : MemLp (Finance.simpleGains (τ m) (n m) (a m) W T) 2 P :=
    hW.memLp_simpleGains (hτ m).monotoneOn (ha m) (ha₂ m) T
  obtain ⟨Z, hZm, hZlim⟩ := exists_martingale_of_cauchySeq_Lp hMm hmem
    (cauchySeq_simpleGains_toLp hW (fun m ↦ (hτ m).monotoneOn) ha hb herr hmem)
  refine ⟨Z, n, τ, a, C, hZm, hτ, ha, hb, herr, fun T ↦ ⟨(hZlim T).1, ?_, (hZlim T).2⟩⟩
  have hh_mem (m : ℕ) : MemLp (Function.uncurry (Finance.simpleHolding (τ m) (n m) (a m))) 2
      ((Probability.timeMeasure T).prod P) := by
    rw [memLp_iff, ← hW.eLpNorm_simpleGains_eq (hτ m).monotoneOn (ha m) (ha₂ m) T]
    exact (hmem m T).eLpNorm_lt_top
  have hLp1 : Tendsto (fun m ↦ (hmem m T).toLp (Finance.simpleGains (τ m) (n m) (a m) W T))
      atTop (𝓝 ((hZlim T).1.toLp (Z T))) := by
    rw [tendsto_iff_edist_tendsto_0]
    simpa only [Lp.edist_toLp_toLp] using (hZlim T).2
  have hLp2 : Tendsto
      (fun m ↦ (hh_mem m).toLp (Function.uncurry (Finance.simpleHolding (τ m) (n m) (a m))))
      atTop (𝓝 ((hH.memLp_timeMeasure T).toLp (Function.uncurry H))) := by
    rw [tendsto_iff_edist_tendsto_0]
    simpa only [Lp.edist_toLp_toLp, Function.uncurry_def, Pi.sub_def] using herr T
  have hnorm_eq (m : ℕ) :
      ‖(hmem m T).toLp (Finance.simpleGains (τ m) (n m) (a m) W T)‖ =
        ‖(hh_mem m).toLp (Function.uncurry (Finance.simpleHolding (τ m) (n m) (a m)))‖ := by
    simp only [Lp.norm_toLp, hW.eLpNorm_simpleGains_eq (hτ m).monotoneOn (ha m) (ha₂ m) T]
  have hlim := tendsto_nhds_unique hLp1.norm (by simpa only [hnorm_eq] using hLp2.norm)
  have hreal : (eLpNorm (Z T) 2 P).toReal =
      (eLpNorm (Function.uncurry H) 2 ((Probability.timeMeasure T).prod P)).toReal := by
    simpa only [Lp.norm_toLp] using hlim
  exact (ENNReal.toReal_eq_toReal_iff' (hZlim T).1.eLpNorm_lt_top.ne
    (hH.memLp_timeMeasure T).eLpNorm_lt_top.ne).mp hreal

/-! ### Existence, `L²` isometry, and martingale property -/

/-- **Existence of the continuous `L²` Brownian Itô integral**: every `BrownianIntegrable`
integrand against a filtered pre-Brownian motion with almost-surely continuous paths admits a
predictable continuous martingale Itô integral on the raw filtration. -/
theorem BrownianIntegrable.exists_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      Martingale I ℱ P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    (memLp_const (C m)).mono' ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable
      (.of_forall (hb m j hj))
  have hMm (m : ℕ) : Martingale (Finance.simpleGains (τ m) (n m) (a m) W) ℱ P :=
    hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, .of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hb m j hj ω⟩
  have hcm (m : ℕ) : ∀ᵐ ω ∂P, Continuous (fun t ↦ Finance.simpleGains (τ m) (n m) (a m) W t ω) := by
    filter_upwards [hcont] with ω hω
    simp only [Finance.simpleGains_def]
    fun_prop
  have hmem (m : ℕ) (T : ℝ≥0) : MemLp (Finance.simpleGains (τ m) (n m) (a m) W T) 2 P :=
    hW.memLp_simpleGains (hτ m).monotoneOn (ha m) (ha₂ m) T
  obtain ⟨I, hIm, hIp, hIlim, -, _φ, -, hIpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp hMm hcm hmem
      (cauchySeq_simpleGains_toLp hW (fun m ↦ (hτ m).monotoneOn) ha hb herr hmem)
  refine ⟨I, ⟨hH.isStronglyPredictable, ?_, fun t ↦ ?_⟩, hIp, hIm⟩
  · filter_upwards [hIpath] with _ h
    exact h.1
  · refine ⟨n, τ, a, fun m ↦ (hτ m).monotoneOn, ha, fun m j hj ↦ ⟨C m, hb m j hj⟩, ?_, ?_⟩
    · exact tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
        (fun m ↦ Finance.isStronglyPredictable_simpleHolding (ha m))
        hH.isStronglyPredictable (herr t)
    · exact tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (hIlim t).2

namespace IsItoIntegral

private theorem ae_eq_of_l2_approx
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H)
    (hI : IsItoIntegral ℱ P W H I) {Z : ℝ≥0 → Ω → ℝ}
    {n : ℕ → ℕ} {τ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (hτ : ∀ m, MonotoneOn (τ m) (Iic (n m)))
    (ha : ∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j))
    (herr : ∀ T, Tendsto (fun m ↦ eLpNorm
      (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
        ((Probability.timeMeasure T).prod P)) atTop (𝓝 0))
    (hZ : ∀ T, Tendsto (fun m ↦ eLpNorm (Finance.simpleGains (τ m) (n m) (a m) W T - Z T) 2 P)
      atTop (𝓝 0)) (T : ℝ≥0) :
    I T =ᵐ[P] Z T := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact hI.ae_eq_of_approx hW hτ ha
    (tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
      (fun m ↦ Finance.isStronglyPredictable_simpleHolding (ha m))
      hH.isStronglyPredictable (herr T))
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (hZ T))

/-- Every continuous Itô integral of a `BrownianIntegrable` integrand belongs to `L²(P)` at each
finite horizon, without assuming path continuity of `W`. -/
theorem memLp (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    MemLp (I T) 2 P := by
  obtain ⟨Z, n, τ, a, -, -, hτ, ha, -, herr, hZ⟩ := exists_martingale_l2 hW hH
  exact (hZ T).1.ae_eq (hI.ae_eq_of_l2_approx hW hH (fun m ↦ (hτ m).monotoneOn) ha herr
    (fun t ↦ (hZ t).2.2) T).symm

/-- **`L²`-seminorm Itô isometry**: at every finite horizon `T`, the `L²(P)` seminorm of `I T`
equals the `L²((timeMeasure T).prod P)` seminorm of `H`. -/
theorem eLpNorm_eq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    eLpNorm (I T) 2 P =
      eLpNorm (Function.uncurry H) 2 ((Probability.timeMeasure T).prod P) := by
  obtain ⟨Z, n, τ, a, -, -, hτ, ha, -, herr, hZ⟩ := exists_martingale_l2 hW hH
  exact (eLpNorm_congr_ae (hI.ae_eq_of_l2_approx hW hH (fun m ↦ (hτ m).monotoneOn) ha herr
    (fun t ↦ (hZ t).2.2) T)).trans (hZ T).2.1

/-- **Bochner-integral Itô isometry**: at every finite horizon `T`,
`E[(I T)²] = E[∫_{(0, T]} H²]`. -/
theorem integral_sq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    ∫ ω, I T ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(Probability.timeMeasure T).prod P := by
  have h1 := (hI.memLp hW hH T).norm_toLp_sq
  have h2 := (hH.memLp_timeMeasure T).norm_toLp_sq
  simp only [Lp.norm_toLp, Real.norm_eq_abs, sq_abs] at h1 h2
  change ∫ ω, I T ω ^ 2 ∂P = ∫ p, Function.uncurry H p ^ 2 ∂(Probability.timeMeasure T).prod P
  rw [← h1, ← h2, hI.eLpNorm_eq hW hH T]

/-- Every strongly adapted continuous Itô integral of a `BrownianIntegrable` integrand is a true
martingale on the raw filtration. -/
theorem martingale (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (hI_adap : StronglyAdapted ℱ I) :
    Martingale I ℱ P := by
  obtain ⟨Z, n, τ, a, -, hZm, hτ, ha, -, herr, hZ⟩ := exists_martingale_l2 hW hH
  exact hZm.congr hI_adap fun T ↦
    (hI.ae_eq_of_l2_approx hW hH (fun m ↦ (hτ m).monotoneOn) ha herr (fun t ↦ (hZ t).2.2) T).symm

/-! ### Stopping an `L²` Itô integral -/

private def dyadicGrid (k j : ℕ) : ℝ≥0 := (j : ℝ≥0) / 2 ^ k

private def dyadicStopHeight (τ : Ω → WithTop ℝ≥0) (k j : ℕ) (ω : Ω) : ℝ :=
  if (dyadicGrid k j : WithTop ℝ≥0) < dyadicCeilTime k (τ ω) then 1 else 0

private theorem strictMono_dyadicGrid (k : ℕ) : StrictMono (dyadicGrid k) :=
  fun _ _ hij ↦ div_lt_div_of_pos_right (Nat.cast_lt.mpr hij) (by positivity)

private theorem monotoneOn_dyadicGrid (k n : ℕ) : MonotoneOn (dyadicGrid k) (Iic n) :=
  (strictMono_dyadicGrid k).monotone.monotoneOn _

private theorem stronglyMeasurable_dyadicStopHeight (hτ : IsStoppingTime ℱ τ) (k j : ℕ) :
    StronglyMeasurable[ℱ (dyadicGrid k j)] (dyadicStopHeight τ k j) := by
  have hset : MeasurableSet[ℱ (dyadicGrid k j)]
      {ω | (dyadicGrid k j : WithTop ℝ≥0) < dyadicCeilTime k (τ ω)} := by
    convert (hτ.dyadicCeilTime k (dyadicGrid k j)).compl using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff]
    exact lt_iff_not_ge
  exact stronglyMeasurable_const.ite hset stronglyMeasurable_const

private theorem norm_dyadicStopHeight_le (τ : Ω → WithTop ℝ≥0) (k j : ℕ) (ω : Ω) :
    ‖dyadicStopHeight τ k j ω‖ ≤ 1 := by
  unfold dyadicStopHeight
  split_ifs <;> norm_num

private theorem simpleHolding_dyadicStopHeight {T t : ℝ≥0} (ht : t ∈ Ioc 0 T) (k : ℕ) (ω : Ω) :
    Finance.simpleHolding (dyadicGrid k) ⌈T * 2 ^ k⌉₊ (dyadicStopHeight τ k) t ω =
      if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then 1 else 0 := by
  let j : ℕ := ⌈t * 2 ^ k⌉₊ - 1
  have hpos : 0 < ⌈t * 2 ^ k⌉₊ := Nat.ceil_pos.mpr (mul_pos ht.1 (by positivity))
  have hj1 : j + 1 = ⌈t * 2 ^ k⌉₊ := Nat.sub_add_cancel hpos
  have hjM : j < ⌈T * 2 ^ k⌉₊ := by
    have hceil : ⌈t * 2 ^ k⌉₊ ≤ ⌈T * 2 ^ k⌉₊ :=
      Nat.ceil_mono (mul_le_mul_of_nonneg_right ht.2 (by positivity))
    omega
  have hmem : t ∈ Ioc (dyadicGrid k j) (dyadicGrid k (j + 1)) := by
    refine ⟨?_, ?_⟩
    · rw [dyadicGrid, div_lt_iff₀ (by positivity)]
      exact Nat.lt_ceil.mp (by omega)
    · rw [dyadicGrid, le_div_iff₀ (by positivity), hj1]
      exact Nat.le_ceil _
  rw [Finance.simpleHolding_of_mem_Ioc (monotoneOn_dyadicGrid k _) hjM hmem, dyadicStopHeight]
  congr 1
  cases hτω : τ ω with
  | top =>
    rw [dyadicCeilTime_top, eq_iff_iff]
    exact ⟨fun _ ↦ le_top, fun _ ↦ WithTop.coe_lt_top _⟩
  | coe s =>
    rw [dyadicCeilTime_coe, WithTop.coe_lt_coe, WithTop.coe_le_coe]
    dsimp [dyadicGrid]
    rw [div_lt_div_iff_of_pos_right (by positivity), le_div_iff₀ (by positivity),
      Nat.cast_lt, ← Nat.ceil_le, ← hj1]
    exact propext (by omega)

private theorem simpleGains_dyadicStopHeight {G : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω}
    (hG0 : G 0 ω = 0) (k : ℕ) :
    Finance.simpleGains (dyadicGrid k) ⌈T * 2 ^ k⌉₊ (dyadicStopHeight τ k) G T ω =
      MeasureTheory.stoppedProcess G (fun ω ↦ dyadicCeilTime k (τ ω)) T ω := by
  let M : ℕ := ⌈T * 2 ^ k⌉₊
  let f (j : ℕ) : ℝ := G (min (dyadicGrid k j) T) ω
  have hf0 : f 0 = 0 := by simp [f, dyadicGrid, hG0]
  have hTM : T ≤ dyadicGrid k M := (le_div_iff₀ (by positivity)).mpr (Nat.le_ceil _)
  have hfM : f M = G T ω := by simp [f, min_eq_right hTM]
  rw [Finance.simpleGains_def]
  rcases le_or_gt (T : WithTop ℝ≥0) (dyadicCeilTime k (τ ω)) with hle | hgt
  · rw [stoppedProcess_eq_of_le (τ := fun ω ↦ dyadicCeilTime k (τ ω)) hle,
      ← hfM, ← sub_zero (f M), ← hf0, ← sum_range_sub f M]
    refine sum_congr rfl fun j _ ↦ ?_
    by_cases hdj : dyadicGrid k j < T
    · have hlt : (dyadicGrid k j : WithTop ℝ≥0) < dyadicCeilTime k (τ ω) :=
        (WithTop.coe_lt_coe.mpr hdj).trans_le hle
      rw [dyadicStopHeight, ite_eq_left hlt, one_mul]
    · have hge : T ≤ dyadicGrid k j := le_of_not_gt hdj
      have hge' : T ≤ dyadicGrid k (j + 1) :=
        hge.trans ((strictMono_dyadicGrid k (Nat.lt_succ_self j)).le)
      simp [f, min_eq_right hge, min_eq_right hge']
  · cases hτω : τ ω with
    | top =>
      rw [hτω, dyadicCeilTime_top] at hgt
      exact (not_top_lt hgt).elim
    | coe s =>
      let r : ℕ := ⌈s * 2 ^ k⌉₊
      have hρ : dyadicCeilTime k (τ ω) = (dyadicGrid k r : WithTop ℝ≥0) := by
        rw [hτω, dyadicCeilTime_coe]
        rfl
      have hrT : dyadicGrid k r < T := WithTop.coe_lt_coe.mp (hρ ▸ hgt)
      have hrM : r ≤ M :=
        ((strictMono_dyadicGrid k).lt_iff_lt.mp (hrT.trans_le hTM)).le
      have hfr : f r = MeasureTheory.stoppedProcess G (fun ω ↦ dyadicCeilTime k (τ ω)) T ω := by
        rw [stoppedProcess_eq_of_ge (τ := fun ω ↦ dyadicCeilTime k (τ ω)) hgt.le, hρ,
          WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
        dsimp only [f]
        rw [min_eq_left hrT.le]
      rw [← hfr, ← sub_zero (f r), ← hf0, ← sum_range_sub f r]
      have hfilt : (range M).filter (· < r) = range r := by
        ext j
        simp only [mem_filter, Finset.mem_range]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨lt_of_lt_of_le h hrM, h⟩⟩
      rw [← hfilt, sum_filter]
      refine sum_congr rfl fun j _ ↦ ?_
      have hiff : (dyadicGrid k j : WithTop ℝ≥0) < dyadicCeilTime k (τ ω) ↔ j < r := by
        rw [hρ, WithTop.coe_lt_coe, (strictMono_dyadicGrid k).lt_iff_lt]
      by_cases hjr : j < r
      · rw [dyadicStopHeight, ite_eq_left (hiff.mpr hjr), ite_eq_left hjr, one_mul]
      · rw [dyadicStopHeight, ite_eq_right (hiff.not.mpr hjr), ite_eq_right hjr, zero_mul]

private theorem exists_simpleStrategy_mul_dyadicStop (hτ : IsStoppingTime ℱ τ) (k : ℕ) (T : ℝ≥0)
    {n : ℕ} {σ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ} {C : ℝ}
    (hσ : MonotoneOn σ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (σ i)] (a i))
    (hb : ∀ i < n, ∀ ω, ‖a i ω‖ ≤ C) :
    ∃ (N : ℕ) (γ : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ) (C' : ℝ),
      StrictMonoOn γ (Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (γ j)] (c j)) ∧
      (∀ j < N, ∀ ω, ‖c j ω‖ ≤ C') ∧
      (∀ t ∈ Ioc 0 T, ∀ ω,
        Finance.simpleHolding γ N c t ω =
          if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then
            Finance.simpleHolding σ n a t ω else 0) ∧
      ∀ ω, Finance.simpleGains γ N c W T ω =
        MeasureTheory.stoppedProcess (Finance.simpleGains σ n a W)
          (fun ω ↦ dyadicCeilTime k (τ ω)) T ω := by
  let M : ℕ := ⌈T * 2 ^ k⌉₊
  let l (p : Fin M × Fin n) : ℝ≥0 := max (σ p.2.1) (dyadicGrid k p.1.1)
  let u (p : Fin M × Fin n) : ℝ≥0 := min (σ (p.2.1 + 1)) (dyadicGrid k (p.1.1 + 1))
  let α (p : Fin M × Fin n) (ω : Ω) : ℝ := dyadicStopHeight τ k p.1.1 ω * a p.2.1 ω
  have hαm (p : Fin M × Fin n) (_ : p ∈ (univ : Finset _)) :
      StronglyMeasurable[ℱ (l p)] (α p) :=
    ((stronglyMeasurable_dyadicStopHeight hτ k p.1.1).mono (ℱ.mono (le_max_right _ _))).mul
      ((ha p.2.1 p.2.2).mono (ℱ.mono (le_max_left _ _)))
  obtain ⟨N, γ, c, -, hγ, hcm, hcb, hhold, hgains⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sum ℱ univ l u α hαm
  refine ⟨N, γ, c, ∑ _ : Fin M × Fin n, max C 0, hγ, hcm,
    fun j hj ω ↦ (hcb j hj ω).trans (sum_le_sum fun p _ ↦ ?_),
    fun t ht ω ↦ ?_, fun ω ↦ ?_⟩
  · calc
      ‖α p ω‖ = ‖dyadicStopHeight τ k p.1.1 ω‖ * ‖a p.2.1 ω‖ := norm_mul _ _
      _ ≤ 1 * max C 0 := mul_le_mul (norm_dyadicStopHeight_le τ k p.1.1 ω)
          ((hb p.2.1 p.2.2 ω).trans (le_max_left C 0)) (norm_nonneg _) zero_le_one
      _ = max C 0 := one_mul _
  · have hmul := Finance.simpleHolding_mul_eq_sum (ρ := dyadicGrid k) (m := M)
      (b := dyadicStopHeight τ k) (τ := σ) (n := n) (a := a) t ω
    rw [hhold t ω, Fintype.sum_prod_type]
    dsimp only [l, u, α]
    simp_rw [← Fin.sum_univ_eq_sum_range] at hmul
    rw [← hmul, simpleHolding_dyadicStopHeight ht k ω]
    split_ifs <;> ring
  · have hg := Finance.simpleGains_simpleGains_eq_sum (X := W) hσ
      (monotoneOn_dyadicGrid k M) (b := dyadicStopHeight τ k) (a := a) T ω
    rw [hgains W T ω, Fintype.sum_prod_type]
    dsimp only [l, u, α]
    simp_rw [← Fin.sum_univ_eq_sum_range] at hg
    rw [← hg, simpleGains_dyadicStopHeight (Finance.simpleGains_of_le hσ bot_le W ω) k]

private theorem tendsto_eLpNorm_ite_le_dyadicCeilTime_sub
    (hH : BrownianIntegrable ℱ P H) (hτ : IsStoppingTime ℱ τ) (T : ℝ≥0) :
    Tendsto (fun k ↦ eLpNorm (fun p : ℝ≥0 × Ω ↦
      (if (p.1 : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ p.2) then H p.1 p.2 else 0) -
        if (p.1 : WithTop ℝ≥0) ≤ τ p.2 then H p.1 p.2 else 0) 2
      ((Probability.timeMeasure T).prod P)) atTop (𝓝 0) := by
  refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
    (Eventually.of_forall fun k ↦
      ((hH.ite_le (hτ.dyadicCeilTime k)).memLp_timeMeasure T).aestronglyMeasurable)
    (hH.memLp_timeMeasure T)
    (Eventually.of_forall fun k ↦ Eventually.of_forall fun p ↦ ?_)
    (Eventually.of_forall fun p ↦ ?_)
  · have hle := le_dyadicCeilTime k (τ p.2)
    dsimp only [Function.uncurry]
    by_cases h1 : (p.1 : WithTop ℝ≥0) ≤ τ p.2
    · rw [ite_eq_left (h1.trans hle), ite_eq_left h1, sub_self, eNorm_zero, ENNReal.coe_one,
        one_mul]
      exact zero_le
    · rw [ite_eq_right h1, sub_zero, ENNReal.coe_one, one_mul]
      split_ifs
      · exact le_rfl
      · simp
  · by_cases h1 : (p.1 : WithTop ℝ≥0) ≤ τ p.2
    · refine tendsto_const_nhds.congr fun k ↦ ?_
      rw [ite_eq_left h1, ite_eq_left (h1.trans (le_dyadicCeilTime k (τ p.2)))]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [(tendsto_dyadicCeilTime (τ p.2)).eventually
        (eventually_lt_nhds (lt_of_not_ge h1))] with k hk
      rw [ite_eq_right h1, ite_eq_right hk.not_ge]

private theorem stoppedProcess_dyadicCeilTime_ae_eq_condExp [IsFiniteMeasure P]
    {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X ℱ P) (hτ : IsStoppingTime ℱ τ) (T : ℝ≥0) (k : ℕ) :
    MeasureTheory.stoppedProcess X (fun ω ↦ dyadicCeilTime k (τ ω)) T =ᵐ[P]
      P[X T | ((isStoppingTime_const ℱ T).min (hτ.dyadicCeilTime k)).measurableSpace] := by
  have hc : (Set.range fun ω ↦ min (T : WithTop ℝ≥0) (dyadicCeilTime k (τ ω))).Countable :=
    ((countable_singleton (T : WithTop ℝ≥0)).mono range_const_subset).range_min
      (countable_range_dyadicCeilTime τ k)
  exact hX.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    ((isStoppingTime_const ℱ T).min (hτ.dyadicCeilTime k)) (fun _ ↦ min_le_left _ _) hc

private theorem eLpNorm_stoppedProcess_dyadicCeilTime_le [IsFiniteMeasure P]
    {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X ℱ P) (hτ : IsStoppingTime ℱ τ) (T : ℝ≥0) (k : ℕ) :
    eLpNorm (MeasureTheory.stoppedProcess X (fun ω ↦ dyadicCeilTime k (τ ω)) T) 2 P ≤
      eLpNorm (X T) 2 P := by
  let m := ((isStoppingTime_const ℱ T).min (hτ.dyadicCeilTime k)).measurableSpace
  have hcond : MeasureTheory.stoppedProcess X (fun ω ↦ dyadicCeilTime k (τ ω)) T =ᵐ[P]
      P[X T | m] := stoppedProcess_dyadicCeilTime_ae_eq_condExp hX hτ T k
  exact (eLpNorm_congr_ae hcond).trans_le
    (eLpNorm_condExp_le_eLpNorm (m := m) (μ := P) (p := 2) (X T) (by norm_num))

private theorem tendstoInMeasure_stoppedProcess_dyadic_diag [IsFiniteMeasure P]
    {M : ℕ → ℝ≥0 → Ω → ℝ} {Z : ℝ≥0 → Ω → ℝ} {m : ℕ → ℕ} {T : ℝ≥0}
    (hMm : ∀ k, Martingale (M k) ℱ P) (hZm : Martingale Z ℱ P)
    (hτ : IsStoppingTime ℱ τ)
    (hIZ : ∀ s, I s =ᵐ[P] Z s)
    (hI_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω))
    (herr : ∀ k, eLpNorm (M (m k) T - Z T) 2 P < ((k : ℝ≥0∞) + 1)⁻¹) :
    TendstoInMeasure P
      (fun k ↦ MeasureTheory.stoppedProcess (M (m k)) (fun ω ↦ dyadicCeilTime k (τ ω)) T)
      atTop (MeasureTheory.stoppedProcess I τ T) := by
  have hinv : Tendsto (fun k : ℕ ↦ ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    simpa [Function.comp_def] using ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hdiff_l2 : Tendsto (fun k ↦ eLpNorm
      (MeasureTheory.stoppedProcess (M (m k) - Z) (fun ω ↦ dyadicCeilTime k (τ ω)) T - 0) 2 P)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv (fun _ ↦ zero_le)
      fun k ↦ ?_
    rw [sub_zero]
    have hle := eLpNorm_stoppedProcess_dyadicCeilTime_le ((hMm (m k)).sub hZm) hτ T k
    exact hle.trans (herr k).le
  have hIZ_ρ (k : ℕ) :
      MeasureTheory.stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T =ᵐ[P]
        MeasureTheory.stoppedProcess Z (fun ω ↦ dyadicCeilTime k (τ ω)) T := by
    have hc : (Set.range fun ω ↦ min (T : WithTop ℝ≥0) (dyadicCeilTime k (τ ω))).Countable :=
      ((countable_singleton (T : WithTop ℝ≥0)).mono range_const_subset).range_min
        (countable_range_dyadicCeilTime τ k)
    have hSc : ((WithTop.untopA : WithTop ℝ≥0 → ℝ≥0) ''
        Set.range fun ω ↦ min (T : WithTop ℝ≥0) (dyadicCeilTime k (τ ω))).Countable :=
      hc.image WithTop.untopA
    filter_upwards [(ae_ball_iff hSc).2 fun s _ ↦ hIZ s] with ω hω
    exact hω _ (mem_image_of_mem WithTop.untopA (mem_range_self ω))
  have hI_meas (k : ℕ) :
      AEStronglyMeasurable (MeasureTheory.stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T) P :=
    ((hZm.stoppedProcess_of_countable_range (hτ.dyadicCeilTime k)
      (countable_range_dyadicCeilTime τ k)).integrable T).aestronglyMeasurable.congr
        (hIZ_ρ k).symm
  have hI_lim : TendstoInMeasure P
      (fun k ↦ MeasureTheory.stoppedProcess I (fun ω ↦ dyadicCeilTime k (τ ω)) T)
      atTop (MeasureTheory.stoppedProcess I τ T) :=
    tendstoInMeasure_of_tendsto_ae hI_meas (hI_cont.mono fun ω hω ↦
      tendsto_stoppedProcess_dyadicCeilTime I τ T ω hω.continuousAt.continuousWithinAt)
  have hsum := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hdiff_l2).add
    (hI_lim.congr_left fun k ↦ hIZ_ρ k)
  refine hsum.congr (fun k ↦ .of_forall fun ω ↦ ?_) (.of_forall fun ω ↦ zero_add _)
  dsimp only [Pi.add_apply, MeasureTheory.stoppedProcess, MeasureTheory.stoppedValue, Pi.sub_apply]
  exact sub_add_cancel _ _

private theorem tendsto_eLpNorm_simpleHolding_mul_dyadicStop_sub
    (hH : BrownianIntegrable ℱ P H) (hτ : IsStoppingTime ℱ τ) {T : ℝ≥0}
    {n : ℕ → ℕ} {σ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ} {m : ℕ → ℕ}
    {N : ℕ → ℕ} {γ : ℕ → ℕ → ℝ≥0} {c : ℕ → ℕ → Ω → ℝ}
    (hcm : ∀ k j, j < N k → StronglyMeasurable[ℱ (γ k j)] (c k j))
    (hm_hold : ∀ k, eLpNorm
      (fun p ↦ Finance.simpleHolding (σ (m k)) (n (m k)) (a (m k)) p.1 p.2 - H p.1 p.2) 2
        ((Probability.timeMeasure T).prod P) < ((k : ℝ≥0∞) + 1)⁻¹)
    (hhold : ∀ k, ∀ t ∈ Ioc 0 T, ∀ ω,
      Finance.simpleHolding (γ k) (N k) (c k) t ω =
        if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then
          Finance.simpleHolding (σ (m k)) (n (m k)) (a (m k)) t ω else 0) :
    Tendsto (fun k ↦ eLpNorm (fun p : ℝ≥0 × Ω ↦
      Finance.simpleHolding (γ k) (N k) (c k) p.1 p.2 -
        if (p.1 : WithTop ℝ≥0) ≤ τ p.2 then H p.1 p.2 else 0) 2
      ((Probability.timeMeasure T).prod P)) atTop (𝓝 0) := by
  let g₁ (k : ℕ) (p : ℝ≥0 × Ω) : ℝ :=
    Finance.simpleHolding (γ k) (N k) (c k) p.1 p.2 -
      if (p.1 : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ p.2) then H p.1 p.2 else 0
  let g₂ (k : ℕ) (p : ℝ≥0 × Ω) : ℝ :=
    (if (p.1 : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ p.2) then H p.1 p.2 else 0) -
      if (p.1 : WithTop ℝ≥0) ≤ τ p.2 then H p.1 p.2 else 0
  have hg₁_l2 : Tendsto (fun k ↦ eLpNorm (g₁ k) 2 ((Probability.timeMeasure T).prod P))
      atTop (𝓝 0) := by
    have hle (k : ℕ) : eLpNorm (g₁ k) 2 ((Probability.timeMeasure T).prod P) ≤
        ((k : ℝ≥0∞) + 1)⁻¹ := by
      have hm₁ : AEStronglyMeasurable (g₁ k) ((Probability.timeMeasure T).prod P) :=
        (((Finance.isStronglyPredictable_simpleHolding (hcm k)).sub
          (hH.ite_le (hτ.dyadicCeilTime k)).isStronglyPredictable).mono
            ℱ.predictable_le_prod).aestronglyMeasurable
      refine (eLpNorm_mono_ae hm₁ ?_).trans (hm_hold k).le
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := Probability.timeMeasure T)
        (ν := P)).ae (Probability.ae_mem_Ioc_timeMeasure T)] with p hp
      dsimp only [g₁]
      rw [hhold k p.1 hp p.2]
      by_cases hle' : (p.1 : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ p.2)
      · rw [ite_eq_left hle', ite_eq_left hle']
      · rw [ite_eq_right hle', ite_eq_right hle', sub_zero]
        exact norm_zero.trans_le (norm_nonneg _)
    have hinv : Tendsto (fun k : ℕ ↦ ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv
      (fun _ ↦ zero_le) hle
  have htri (k : ℕ) : eLpNorm (fun p : ℝ≥0 × Ω ↦
      Finance.simpleHolding (γ k) (N k) (c k) p.1 p.2 -
        if (p.1 : WithTop ℝ≥0) ≤ τ p.2 then H p.1 p.2 else 0) 2
      ((Probability.timeMeasure T).prod P) ≤
      eLpNorm (g₁ k) 2 ((Probability.timeMeasure T).prod P) +
        eLpNorm (g₂ k) 2 ((Probability.timeMeasure T).prod P) := by
    have hadd : (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (γ k) (N k) (c k) p.1 p.2 -
        if (p.1 : WithTop ℝ≥0) ≤ τ p.2 then H p.1 p.2 else 0) = g₁ k + g₂ k := by
      ext p
      dsimp only [g₁, g₂, Pi.add_apply]
      ring
    rw [hadd]
    exact eLpNorm_add_le (by norm_num)
  have hsum := hg₁_l2.add (tendsto_eLpNorm_ite_le_dyadicCeilTime_sub hH hτ T)
  rw [add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) htri

/-- **Optional stopping for the continuous `L²` Brownian Itô integral**: stopping a continuous Itô
integral `I` of a `BrownianIntegrable` integrand `H` at any stopping time `τ` yields a continuous
Itô integral of the cutoff integrand `H · 1_{[0, τ]}`. Neither path continuity of `W` nor
adaptation of `I` is required. -/
theorem stoppedProcess (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hτ : IsStoppingTime ℱ τ)
    (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (MeasureTheory.stoppedProcess I τ) where
  isStronglyPredictable := (hH.ite_le hτ).isStronglyPredictable
  ae_continuous := hI.ae_continuous.mono fun _ hω ↦ hω.stoppedProcess
  exists_seq_approx T := by
    have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
    obtain ⟨Z, n, σ, a, C, hZm, hσ, ha, hb, herr, hZ⟩ := exists_martingale_l2 hW hH
    have hMm (i : ℕ) : Martingale (Finance.simpleGains (σ i) (n i) (a i) W) ℱ P :=
      hW.martingale.simpleGains_of_bdd (hσ i).monotoneOn (ha i) fun j hj ↦
        ⟨C i, .of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hb i j hj ω⟩
    have hex_m (k : ℕ) : ∃ m : ℕ,
        eLpNorm (fun p ↦ Finance.simpleHolding (σ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
          ((Probability.timeMeasure T).prod P) < ((k : ℝ≥0∞) + 1)⁻¹ ∧
        eLpNorm (Finance.simpleGains (σ m) (n m) (a m) W T - Z T) 2 P < ((k : ℝ≥0∞) + 1)⁻¹ := by
      have hpos : (0 : ℝ≥0∞) < ((k : ℝ≥0∞) + 1)⁻¹ :=
        ENNReal.inv_pos.mpr (by simp [ENNReal.natCast_ne_top])
      exact (((herr T).eventually (gt_mem_nhds hpos)).and
        ((hZ T).2.2.eventually (gt_mem_nhds hpos))).exists
    choose m hm_hold hm_gain using hex_m
    choose N γ c C' hγ hcm hcb hhold hgains using fun k ↦
      exists_simpleStrategy_mul_dyadicStop hτ k T (hσ (m k)).monotoneOn (ha (m k)) (hb (m k))
    refine ⟨N, γ, c, fun k ↦ (hγ k).monotoneOn, hcm, fun k j hj ↦ ⟨C' k, hcb k j hj⟩, ?_, ?_⟩
    · exact tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
        (fun k ↦ Finance.isStronglyPredictable_simpleHolding (hcm k))
        (hH.ite_le hτ).isStronglyPredictable
        (tendsto_eLpNorm_simpleHolding_mul_dyadicStop_sub hH hτ hcm hm_hold hhold)
    · refine (tendstoInMeasure_stoppedProcess_dyadic_diag hMm hZm hτ
        (hI.ae_eq_of_l2_approx hW hH (fun i ↦ (hσ i).monotoneOn) ha herr (fun t ↦ (hZ t).2.2))
        hI.ae_continuous hm_gain).congr_left fun k ↦ .of_forall fun ω ↦ (hgains k ω).symm

/-- Stopping a continuous Itô integral `I` of a `BrownianIntegrable` integrand `H` at a stopping
time `τ` gives a process indistinguishable from any continuous Itô integral `J` of
`H · 1_{[0, τ]}`. -/
theorem stoppedProcess_indist (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hτ : IsStoppingTime ℱ τ)
    (hI : IsItoIntegral ℱ P W H I)
    (hJ : IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) J) :
    MeasureTheory.stoppedProcess I τ ≡ᵐ[P] J :=
  (hI.stoppedProcess hW hH hτ).indist hW hJ

end IsItoIntegral

end TauCeti
