/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Indistinguishable
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Process.TimeMeasure
import Mathlib.Topology.Instances.NNReal.Lemmas
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Process.ContinuousAE

/-!
# Continuous-time Itô stochastic integrals: definition, algebra, and uniqueness

`TauCeti.Probability.IsItoIntegral ℱ P W H I` characterizes a continuous-time stochastic
integral process `I` of a predictable real integrand `H` against an integrator `W`: the paths
of `I` are almost surely continuous and, at every finite horizon `t`, some sequence of bounded
left-measurable simple holdings approximates `H` in pathwise square energy in probability on
`(0, t]` while their elementary gains `Finance.simpleGains` converge in probability to `I t`.
Using the lower Lebesgue integral for the square-energy error ensures that non-integrable
deviations register as infinite energy rather than a fallback Bochner value.

Every Itô integral automatically starts at zero almost surely and forces its integrand to be
locally Brownian integrable, with no assumption on `W` or finiteness of `P`. The predicate is
closed under indistinguishability of the integral, product-almost-everywhere replacement of the
predictable integrand, fixed-time almost-everywhere replacement of the integrator, filtration
enlargement, addition, scaling, and negation, and holds for elementary holdings and constants.

Against a filtered pre-Brownian motion `W`—without assuming path continuity of `W` or usual
conditions on `ℱ`—any two Itô integrals of the same integrand (or of product-almost-everywhere
equal predictable integrands) are indistinguishable. The proof places both approximating
sequences on a common grid via `Finance.exists_simpleHolding_simpleGains_eq_sum`, clips the
grid at the observation time while zeroing heights beyond it, and applies the elementary
energy-to-probability estimate `IsFilteredPreBrownianReal.tendstoInMeasure_sum_mul_sub_of_energy`
before lifting fixed-time equality to whole paths along a countable dense subset of `ℝ≥0`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, §2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W W' H K I J : ℝ≥0 → Ω → ℝ}

/-- `IsItoIntegral ℱ P W H I` asserts that `I` is a continuous-time Itô stochastic integral of
the predictable integrand `H` with respect to `W`: `I` has almost surely continuous paths, and
for every horizon `t` there is a sequence of bounded left-measurable simple holdings whose
pathwise square-energy errors against `H` on `(0, t]` tend to zero in probability while their
elementary gains at `t` converge in probability to `I t`. -/
structure IsItoIntegral (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (W H I : ℝ≥0 → Ω → ℝ) : Prop where
  /-- The integrand is literally predictable for the declared filtration. -/
  isStronglyPredictable : IsStronglyPredictable ℱ H
  /-- The integral process has almost surely continuous paths. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)
  /-- At every finite horizon, bounded left-measurable simple holdings approximate `H` in
  pathwise square energy in probability while their elementary integrals converge to `I t`. -/
  approx : ∀ t : ℝ≥0, ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ),
    (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
    (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
    (∀ k j, j < n k → ∃ C : ℝ, ∀ ω, ‖a k j ω‖ ≤ C) ∧
    (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
        ∂timeMeasure t}) atTop (𝓝 0)) ∧
    TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t) atTop (I t)

/-! ### Private helpers for `timeMeasure` square energy and common simple-holding grids -/

private theorem lintegral_eNorm_sq_le_of_add {f g : ℝ≥0 → ℝ} (t : ℝ≥0) (hf : Measurable f) :
    (∫⁻ s, ‖f s + g s‖ₑ ^ 2 ∂timeMeasure t) ≤
      2 * (∫⁻ s, ‖f s‖ₑ ^ 2 ∂timeMeasure t) + 2 * (∫⁻ s, ‖g s‖ₑ ^ 2 ∂timeMeasure t) := by
  calc
    _ ≤ ∫⁻ s, 2 * ‖f s‖ₑ ^ 2 + 2 * ‖g s‖ₑ ^ 2 ∂timeMeasure t := by
      refine lintegral_mono fun s ↦ ?_
      have h := ENNReal.ofReal_le_ofReal (norm_sub_sq_le_two_mul (f s) (-g s) 0)
      simp only [sub_neg_eq_add, sub_zero, norm_neg,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.ofReal_ofNat] at h
      simpa only [mul_add] using h
    _ = _ := by
      rw [lintegral_add_left ((hf.eNorm.pow_const 2).const_mul 2),
        lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]

private theorem tendsto_measure_lintegral_add_sq {f g h : ℕ → ℝ≥0 → Ω → ℝ} (t : ℝ≥0)
    (hf : ∀ k ω, Measurable (fun s ↦ f k s ω))
    (hpt : ∀ k ω s, h k s ω = f k s ω + g k s ω)
    (hf0 : ∀ ε : ℝ≥0∞, 0 < ε →
      Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖f k s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    (hg0 : ∀ ε : ℝ≥0∞, 0 < ε →
      Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖g k s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖h k s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0) := by
  have hε4 : 0 < ε / 4 := by
    by_cases htop : ε = ∞
    · simp [htop]
    · exact ENNReal.div_pos hε.ne' (by norm_num)
  have hsub (k : ℕ) :
      {ω | ε ≤ ∫⁻ s, ‖h k s ω‖ₑ ^ 2 ∂timeMeasure t} ⊆
        {ω | ε / 4 ≤ ∫⁻ s, ‖f k s ω‖ₑ ^ 2 ∂timeMeasure t} ∪
          {ω | ε / 4 ≤ ∫⁻ s, ‖g k s ω‖ₑ ^ 2 ∂timeMeasure t} := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hnot
    have hlt : 2 * (∫⁻ s, ‖f k s ω‖ₑ ^ 2 ∂timeMeasure t) +
        2 * (∫⁻ s, ‖g k s ω‖ₑ ^ 2 ∂timeMeasure t) < ε := by
      by_cases htop : ε = ∞
      · subst htop
        have htop4 : (∞ : ℝ≥0∞) / 4 = ∞ := ENNReal.top_div_of_ne_top (by norm_num)
        have hlt1 : ∫⁻ s, ‖f k s ω‖ₑ ^ 2 ∂timeMeasure t < ∞ := by
          simpa only [htop4] using hnot.1
        have hlt2 : ∫⁻ s, ‖g k s ω‖ₑ ^ 2 ∂timeMeasure t < ∞ := by
          simpa only [htop4] using hnot.2
        exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) hlt1,
          ENNReal.mul_lt_top (by norm_num) hlt2⟩
      · have h1 : 2 * (∫⁻ s, ‖f k s ω‖ₑ ^ 2 ∂timeMeasure t) < 2 * (ε / 4) :=
          ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hnot.1
        have h2 : 2 * (∫⁻ s, ‖g k s ω‖ₑ ^ 2 ∂timeMeasure t) < 2 * (ε / 4) :=
          ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hnot.2
        have hsum : 2 * (ε / 4) + 2 * (ε / 4) = ε := by
          rw [← two_mul, ← mul_assoc]
          norm_num
          exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
        exact (ENNReal.add_lt_add h1 h2).trans_eq hsum
    have hle : ∫⁻ s, ‖h k s ω‖ₑ ^ 2 ∂timeMeasure t ≤
        2 * (∫⁻ s, ‖f k s ω‖ₑ ^ 2 ∂timeMeasure t) +
          2 * (∫⁻ s, ‖g k s ω‖ₑ ^ 2 ∂timeMeasure t) := by
      simp_rw [hpt k ω]
      exact lintegral_eNorm_sq_le_of_add t (hf k ω)
    exact hlt.not_ge (hω.trans hle)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using (hf0 _ hε4).add (hg0 _ hε4)) (fun _ ↦ zero_le) fun k ↦ ?_
  exact (measure_mono (hsub k)).trans (measure_union_le _ _)

private theorem exists_simpleHolding_add_common
    {n₁ n₂ : ℕ} {τ₁ τ₂ : ℕ → ℝ≥0} {a₁ a₂ : ℕ → Ω → ℝ}
    (hτ₁ : MonotoneOn τ₁ (Iic n₁)) (hτ₂ : MonotoneOn τ₂ (Iic n₂))
    (ha₁ : ∀ j < n₁, StronglyMeasurable[ℱ (τ₁ j)] (a₁ j))
    (ha₂ : ∀ j < n₂, StronglyMeasurable[ℱ (τ₂ j)] (a₂ j)) :
    ∃ (n : ℕ) (τ : ℕ → ℝ≥0) (b : ℕ → Ω → ℝ),
      MonotoneOn τ (Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (b j)) ∧
      (∀ j < n, ∀ ω, ‖b j ω‖ ≤ ∑ i ∈ range n₁, ‖a₁ i ω‖ + ∑ i ∈ range n₂, ‖a₂ i ω‖) ∧
      (∀ s ω, Finance.simpleHolding τ n b s ω =
        Finance.simpleHolding τ₁ n₁ a₁ s ω + Finance.simpleHolding τ₂ n₂ a₂ s ω) ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) s ω, Finance.simpleGains τ n b X s ω =
        Finance.simpleGains τ₁ n₁ a₁ X s ω + Finance.simpleGains τ₂ n₂ a₂ X s ω := by
  let l : Fin n₁ ⊕ Fin n₂ → ℝ≥0 := Sum.elim (fun i ↦ τ₁ i.val) (fun j ↦ τ₂ j.val)
  let u : Fin n₁ ⊕ Fin n₂ → ℝ≥0 := Sum.elim (fun i ↦ τ₁ (i.val + 1)) (fun j ↦ τ₂ (j.val + 1))
  let h : Fin n₁ ⊕ Fin n₂ → Ω → ℝ := Sum.elim (fun i ↦ a₁ i.val) (fun j ↦ a₂ j.val)
  have hlu : ∀ i : Fin n₁ ⊕ Fin n₂, l i ≤ u i := by
    rintro (i | j)
    · exact hτ₁ (mem_Iic.mpr i.isLt.le) (mem_Iic.mpr i.isLt) (Nat.le_succ _)
    · exact hτ₂ (mem_Iic.mpr j.isLt.le) (mem_Iic.mpr j.isLt) (Nat.le_succ _)
  have hh : ∀ i ∈ (Finset.univ : Finset (Fin n₁ ⊕ Fin n₂)),
      StronglyMeasurable[ℱ (l i)] (h i) := by
    rintro (i | j) _
    · exact ha₁ i.val i.isLt
    · exact ha₂ j.val j.isLt
  obtain ⟨n, τ, b, -, hτ, hb, hbound, hhold, hgain⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sum ℱ Finset.univ l u h hh
  refine ⟨n, τ, b, hτ.monotoneOn, hb, fun j hj ω ↦ ?_, ?_, ?_⟩
  · refine (hbound j hj ω).trans_eq ?_
    rw [Fintype.sum_sum_type]
    simp only [h, Sum.elim_inl, Sum.elim_inr]
    rw [Fin.sum_univ_eq_sum_range (f := fun i ↦ ‖a₁ i ω‖),
      Fin.sum_univ_eq_sum_range (f := fun i ↦ ‖a₂ i ω‖)]
  · intro s ω
    rw [hhold s ω, Fintype.sum_sum_type]
    simp only [l, u, h, Sum.elim_inl, Sum.elim_inr]
    rw [Fin.sum_univ_eq_sum_range (f := fun i ↦
        (Ioc (τ₁ i) (τ₁ (i + 1))).indicator (fun _ ↦ a₁ i ω) s),
      Fin.sum_univ_eq_sum_range (f := fun j ↦
        (Ioc (τ₂ j) (τ₂ (j + 1))).indicator (fun _ ↦ a₂ j ω) s)]
    simp only [Finance.simpleHolding_def]
  · intro X s ω
    have hif (i : Fin n₁ ⊕ Fin n₂) :
        (if l i ≤ u i then h i ω * (X (min (u i) s) ω - X (min (l i) s) ω) else 0) =
          h i ω * (X (min (u i) s) ω - X (min (l i) s) ω) := by
      simp [hlu i]
    rw [hgain X s ω, Finset.sum_congr rfl fun i _ ↦ hif i, Fintype.sum_sum_type]
    simp only [l, u, h, Sum.elim_inl, Sum.elim_inr]
    rw [Fin.sum_univ_eq_sum_range (f := fun i ↦
        a₁ i ω * (X (min (τ₁ (i + 1)) s) ω - X (min (τ₁ i) s) ω)),
      Fin.sum_univ_eq_sum_range (f := fun j ↦
        a₂ j ω * (X (min (τ₂ (j + 1)) s) ω - X (min (τ₂ j) s) ω))]
    simp only [Finance.simpleGains_def]

/-! ### Basic properties and closure of `IsItoIntegral` -/

namespace IsItoIntegral

/-- Every Itô integral starts at zero almost surely, with no assumptions on the integrator
or sample measure. -/
theorem eval_zero_ae_eq_zero (hI : IsItoIntegral ℱ P W H I) : I 0 =ᵐ[P] 0 := by
  obtain ⟨n, τ, a, -, -, -, -, hlim⟩ := hI.approx 0
  have hzero : ∀ k, Finance.simpleGains (τ k) (n k) (a k) W 0 = 0 := fun k ↦ by
    ext ω
    simp [Finance.simpleGains_def]
  have ht0 : TendstoInMeasure P (fun _ : ℕ ↦ (0 : Ω → ℝ)) atTop (0 : Ω → ℝ) := fun ε hε ↦ by
    simp [hε.not_ge]
  exact tendstoInMeasure_ae_unique (by simpa only [hzero] using hlim) ht0

/-- Any integrand admitting an Itô integral has finite pathwise square energy on every finite
horizon outside one common null set. Neither a Brownian law nor finiteness of `P` is needed. -/
theorem locallyBrownianIntegrable (hI : IsItoIntegral ℱ P W H I) :
    LocallyBrownianIntegrable ℱ P H := by
  refine locallyBrownianIntegrable_iff_nat.2 ⟨hI.isStronglyPredictable, fun m ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, -, hb, henergy, -⟩ := hI.approx m
  have hHmeas : StronglyMeasurable (Function.uncurry H) :=
    hI.isStronglyPredictable.mono ℱ.predictable_le_prod
  have hfinite : ∀ᵐ ω ∂P, ∫⁻ s, ‖H s ω‖ₑ ^ 2 ∂timeMeasure m < ∞ := by
    rw [ae_iff]
    have hsub (k : ℕ) : {ω | ¬ ∫⁻ s, ‖H s ω‖ₑ ^ 2 ∂timeMeasure m < ∞} ⊆
        {ω | (1 : ℝ≥0∞) ≤ ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
          ∂timeMeasure m} := by
      intro ω hω
      simp only [mem_ofPred_eq, not_lt, top_le_iff] at hω ⊢
      have hKfin : ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω‖ₑ ^ 2 ∂timeMeasure m < ∞ := by
        rw [Finance.lintegral_enorm_sq_simpleHolding_timeMeasure (hτ k)]
        refine ENNReal.sum_lt_top.2 fun j hj ↦ ?_
        obtain ⟨C, hC⟩ := hb k j (mem_range.mp hj)
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (lt_of_le_of_lt
          (by simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hC ω))
          ENNReal.ofReal_lt_top)) ENNReal.ofReal_lt_top
      have hKmeas : Measurable (fun s ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω) := by
        simp only [Finance.simpleHolding_def]
        exact Finset.measurable_sum _ fun _ _ ↦ measurable_const.indicator measurableSet_Ioc
      have hHω : Measurable (fun s ↦ H s ω) :=
        (hHmeas.comp_measurable measurable_prodMk_right).measurable
      have hle := lintegral_eNorm_sq_le_of_add
        (g := fun s ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω) m (hHω.sub hKmeas)
      simp only [Pi.sub_apply, sub_add_cancel] at hle
      by_contra hlt
      have hfin1 : ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
          ∂timeMeasure m < ∞ := (not_le.mp hlt).trans ENNReal.one_lt_top
      have hfin2 : ∫⁻ s, ‖H s ω - Finance.simpleHolding (τ k) (n k) (a k) s ω‖ₑ ^ 2
          ∂timeMeasure m < ∞ := by
        simpa only [eNorm_sub_rev] using hfin1
      have htop : ∫⁻ s, ‖H s ω‖ₑ ^ 2 ∂timeMeasure m < ∞ :=
        hle.trans_lt (ENNReal.add_lt_top.2
          ⟨ENNReal.mul_lt_top (by norm_num) hfin2, ENNReal.mul_lt_top (by norm_num) hKfin⟩)
      exact htop.ne hω
    exact le_antisymm (ge_of_tendsto' (henergy 1 zero_lt_one) (fun k ↦ measure_mono (hsub k)))
      zero_le
  filter_upwards [hfinite] with ω hω
  have hHω : AEStronglyMeasurable (fun s ↦ H s ω) (timeMeasure m) :=
    (hHmeas.comp_measurable measurable_prodMk_right).aestronglyMeasurable
  have hmem := hHω.memLp_two_iff_lintegral_enorm_sq_lt_top.2 hω
  rw [timeMeasure_def, ← NNReal.comap_volume_restrict_Ioc, NNReal.coe_natCast] at hmem
  exact hmem

/-- Replacing an Itô integral by an indistinguishable process preserves `IsItoIntegral`. -/
theorem congr_integral (hI : IsItoIntegral ℱ P W H I) (hIJ : I ≡ᵐ[P] J) :
    IsItoIntegral ℱ P W H J where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := by
    filter_upwards [hI.ae_continuous, hIJ] with ω hω heq
    exact hω.congr fun t ↦ heq t
  approx t := by
    obtain ⟨n, τ, a, hτ, ha, hb, henergy, hlim⟩ := hI.approx t
    exact ⟨n, τ, a, hτ, ha, hb, henergy, hlim.congr_right (hIJ.ae_eq_eval t)⟩

/-- Replacing the integrator by a process equal almost surely at each deterministic time
preserves `IsItoIntegral`. -/
theorem congr_noise (hI : IsItoIntegral ℱ P W H I) (hWW' : ∀ t, W t =ᵐ[P] W' t) :
    IsItoIntegral ℱ P W' H I where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := hI.ae_continuous
  approx t := by
    obtain ⟨n, τ, a, hτ, ha, hb, henergy, hlim⟩ := hI.approx t
    refine ⟨n, τ, a, hτ, ha, hb, henergy, hlim.congr_left fun k ↦ ?_⟩
    have hall : ∀ᵐ ω ∂P, ∀ j ≤ n k, W (min (τ k j) t) ω = W' (min (τ k j) t) ω :=
      ae_all_iff.2 fun j ↦ ae_all_iff.2 fun _ ↦ hWW' _
    filter_upwards [hall] with ω hω
    exact Finance.simpleGains_congr_price ω hω

/-- Product-almost-everywhere replacement of the integrand by a predictable process preserves
`IsItoIntegral`. -/
theorem congr_integrand [SFinite P] (hI : IsItoIntegral ℱ P W H I)
    (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure T).prod P] Function.uncurry K) :
    IsItoIntegral ℱ P W K I where
  isStronglyPredictable := hK
  ae_continuous := hI.ae_continuous
  approx t := by
    obtain ⟨n, τ, a, hτ, ha, hb, henergy, hlim⟩ := hI.approx t
    have hsec : ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[timeMeasure t] (fun s ↦ K s ω) :=
      Measure.ae_ae_of_ae_prod
        ((Measure.measurePreserving_swap (μ := P) (ν := timeMeasure t)).quasiMeasurePreserving
          |>.ae_eq_comp (hHK t))
    refine ⟨n, τ, a, hτ, ha, hb, fun ε hε ↦ ?_, hlim⟩
    have hcongr (k : ℕ) :
        P {ω | ε ≤ ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - K s ω‖ₑ ^ 2
          ∂timeMeasure t} =
        P {ω | ε ≤ ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
          ∂timeMeasure t} := by
      refine measure_congr ?_
      filter_upwards [hsec] with ω hω
      have hint : (∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - K s ω‖ₑ ^ 2
          ∂timeMeasure t) =
          ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t :=
        lintegral_congr_ae (hω.mono fun s hs ↦ by simp [hs])
      simp [hint]
    simpa only [hcongr] using henergy ε hε

/-- Enlarging the filtration preserves `IsItoIntegral`. -/
theorem mono_filtration {𝒢 : Filtration ℝ≥0 mΩ} (hI : IsItoIntegral ℱ P W H I) (h : ℱ ≤ 𝒢) :
    IsItoIntegral 𝒢 P W H I where
  isStronglyPredictable := hI.isStronglyPredictable.mono (Filtration.predictable_mono h)
  ae_continuous := hI.ae_continuous
  approx t := by
    obtain ⟨n, τ, a, hτ, ha, hb, henergy, hlim⟩ := hI.approx t
    exact ⟨n, τ, a, hτ, fun k j hj ↦ (ha k j hj).mono (h _), hb, henergy, hlim⟩

/-- The zero process is an Itô integral of the zero integrand against any integrator. -/
theorem zero (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) :
    IsItoIntegral ℱ P W 0 0 where
  isStronglyPredictable := stronglyMeasurable_zero
  ae_continuous := Eventually.of_forall fun _ ↦ continuous_const
  approx t := by
    refine ⟨fun _ ↦ 0, fun _ _ ↦ 0, fun _ _ _ ↦ 0, fun _ ↦ monotoneOn_const,
      fun _ _ hj ↦ (Nat.not_lt_zero _ hj).elim,
      fun _ _ hj ↦ (Nat.not_lt_zero _ hj).elim, fun ε hε ↦ ?_, fun ε hε ↦ ?_⟩
    · simp [Finance.simpleHolding_def, hε.not_ge]
    · simp [Finance.simpleGains_def, hε.not_ge]

/-- For an almost surely continuous integrator, the elementary gains of a bounded
left-measurable simple holding form an Itô integral of that holding. -/
theorem simpleHolding {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j < n, ∃ C : ℝ, ∀ ω, ‖a j ω‖ ≤ C) :
    IsItoIntegral ℱ P W (Finance.simpleHolding τ n a) (Finance.simpleGains τ n a W) where
  isStronglyPredictable := Finance.isStronglyPredictable_simpleHolding ha
  ae_continuous := by
    filter_upwards [hcont] with ω hω
    simp only [Finance.simpleGains_def]
    exact continuous_finsetSum _ fun j _ ↦ continuous_const.mul
      ((hω.comp (continuous_const.min continuous_id)).sub
        (hω.comp (continuous_const.min continuous_id)))
  approx t := by
    refine ⟨fun _ ↦ n, fun _ ↦ τ, fun _ ↦ a, fun _ ↦ hτ, fun _ ↦ ha, fun _ ↦ hb,
      fun ε hε ↦ ?_, fun ε hε ↦ ?_⟩
    · simp [hε.not_ge]
    · simp [hε.not_ge]

/-- For an almost surely continuous integrator starting at zero almost surely, `c • W` is an
Itô integral of the constant integrand `c`. -/
theorem const (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hW0 : W 0 =ᵐ[P] 0) (c : ℝ) :
    IsItoIntegral ℱ P W (fun _ _ ↦ c) (fun t ω ↦ c * W t ω) where
  isStronglyPredictable := stronglyMeasurable_const
  ae_continuous := hcont.mono fun _ hω ↦ continuous_const.mul hω
  approx t := by
    let τ : ℕ → ℝ≥0 := fun j ↦ if j = 0 then 0 else t
    refine ⟨fun _ ↦ 1, fun _ ↦ τ, fun _ _ _ ↦ c,
      fun _ i _ j _ hij ↦ by
        by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [τ, hi, hj]
        omega,
      fun _ _ _ ↦ stronglyMeasurable_const,
      fun _ _ _ ↦ ⟨‖c‖, fun _ ↦ le_rfl⟩, fun ε hε ↦ ?_, ?_⟩
    · have hzero (ω : Ω) :
          ∫⁻ s, ‖Finance.simpleHolding τ 1 (fun _ _ ↦ c) s ω - c‖ₑ ^ 2 ∂timeMeasure t = 0 := by
        rw [lintegral_eq_zero_iff']
        · filter_upwards [ae_mem_Ioc_timeMeasure t] with s hs
          simp [Finance.simpleHolding_def, τ, hs]
        · have hm : Measurable (fun s ↦ Finance.simpleHolding τ 1 (fun _ _ ↦ c) s ω - c) := by
            simp only [Finance.simpleHolding_def, sum_range_one, τ, ite_true,
              Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
            exact (measurable_const.indicator measurableSet_Ioc).sub measurable_const
          exact (hm.eNorm.pow_const 2).aemeasurable
      simp [hzero, hε.not_ge]
    · have hgain : Finance.simpleGains τ 1 (fun _ _ ↦ c) W t =ᵐ[P] fun ω ↦ c * W t ω := by
        filter_upwards [hW0] with ω hω
        simp [Finance.simpleGains_def, τ, hω]
      refine TendstoInMeasure.congr_left (fun _ ↦ hgain.symm) fun ε hε ↦ ?_
      simp [hε.not_ge]

/-- Itô integrals are additive in the integrand and the integral process. -/
theorem add (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (fun t ω ↦ H t ω + K t ω) (fun t ω ↦ I t ω + J t ω) where
  isStronglyPredictable := hI.isStronglyPredictable.add hJ.isStronglyPredictable
  ae_continuous := by
    filter_upwards [hI.ae_continuous, hJ.ae_continuous] with ω hIω hJω
    exact hIω.add hJω
  approx t := by
    obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, hb₁, hE₁, hL₁⟩ := hI.approx t
    obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hb₂, hE₂, hL₂⟩ := hJ.approx t
    have hcomb (k : ℕ) := exists_simpleHolding_add_common
      (hτ₁ k) (hτ₂ k) (ha₁ k) (ha₂ k)
    choose n τ b hτ hb hbd hhold hgain using hcomb
    have hbd' (k j : ℕ) (hj : j < n k) : ∃ C : ℝ, ∀ ω, ‖b k j ω‖ ≤ C := by
      have hC₁ : ∀ i : Fin (n₁ k), ∃ C : ℝ, ∀ ω, ‖a₁ k i.val ω‖ ≤ C :=
        fun i ↦ hb₁ k i.val i.isLt
      have hC₂ : ∀ i : Fin (n₂ k), ∃ C : ℝ, ∀ ω, ‖a₂ k i.val ω‖ ≤ C :=
        fun i ↦ hb₂ k i.val i.isLt
      choose C₁ hC₁ using hC₁
      choose C₂ hC₂ using hC₂
      refine ⟨∑ i, C₁ i + ∑ i, C₂ i, fun ω ↦ (hbd k j hj ω).trans (add_le_add ?_ ?_)⟩
      · rw [← Fin.sum_univ_eq_sum_range (f := fun i ↦ ‖a₁ k i ω‖)]
        exact Finset.sum_le_sum fun i _ ↦ hC₁ i ω
      · rw [← Fin.sum_univ_eq_sum_range (f := fun i ↦ ‖a₂ k i ω‖)]
        exact Finset.sum_le_sum fun i _ ↦ hC₂ i ω
    have hHmeas : StronglyMeasurable (Function.uncurry H) :=
      hI.isStronglyPredictable.mono ℱ.predictable_le_prod
    refine ⟨n, τ, b, hτ, hb, hbd', fun ε hε ↦ ?_, ?_⟩
    · refine tendsto_measure_lintegral_add_sq t (fun k ω ↦ ?_) (fun k ω s ↦ ?_) hE₁ hE₂ hε
      · have hK : Measurable (fun s ↦ Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω) := by
          simp only [Finance.simpleHolding_def]
          exact Finset.measurable_sum _ fun _ _ ↦ measurable_const.indicator measurableSet_Ioc
        exact hK.sub (hHmeas.comp_measurable measurable_prodMk_right).measurable
      · rw [hhold k s ω]
        ring
    · simpa only [funext fun k ↦ funext fun ω ↦ hgain k W t ω] using hL₁.add hL₂

/-- Itô integrals scale linearly with real constants. -/
theorem const_mul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (fun t ω ↦ c * H t ω) (fun t ω ↦ c * I t ω) where
  isStronglyPredictable := hI.isStronglyPredictable.const_mul c
  ae_continuous := hI.ae_continuous.mono fun _ hω ↦ continuous_const.mul hω
  approx t := by
    obtain ⟨n, τ, a, hτ, ha, hb, hE, hL⟩ := hI.approx t
    refine ⟨n, τ, fun k ↦ c • a k, hτ,
      fun k j hj ↦ (ha k j hj).const_mul c,
      fun k j hj ↦ by
        obtain ⟨C, hC⟩ := hb k j hj
        exact ⟨‖c‖ * C, fun ω ↦ by
          simpa only [Pi.smul_apply, smul_eq_mul, norm_mul] using
            mul_le_mul_of_nonneg_left (hC ω) (norm_nonneg c)⟩,
      fun ε hε ↦ ?_, ?_⟩
    · by_cases hc : c = 0
      · subst hc
        simp_rw [Finance.simpleHolding_smul]
        simp [hε.not_ge]
      · have hc2pos : 0 < ‖c‖ₑ ^ 2 := ENNReal.pow_pos (eNorm_pos.mpr hc) 2
        have hc2top : ‖c‖ₑ ^ 2 ≠ ∞ := ENNReal.pow_ne_top eNorm_ne_top
        have hε' : 0 < ε / ‖c‖ₑ ^ 2 := by
          by_cases htop : ε = ∞
          · simp [htop, hc2top]
          · exact ENNReal.div_pos hε.ne' hc2top
        convert hE (ε / ‖c‖ₑ ^ 2) hε' using 2 with k
        congr 1
        ext ω
        have hscale : ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (c • a k) s ω - c * H s ω‖ₑ ^ 2
            ∂timeMeasure t =
            ‖c‖ₑ ^ 2 * ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
              ∂timeMeasure t := by
          have hpt (s : ℝ≥0) :
              ‖Finance.simpleHolding (τ k) (n k) (c • a k) s ω - c * H s ω‖ₑ ^ 2 =
                ‖c‖ₑ ^ 2 * ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 := by
            rw [Finance.simpleHolding_smul, ← mul_sub, eNorm_mul, mul_pow]
          simp_rw [hpt]
          exact lintegral_const_mul' _ _ hc2top
        simp only [mem_ofPred_eq, hscale, ENNReal.div_le_iff_le_mul (.inl hc2pos.ne') (.inl hc2top),
          mul_comm]
    · have hpt : (fun k ↦ Finance.simpleGains (τ k) (n k) (c • a k) W t) =
          fun k ω ↦ c * Finance.simpleGains (τ k) (n k) (a k) W t ω :=
        funext fun k ↦ funext fun ω ↦ Finance.simpleGains_smul (τ k) (n k) c (a k) W t ω
      rw [hpt]
      simpa only [smul_eq_mul] using hL.const_smul c

/-- Negating the integrand negates its Itô integral. -/
theorem neg (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (fun t ω ↦ -H t ω) (fun t ω ↦ -I t ω) := by
  simpa only [neg_one_mul] using hI.const_mul (-1)

/-- Subtracting two integrands subtracts their Itô integrals. -/
theorem sub (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (fun t ω ↦ H t ω - K t ω) (fun t ω ↦ I t ω - J t ω) := by
  simpa only [sub_eq_add_neg] using hI.add hJ.neg

end IsItoIntegral

/-! ### Uniqueness and integrand congruence against a filtered pre-Brownian motion -/

namespace IsFilteredPreBrownianReal

/-- If a sequence of bounded left-measurable simple holdings tends to zero in pathwise square
energy in probability on `(0, t]`, then its elementary gains against a filtered pre-Brownian
motion tend to zero in probability at `t`. No path continuity of `W` is required. -/
theorem tendstoInMeasure_simpleGains_of_energy (hW : IsFilteredPreBrownianReal ℱ W P) (t : ℝ≥0)
    {n : ℕ → ℕ} {τ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (n k)))
    (ha : ∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j))
    (henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0)) :
    TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t) atTop (fun _ ↦ 0) := by
  -- Clip each grid at t and zero heights on intervals starting at or after t so left-endpoint
  -- measurability is preserved without peeking into the future.
  let σ (k j : ℕ) : ℝ≥0 := min (τ k j) t
  let c (k j : ℕ) : Ω → ℝ := if τ k j < t then a k j else 0
  have hσ (k : ℕ) : MonotoneOn (σ k) (Iic (n k)) :=
    fun i hi j hj hij ↦ min_le_min_right t (hτ k hi hj hij)
  have hc (k j : ℕ) (hj : j < n k) : StronglyMeasurable[ℱ (σ k j)] (c k j) := by
    by_cases hlt : τ k j < t
    · have hσeq : σ k j = τ k j := min_eq_left hlt.le
      rw [hσeq]
      simpa only [c, hlt, ite_true] using ha k j hj
    · simpa only [c, hlt, ite_false] using
        (stronglyMeasurable_zero : StronglyMeasurable[ℱ (σ k j)] (fun _ : Ω ↦ (0 : ℝ)))
  have hgain (k : ℕ) (ω : Ω) :
      (∑ j ∈ range (n k), c k j ω * (W (σ k (j + 1)) ω - W (σ k j) ω)) =
        Finance.simpleGains (τ k) (n k) (a k) W t ω := by
    rw [Finance.simpleGains_def]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' := mem_range.mp hj
    by_cases hlt : τ k j < t
    · simp [c, σ, hlt]
    · have hle : t ≤ τ k j := not_lt.mp hlt
      have hle' : t ≤ τ k (j + 1) :=
        hle.trans (hτ k (mem_Iic.mpr hj'.le) (mem_Iic.mpr hj') (Nat.le_succ j))
      simp [c, σ, hlt, min_eq_right hle, min_eq_right hle']
  have henergy_eq (k : ℕ) (ω : Ω) :
      ENNReal.ofReal (elementaryEnergy (σ k) (c k) (n k) ω) =
        ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω‖ₑ ^ 2 ∂timeMeasure t := by
    rw [Finance.lintegral_enorm_sq_simpleHolding_timeMeasure (hτ k), elementaryEnergy_def,
      ENNReal.ofReal_sum_of_nonneg (fun j hj ↦ mul_nonneg (sq_nonneg _)
        (sub_nonneg.mpr (NNReal.coe_le_coe.mpr
          (hσ k (mem_Iic.mpr (mem_range.mp hj).le) (mem_Iic.mpr (mem_range.mp hj))
            (Nat.le_succ j)))))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hlt : τ k j < t
    · simp only [c, σ, hlt, ite_true, min_eq_left hlt.le]
      rw [ENNReal.ofReal_mul (sq_nonneg _), ← sq_abs (a k j ω), ENNReal.ofReal_pow (abs_nonneg _),
        ← Real.norm_eq_abs, ofReal_norm]
    · have hle : t ≤ τ k j := not_lt.mp hlt
      have hsub : ((min (τ k (j + 1)) t : ℝ≥0) : ℝ) - (τ k j : ℝ) ≤ 0 :=
        sub_nonpos.mpr (NNReal.coe_le_coe.mpr ((min_le_right _ _).trans hle))
      simp only [c, hlt, ite_false, Pi.zero_apply, zero_pow two_ne_zero, zero_mul,
        ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hsub, mul_zero]
  have hE : TendstoInMeasure P (fun k ↦ elementaryEnergy (σ k) (c k) (n k)) atTop (fun _ ↦ 0) := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    convert henergy (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε) using 2 with k
    congr 1
    ext ω
    simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (elementaryEnergy_nonneg (hσ k) ω), ← henergy_eq k ω,
      ENNReal.ofReal_le_ofReal_iff (elementaryEnergy_nonneg (hσ k) ω)]
  simpa only [funext fun k ↦ funext fun ω ↦ hgain k ω] using
    hW.tendstoInMeasure_sum_mul_sub_of_energy hσ hc hE

/-- At a fixed horizon `t`, any limit in probability of elementary gains whose left-measurable
simple holdings converge to `H` in pathwise square energy in probability agrees almost surely
with every Itô integral of `H`. Neither boundedness of the heights nor path continuity of `W`
is required. -/
theorem ae_eq_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0} {Y : Ω → ℝ}
    {n₂ : ℕ → ℕ} {τ₂ : ℕ → ℕ → ℝ≥0} {a₂ : ℕ → ℕ → Ω → ℝ}
    (hτ₂ : ∀ k, MonotoneOn (τ₂ k) (Iic (n₂ k)))
    (ha₂ : ∀ k j, j < n₂ k → StronglyMeasurable[ℱ (τ₂ k j)] (a₂ k j))
    (hE₂ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ₂ k) (n₂ k) (a₂ k) s ω - H s ω‖ₑ ^ 2
        ∂timeMeasure t}) atTop (𝓝 0))
    (hL₂ : TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ₂ k) (n₂ k) (a₂ k) W t) atTop Y) :
    I t =ᵐ[P] Y := by
  obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, -, hE₁, hL₁⟩ := hI.approx t
  have hcomb (k : ℕ) := exists_simpleHolding_add_common (a₂ := (-1 : ℝ) • a₂ k)
    (hτ₁ k) (hτ₂ k) (ha₁ k) (fun j hj ↦ (ha₂ k j hj).const_mul (-1))
  choose n τ b hτ hb _ hhold hgain using hcomb
  have hHmeas : StronglyMeasurable (Function.uncurry H) :=
    hI.isStronglyPredictable.mono ℱ.predictable_le_prod
  have hE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (b k) s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0) := by
    intro ε hε
    have hE₂' : ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun k ↦ P {ω | δ ≤
        ∫⁻ s, ‖H s ω - Finance.simpleHolding (τ₂ k) (n₂ k) (a₂ k) s ω‖ₑ ^ 2 ∂timeMeasure t})
        atTop (𝓝 0) := fun δ hδ ↦ by
      simpa only [eNorm_sub_rev] using hE₂ δ hδ
    refine tendsto_measure_lintegral_add_sq t (fun k ω ↦ ?_) (fun k ω s ↦ ?_) hE₁ hE₂' hε
    · have hK₁ : Measurable (fun s ↦ Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω) := by
        simp only [Finance.simpleHolding_def]
        exact Finset.measurable_sum _ fun _ _ ↦ measurable_const.indicator measurableSet_Ioc
      exact hK₁.sub (hHmeas.comp_measurable measurable_prodMk_right).measurable
    · rw [hhold k s ω, Finance.simpleHolding_smul]
      ring
  have hdiff0 := hW.tendstoInMeasure_simpleGains_of_energy t hτ hb hE
  have hdiffIY : TendstoInMeasure P
      (fun k ↦ Finance.simpleGains (τ k) (n k) (b k) W t) atTop (fun ω ↦ I t ω - Y ω) := by
    have hpt (k : ℕ) (ω : Ω) : Finance.simpleGains (τ k) (n k) (b k) W t ω =
        Finance.simpleGains (τ₁ k) (n₁ k) (a₁ k) W t ω +
          (-1 : ℝ) * Finance.simpleGains (τ₂ k) (n₂ k) (a₂ k) W t ω := by
      rw [hgain k W t ω, Finance.simpleGains_smul]
    simpa only [funext fun k ↦ funext fun ω ↦ hpt k ω, smul_eq_mul, neg_one_mul,
      ← sub_eq_add_neg] using hL₁.add (hL₂.const_smul (-1 : ℝ))
  filter_upwards [tendstoInMeasure_ae_unique hdiffIY hdiff0] with ω hω
  exact sub_eq_zero.mp hω

/-- **Uniqueness of the Itô integral.** Against a filtered pre-Brownian motion, any two Itô
integrals of the same integrand are indistinguishable. Path continuity of `W` is not needed. -/
theorem isItoIntegral_unique (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) :
    I ≡ᵐ[P] J := by
  refine indist_of_ae_eq_of_ae_continuous (fun t ↦ ?_) hI.ae_continuous hJ.ae_continuous
  obtain ⟨n, τ, a, hτ, ha, -, hE, hL⟩ := hJ.approx t
  exact hW.ae_eq_of_isItoIntegral hI hτ ha hE hL

/-- **Product-a.e. integrand congruence.** Against a filtered pre-Brownian motion, Itô
integrals of predictable integrands that agree `dt × P`-almost everywhere on every finite
horizon are indistinguishable. Neither path continuity of `W` nor a separate local-energy
assumption is required. -/
theorem isItoIntegral_congr (hW : IsFilteredPreBrownianReal ℱ W P)
    (hHK : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure T).prod P] Function.uncurry K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    I ≡ᵐ[P] J := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact hW.isItoIntegral_unique (hI.congr_integrand hJ.isStronglyPredictable hHK) hJ

end IsFilteredPreBrownianReal

end TauCeti.Probability
