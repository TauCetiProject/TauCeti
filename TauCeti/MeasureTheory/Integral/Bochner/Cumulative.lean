/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Cumulative Bochner integrals on ordered spaces

An integrable function has a bounded-variation cumulative integral. If the measure has no
atoms at singletons, both its cumulative integral over `(-∞, t]` and its tail integral over
`(t, ∞)` are continuous. These statements apply in particular to nonnegative real time, without
extending the integrand to negative times.

For a real-valued function `f` integrable on `(t, ∞)` with respect to an `SFinite` measure
vanishing on singletons on a second-countable linear order, exchanging the order of integration
over `t < s < u` yields the power and exponential identities for the tail `G s = ∫ u in Ioi s, f u`:

* `IntegrableOn.integral_Ioi_mul_pow_integral_Ioi`:
  `∫ s in Ioi t, f s * (G s) ^ k = (G t) ^ (k + 1) / (k + 1)`, requiring neither continuity nor a
  sign condition on `f`.
* `IntegrableOn.mul_integral_Ioi_mul_exp_integral_Ioi`:
  `c * ∫ s in Ioi t, f s * exp (c * G s) = exp (c * G t) - 1` for every `c : ℝ`.
-/

public section

open Set Filter
open scoped Topology

namespace MeasureTheory

variable {ι E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [MeasurableSpace ι] [OpensMeasurableSpace ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure ι} {f : ι → E}

/-- The cumulative Bochner integral of an integrable function is continuous for a measure
vanishing on singletons. -/
theorem Integrable.continuous_integral_Iic [FirstCountableTopology ι] [NullSingletonClass μ]
    (hf : Integrable f μ) :
    Continuous (fun t => ∫ s in Iic t, f s ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro t
  simp_rw [← integral_indicator measurableSet_Iic]
  apply continuousAt_of_dominated (bound := fun s => ‖f s‖)
  · exact Eventually.of_forall fun u => hf.aestronglyMeasurable.indicator measurableSet_Iic
  · exact Eventually.of_forall fun u => ae_of_all _ fun s => norm_indicator_le_norm_self _ _
  · exact hf.norm
  · have hne : ∀ᵐ s ∂μ, s ≠ t := by
      simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using measure_singleton t
    filter_upwards [hne] with s hs
    rcases lt_or_gt_of_ne hs with hst | hts
    · apply (continuousAt_const (y := f s)).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hst] with u hu
      simp [hu.le]
    · apply (continuousAt_const (y := (0 : E))).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hts] with u hu
      simp [not_le.mpr hu]

/-- The total variation of a cumulative Bochner integral is bounded by the integral of the
norm. Atoms are allowed. -/
theorem Integrable.eVariationOn_integral_Iic_le (hf : Integrable f μ) :
    eVariationOn (fun t => ∫ s in Iic t, f s ∂μ) univ ≤
      ENNReal.ofReal (∫ s, ‖f s‖ ∂μ) := by
  simp only [eVariationOn, iSup_le_iff]
  rintro ⟨n, u, hu, -⟩
  have hcell (i : ℕ) :
      edist (∫ s in Iic (u (i + 1)), f s ∂μ) (∫ s in Iic (u i), f s ∂μ) ≤
        ENNReal.ofReal ((∫ s in Iic (u (i + 1)), ‖f s‖ ∂μ) -
          ∫ s in Iic (u i), ‖f s‖ ∂μ) := by
    rw [eDist_eq_eNorm_sub, ← ofReal_norm, ← setIntegral_sdiff measurableSet_Iic
      hf.integrableOn (Iic_subset_Iic.mpr (hu (Nat.le_succ i))),
      ← setIntegral_sdiff measurableSet_Iic hf.norm.integrableOn
        (Iic_subset_Iic.mpr (hu (Nat.le_succ i)))]
    exact ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)
  calc
    _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal
        ((∫ s in Iic (u (i + 1)), ‖f s‖ ∂μ) - ∫ s in Iic (u i), ‖f s‖ ∂μ) :=
      Finset.sum_le_sum fun i _ => hcell i
    _ = ENNReal.ofReal ((∫ s in Iic (u n), ‖f s‖ ∂μ) -
        ∫ s in Iic (u 0), ‖f s‖ ∂μ) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · exact congrArg ENNReal.ofReal (Finset.sum_range_sub
          (fun i => ∫ s in Iic (u i), ‖f s‖ ∂μ) n)
      · intro i _
        exact sub_nonneg.mpr (setIntegral_mono_set hf.norm.integrableOn
          (ae_of_all _ fun s => norm_nonneg _)
          (ae_of_all _ (Iic_subset_Iic.mpr (hu (Nat.le_succ i)))))
    _ ≤ ENNReal.ofReal (∫ s, ‖f s‖ ∂μ) := by
      apply ENNReal.ofReal_le_ofReal
      exact (sub_le_self _ (integral_nonneg fun s => norm_nonneg _)).trans
        (integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun s => norm_nonneg _)
          hf.norm)

/-- A path integrable on a finite horizon has a continuous accumulated integral throughout
that horizon for a measure vanishing on singletons. -/
theorem IntegrableOn.continuousOn_integral_Ioc [FirstCountableTopology ι]
    [NullSingletonClass μ] {a b : ι} (hf : IntegrableOn f (Ioc a b) μ) :
    ContinuousOn (fun t => ∫ s in Ioc a t, f s ∂μ) (Iic b) := by
  refine hf.continuous_integral_Iic.continuousOn.congr ?_
  intro t ht
  simp only [Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioc_of_le ht]

/-- The variation of an accumulated integral on a finite horizon is bounded by its pathwise
integral norm. No atomlessness or integrability outside the horizon is required. -/
theorem IntegrableOn.eVariationOn_integral_Ioc_le {a b : ι}
    (hf : IntegrableOn f (Ioc a b) μ) :
    eVariationOn (fun t => ∫ s in Ioc a t, f s ∂μ) (Iic b) ≤
      ENNReal.ofReal (∫ s in Ioc a b, ‖f s‖ ∂μ) := by
  have heq : EqOn (fun t => ∫ s in Iic t, f s ∂μ.restrict (Ioc a b))
      (fun t => ∫ s in Ioc a t, f s ∂μ) (Iic b) := by
    intro t ht
    simp only [Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioc_of_le ht]
  rw [← eVariationOn.congr heq]
  exact (eVariationOn.mono _ (subset_univ _)).trans hf.eVariationOn_integral_Iic_le

/-- The tail Bochner integral of an integrable function is continuous for a measure vanishing on
singletons. -/
theorem Integrable.continuous_integral_Ioi [FirstCountableTopology ι] [NullSingletonClass μ]
    (hf : Integrable f μ) :
    Continuous (fun t => ∫ s in Ioi t, f s ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro t
  simp_rw [← integral_indicator measurableSet_Ioi]
  apply continuousAt_of_dominated (bound := fun s => ‖f s‖)
  · exact Eventually.of_forall fun u => hf.aestronglyMeasurable.indicator measurableSet_Ioi
  · exact Eventually.of_forall fun u => ae_of_all _ fun s => norm_indicator_le_norm_self _ _
  · exact hf.norm
  · have hne : ∀ᵐ s ∂μ, s ≠ t := by
      simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using measure_singleton t
    filter_upwards [hne] with s hs
    rcases lt_or_gt_of_ne hs with hst | hts
    · apply (continuousAt_const (y := (0 : E))).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hst] with u hu
      exact indicator_of_notMem (not_lt.mpr (mem_Ioi.mp hu).le) _
    · apply (continuousAt_const (y := f s)).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hts] with u hu
      exact indicator_of_mem (mem_Ioi.mpr hu) _

/-- A function integrable on `(a, ∞)` has a continuous tail integral on `[a, ∞)` for a measure
vanishing on singletons. -/
theorem IntegrableOn.continuousOn_integral_Ioi [FirstCountableTopology ι]
    [NullSingletonClass μ] {a : ι} (hf : IntegrableOn f (Ioi a) μ) :
    ContinuousOn (fun t => ∫ s in Ioi t, f s ∂μ) (Ici a) := by
  refine hf.continuous_integral_Ioi.continuousOn.congr ?_
  intro t ht
  simp only [Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_self_of_subset_left (Ioi_subset_Ioi ht)]

section TailIdentities

variable {g : ι → ℝ} {t : ι}

omit [TopologicalSpace ι] [OrderTopology ι] [OpensMeasurableSpace ι] in
private lemma norm_integral_Ioi_le_of_le (hg : IntegrableOn g (Ioi t) μ) {s : ι} (hts : t ≤ s) :
    ‖∫ u in Ioi s, g u ∂μ‖ ≤ ∫ u in Ioi t, ‖g u‖ ∂μ :=
  (norm_integral_le_integral_norm _).trans <|
    setIntegral_mono_set hg.norm (ae_of_all _ fun _ => norm_nonneg _)
      (ae_of_all _ (Ioi_subset_Ioi hts))

private lemma integral_Iio_restrict_Ioi_eq_sub [NullSingletonClass μ]
    (hg : IntegrableOn g (Ioi t) μ) {u : ι} (htu : t < u) :
    ∫ s in Iio u, g s ∂(μ.restrict (Ioi t)) =
      (∫ s in Ioi t, g s ∂μ) - ∫ s in Ioi u, g s ∂μ := by
  rw [setIntegral_congr_set Iio_ae_eq_Iic]
  have hsplit := integral_add_compl (s := Iic u) measurableSet_Iic hg
  simp only [compl_Iic] at hsplit
  have hrest : ∫ s in Ioi u, g s ∂(μ.restrict (Ioi t)) = ∫ s in Ioi u, g s ∂μ := by
    simp only [Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_self_of_subset_left (Ioi_subset_Ioi htu.le)]
  linarith

/-- For `g` integrable on `(t, ∞)` under a measure vanishing on singletons, every product
`s ↦ g s * (∫ u in Ioi s, g u ∂μ) ^ k` is integrable on `(t, ∞)`. -/
theorem IntegrableOn.integrableOn_mul_pow_integral_Ioi [FirstCountableTopology ι]
    [NullSingletonClass μ] (hg : IntegrableOn g (Ioi t) μ) (k : ℕ) :
    IntegrableOn (fun s => g s * (∫ u in Ioi s, g u ∂μ) ^ k) (Ioi t) μ := by
  have hmeas : AEStronglyMeasurable (fun s => (∫ u in Ioi s, g u ∂μ) ^ k)
      (μ.restrict (Ioi t)) :=
    ((hg.continuousOn_integral_Ioi.mono Ioi_subset_Ici_self).pow k).aestronglyMeasurable
      measurableSet_Ioi
  refine hg.mul_bdd (c := (∫ u in Ioi t, ‖g u‖ ∂μ) ^ k) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [norm_pow]
  gcongr
  exact norm_integral_Ioi_le_of_le hg hs.le

/-- **Power identity for tail integrals.** For a real-valued function `g` integrable on `(t, ∞)`
with respect to an `SFinite` measure vanishing on singletons on a second-countable linear order,
`∫ s in Ioi t, g s * (∫ u in Ioi s, g u ∂μ) ^ k ∂μ = (∫ s in Ioi t, g s ∂μ) ^ (k + 1) / (k + 1)`.
Neither continuity nor nonnegativity of `g` is needed. -/
theorem IntegrableOn.integral_Ioi_mul_pow_integral_Ioi [SecondCountableTopology ι]
    [SFinite μ] [NullSingletonClass μ] (hg : IntegrableOn g (Ioi t) μ) (k : ℕ) :
    ∫ s in Ioi t, g s * (∫ u in Ioi s, g u ∂μ) ^ k ∂μ =
      (∫ s in Ioi t, g s ∂μ) ^ (k + 1) / (k + 1) := by
  induction k generalizing t with
  | zero => simp
  | succ m ih =>
    set G : ι → ℝ := fun s => ∫ u in Ioi s, g u ∂μ
    set ν : Measure ι := μ.restrict (Ioi t)
    have hgm : Integrable (fun u => g u * G u ^ m) ν := hg.integrableOn_mul_pow_integral_Ioi m
    have hgm1 : Integrable (fun u => g u * G u ^ (m + 1)) ν :=
      hg.integrableOn_mul_pow_integral_Ioi (m + 1)
    set H : ι × ι → ℝ := {p : ι × ι | p.1 < p.2}.indicator fun p => g p.1 * (g p.2 * G p.2 ^ m)
    have hH : Integrable H (ν.prod ν) :=
      (hg.smul_prod hgm).indicator (isOpen_lt continuous_fst continuous_snd).measurableSet
    have hfub : ∫ s, (∫ u, H (s, u) ∂ν) ∂ν = ∫ u, (∫ s, H (s, u) ∂ν) ∂ν :=
      (integral_prod H hH).symm.trans (integral_prod_symm H hH)
    have hlhs : ∫ s, (∫ u, H (s, u) ∂ν) ∂ν =
        (∫ s in Ioi t, g s * G s ^ (m + 1) ∂μ) / (m + 1 : ℝ) := by
      have hslice : ∀ᵐ s ∂ν, ∫ u, H (s, u) ∂ν = g s * G s ^ (m + 1) / (m + 1 : ℝ) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hcongr : (fun u => H (s, u)) =
            (Ioi s).indicator (fun u => g s * (g u * G u ^ m)) := by
          ext u; by_cases hsu : s < u <;> simp [H, hsu]
        rw [hcongr, integral_indicator measurableSet_Ioi, integral_const_mul,
          Measure.restrict_restrict measurableSet_Ioi,
          inter_eq_self_of_subset_left (Ioi_subset_Ioi hs.le),
          ih (hg.mono_set (Ioi_subset_Ioi hs.le)), mul_div_assoc]
      rw [integral_congr_ae hslice, integral_div]
    have hrhs : ∫ u, (∫ s, H (s, u) ∂ν) ∂ν =
        G t * (G t ^ (m + 1) / (m + 1 : ℝ)) - ∫ u in Ioi t, g u * G u ^ (m + 1) ∂μ := by
      have hslice : ∀ᵐ u ∂ν,
          ∫ s, H (s, u) ∂ν = G t * (g u * G u ^ m) - g u * G u ^ (m + 1) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hcongr : (fun s => H (s, u)) =
            (Iio u).indicator (fun s => g s * (g u * G u ^ m)) := by
          ext s; by_cases hsu : s < u <;> simp [H, hsu]
        rw [hcongr, integral_indicator measurableSet_Iio, integral_mul_const,
          integral_Iio_restrict_Ioi_eq_sub hg hu]
        ring
      rw [integral_congr_ae hslice, integral_sub (hgm.const_mul _) hgm1,
        integral_const_mul, show ∫ x, g x * G x ^ m ∂ν = ∫ u in Ioi t, g u * G u ^ m ∂μ from rfl,
        ih hg]
    rw [hlhs, hrhs] at hfub
    have hm1 : (m + 1 : ℝ) ≠ 0 := by positivity
    have hm2 : (m : ℝ) + 1 + 1 ≠ 0 := by positivity
    push_cast
    field_simp at hfub ⊢
    rw [← pow_succ'] at hfub
    linarith

/-- For `g` integrable on `(t, ∞)` under a measure vanishing on singletons,
`s ↦ g s * exp (c * ∫ u in Ioi s, g u ∂μ)` is integrable on `(t, ∞)` for every `c : ℝ`. -/
theorem IntegrableOn.integrableOn_mul_exp_integral_Ioi [FirstCountableTopology ι]
    [NullSingletonClass μ] (hg : IntegrableOn g (Ioi t) μ) (c : ℝ) :
    IntegrableOn (fun s => g s * Real.exp (c * ∫ u in Ioi s, g u ∂μ)) (Ioi t) μ := by
  have hmeas : AEStronglyMeasurable (fun s => Real.exp (c * ∫ u in Ioi s, g u ∂μ))
      (μ.restrict (Ioi t)) :=
    (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (hg.continuousOn_integral_Ioi.mono Ioi_subset_Ici_self)))
      |>.aestronglyMeasurable measurableSet_Ioi
  refine hg.mul_bdd (c := Real.exp (|c| * ∫ u in Ioi t, ‖g u‖ ∂μ)) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul]
  gcongr
  exact norm_integral_Ioi_le_of_le hg hs.le

/-- **Exponential identity for tail integrals.** For a real-valued function `g` integrable on
`(t, ∞)` with respect to an `SFinite` measure vanishing on singletons on a second-countable linear
order, and any `c : ℝ`,
`c * ∫ s in Ioi t, g s * exp (c * ∫ u in Ioi s, g u ∂μ) ∂μ = exp (c * ∫ s in Ioi t, g s ∂μ) - 1`. -/
theorem IntegrableOn.mul_integral_Ioi_mul_exp_integral_Ioi [SecondCountableTopology ι]
    [SFinite μ] [NullSingletonClass μ] (hg : IntegrableOn g (Ioi t) μ) (c : ℝ) :
    c * ∫ s in Ioi t, g s * Real.exp (c * ∫ u in Ioi s, g u ∂μ) ∂μ =
      Real.exp (c * ∫ s in Ioi t, g s ∂μ) - 1 := by
  set G : ι → ℝ := fun s => ∫ u in Ioi s, g u ∂μ
  set ν : Measure ι := μ.restrict (Ioi t)
  set M : ℝ := ∫ u in Ioi t, ‖g u‖ ∂μ
  have : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  set F : ℕ → ι → ℝ := fun k s => c ^ k / (Nat.factorial k : ℝ) * (g s * G s ^ k)
  have hF_int : ∀ k, Integrable (F k) ν := fun k =>
    (hg.integrableOn_mul_pow_integral_Ioi k).const_mul _
  have hF_sum : Summable fun k => ∫ s, ‖F k s‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _)
      (fun k => ?_) ((Real.summable_pow_div_factorial (|c| * M)).mul_left M)
    have hbound : ∀ᵐ s ∂ν, ‖F k s‖ ≤ |c| ^ k / (Nat.factorial k : ℝ) * (‖g s‖ * M ^ k) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      simp only [F, norm_mul, norm_div, norm_pow, Real.norm_eq_abs, Nat.abs_cast]
      gcongr
      exact norm_integral_Ioi_le_of_le hg hs.le
    calc ∫ s, ‖F k s‖ ∂ν
        ≤ ∫ s, |c| ^ k / (Nat.factorial k : ℝ) * (‖g s‖ * M ^ k) ∂ν :=
          integral_mono_ae (hF_int k).norm ((hg.norm.mul_const (M ^ k)).const_mul _) hbound
      _ = M * ((|c| * M) ^ k / (Nat.factorial k : ℝ)) := by
          rw [integral_const_mul, integral_mul_const, show ∫ x, ‖g x‖ ∂ν = M from rfl, mul_pow]
          ring
  have hexp_eq : ∀ s, g s * Real.exp (c * G s) = ∑' k, F k s := fun s => by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div, ← tsum_mul_left]
    exact tsum_congr fun k => by simp only [F, mul_pow]; ring
  rw [show ∫ s in Ioi t, g s * Real.exp (c * ∫ u in Ioi s, g u ∂μ) ∂μ = ∫ s, (∑' k, F k s) ∂ν from
      integral_congr_ae (ae_of_all _ hexp_eq),
    ← integral_tsum_of_summable_integral_norm hF_int hF_sum, ← tsum_mul_left]
  have hterm : ∀ k, c * ∫ s, F k s ∂ν =
      (c * G t) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := fun k => by
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    rw [show ∫ s, F k s ∂ν = c ^ k / (Nat.factorial k : ℝ) * ∫ s in Ioi t, g s * G s ^ k ∂μ from
        integral_const_mul _ _,
      hg.integral_Ioi_mul_pow_integral_Ioi k, Nat.factorial_succ]
    push_cast
    rw [mul_pow]; field_simp; ring
  simp_rw [hterm]
  have hexp_Gt : HasSum (fun k => (c * G t) ^ k / (Nat.factorial k : ℝ)) (Real.exp (c * G t)) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp (c * G t)
  have hshift := hexp_Gt.summable.tsum_eq_zero_add
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hshift
  linarith [hexp_Gt.tsum_eq]

end TailIdentities

end MeasureTheory
