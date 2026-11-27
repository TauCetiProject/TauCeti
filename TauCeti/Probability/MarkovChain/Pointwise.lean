/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Classification
public import TauCeti.Probability.MarkovChain.Coupling.Convergence
public import TauCeti.Probability.MarkovChain.Product.Basic
public import TauCeti.Probability.MarkovChain.Product.Limits
public import TauCeti.Probability.MarkovChain.Occupation.Bounds
public import TauCeti.Probability.MarkovChain.Occupation
public import TauCeti.Probability.Process.Occupation
public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
public import TauCeti.Analysis.SpecificLimits.MovingAverage
import TauCeti.MeasureTheory.Measure.Subtype
import TauCeti.Probability.MarkovChain.Transient.Occupation

/-!
# Pointwise decay at states with infinite mean return time

For an irreducible aperiodic chain, an infinite extended mean positive
return time at `y` implies that the time-`n` mass of `y` tends to zero from every initial
probability law. This includes null recurrent states and states with a positive chance
of never returning: the hypothesis uses an `ℝ≥0∞`-valued mean, with infinity on nonreturn.

The independent square chain gives two alternatives. Transience of `(y, y)` already
implies decay by summability of squared transition masses. In the recurrent case,
meeting-time coupling makes every fixed time shift asymptotically indistinguishable.
The uniform occupation bound and the occupation strong law then force pointwise decay.
The recurrent-square criterion is also exposed with a zero Cesàro return-mass hypothesis,
without an aperiodicity assumption on the original kernel.

Because the limit is zero on every cyclic subclass, aperiodicity is in fact unnecessary for
singleton decay: sampling at multiples of `κ.period y` preserves null recurrence
(`Kernel.IsNullRecurrent.pow_period`) and yields an aperiodic restriction on the communicating class
of `y` under `κ ^ κ.period y`, while transient states have summable transition masses directly.
Consequently, on any counting-measure-irreducible chain (periodic or aperiodic), the time-`n`
singleton mass at a null recurrent or non-positive-recurrent state tends to zero from every finite
initial law (`Kernel.IsNullRecurrent.tendsto_pow_comp_real_singleton`,
`Kernel.tendsto_pow_comp_real_singleton_of_not_isPositiveRecurrent`).

Only singleton convergence is asserted, not convergence in total variation to zero.
The non-positive-recurrent decay theorem transfers to arbitrary realizations of the chain through
their path laws.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.8,
  the independent-product and averaged-occupation proof of convergence.
-/

public section

open MeasureTheory ProbabilityTheory Filter TauCeti TauCeti.Probability
open scoped Topology ENNReal

namespace ProbabilityTheory.Kernel

section Aperiodic

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (κ : Kernel α α) [IsMarkovKernel κ]

/-- If the square chain is irreducible and recurrent, vanishing Cesàro return masses at `y`
force the singleton mass at `y` to vanish from every initial probability law. -/
theorem tendsto_pow_comp_real_singleton_of_parallelComp_isRecurrent
    [MeasurableEq α] [IsIrreducible Measure.count (κ ∥ₖ κ)]
    {z : α × α} (hz : (κ ∥ₖ κ).IsRecurrent z) {y : α}
    (hy : Tendsto (fun k : ℕ =>
      (∑ i ∈ Finset.range k, ((κ ^ (i + 1)) y).real {y}) / k) atTop (𝓝 0))
    (ν : Measure α) [IsProbabilityMeasure ν] :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
  have hshift (i : ℕ) : Tendsto (fun n : ℕ =>
      ((κ ^ (n + i)) ∘ₘ ν).real {y} - ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (κ.tendsto_tvDist_pow_comp_pow_add_comp_of_parallelComp_isRecurrent hz ν i)
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact abs_measureReal_sub_le_tvDist (measurableSet_singleton y)
  have hb : Tendsto (fun k : ℕ =>
      (1 + ∑ i ∈ Finset.range k, ((κ ^ (i + 1)) y).real {y}) / k) atTop (𝓝 0) := by
    simpa only [add_div, zero_add] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).add hy
  exact tendsto_zero_of_nonneg_of_sum_range_add_div_le
    (fun _ => measureReal_nonneg) hshift hb
    (fun n k _ => κ.sum_range_pow_comp_real_singleton_div_le ν y n k)

-- Pointwise decay at an infinite-mean state for an irreducible aperiodic Markov kernel.
private theorem tendsto_pow_comp_real_singleton_of_isAperiodic_of_meanReturnTime_eq_top
    [IsIrreducible Measure.count κ] (hκ : κ.IsAperiodic) {y : α}
    (hy : κ.meanReturnTime y = ⊤) (ν : Measure α) [IsProbabilityMeasure ν] :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
  have := countable_of_isIrreducible_count (κ := κ)
  by_cases hr : (κ ∥ₖ κ).IsRecurrent (y, y)
  · let := hκ.isIrreducible_parallelComp hκ
    apply κ.tendsto_pow_comp_real_singleton_of_parallelComp_isRecurrent hr _ ν
    simpa only [hy, ENNReal.inv_top, ENNReal.toReal_zero] using
      κ.tendsto_cesaro_pow_real_singleton_self y
  · exact κ.tendsto_pow_comp_apply_singleton_of_parallelComp_return_lt_one ν
      (isTransient_iff_return_probability_lt_one.mp (isTransient_iff.mpr hr))

end Aperiodic

/-! ### Unconditional pointwise decay via period decomposition -/

section PeriodDecay

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

private theorem tendsto_pow_comp_real_singleton_of_isAperiodic_of_not_isPositiveRecurrent_finite
    {κ : Kernel α α} [IsMarkovKernel κ] [IsIrreducible Measure.count κ]
    (hκ : κ.IsAperiodic) {y : α} (hy : ¬ κ.IsPositiveRecurrent y)
    (ν : Measure α) [IsFiniteMeasure ν] :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
  have : Nonempty α := ⟨y⟩
  let m : FiniteMeasure α := ⟨ν, inferInstance⟩
  have hν : ν = (m.mass : ℝ≥0∞) • (m.normalize : Measure α) :=
    (congrArg (fun (μ : FiniteMeasure α) => (μ : Measure α)) m.self_eq_mass_smul_normalize).trans
      (Measure.coe_nnreal_smul m.mass (m.normalize : Measure α)).symm
  have hprob := κ.tendsto_pow_comp_real_singleton_of_isAperiodic_of_meanReturnTime_eq_top hκ
    (not_lt_top_iff.mp ((isPositiveRecurrent_iff κ y).not.mp hy)) (m.normalize : Measure α)
  have hscale (n : ℕ) : ((κ ^ n) ∘ₘ ν).real {y} =
      ν.real Set.univ * ((κ ^ n) ∘ₘ (m.normalize : Measure α)).real {y} := by
    rw [hν, Measure.comp_smul]
    simp [Measure.real, smul_apply, ENNReal.toReal_mul, m]
  simp_rw [hscale]
  simpa only [mul_zero] using (tendsto_const_nhds (x := ν.real Set.univ)).mul hprob

private theorem pow_period_mul_comp_restrict_compl_singleton_eq_zero
    {κ : Kernel α α} [IsMarkovKernel κ] [IsIrreducible Measure.count κ]
    (y : α) (μ : Measure α) (q : ℕ) :
    (((κ ^ κ.period y) ^ q) ∘ₘ (μ.restrict ((κ ^ κ.period y).communicatingClass y)ᶜ)) {y} = 0 := by
  have := countable_of_isIrreducible_count (κ := κ)
  set d := κ.period y
  set η := κ ^ d
  set s := η.communicatingClass y
  have hs : MeasurableSet s := η.measurableSet_communicatingClass y
  have hzero_outside : ∀ z ∈ sᶜ, (η ^ q) z {y} = 0 := fun z hz => by
    refine nonpos_iff_eq_zero.mp (not_lt.mp fun hpos => hz ?_)
    obtain ⟨a, ha⟩ := exists_pos_pow_apply_singleton (κ := κ) y z
    have hpos' : 0 < (κ ^ (d * q)) z {y} := by rwa [pow_mul]
    have hdvd_sum : d ∣ a + d * q := Classical.not_not.mp
      (mt pow_apply_singleton_self_eq_zero_of_not_period_dvd (pow_add_apply_pos ha hpos').ne')
    obtain ⟨m, rfl⟩ := (Nat.dvd_add_left (dvd_mul_right d q)).mp hdvd_sum
    have hyz : η.Reaches y z := (reaches_def y z).mpr ⟨m, by rwa [← pow_mul]⟩
    have hzy : η.Reaches z y := (reaches_def z y).mpr ⟨q, hpos⟩
    exact (mem_communicatingClass_iff y z).mpr ((communicates_def y z).mpr ⟨hyz, hzy⟩)
  rw [Measure.bind_apply (measurableSet_singleton y) (η ^ q).aemeasurable]
  exact (lintegral_eq_zero_iff ((η ^ q).measurable_coe (measurableSet_singleton y))).mpr
    ((ae_restrict_iff' hs.compl).mpr (Eventually.of_forall hzero_outside))

private theorem tendsto_pow_period_mul_comp_real_singleton_of_isNullRecurrent
    {κ : Kernel α α} [IsMarkovKernel κ] [IsIrreducible Measure.count κ]
    {y : α} (hy : κ.IsNullRecurrent y) (μ : Measure α) [IsFiniteMeasure μ] :
    Tendsto (fun q : ℕ => ((κ ^ (κ.period y * q)) ∘ₘ μ).real {y}) atTop (𝓝 0) := by
  have := countable_of_isIrreducible_count (κ := κ)
  set d := κ.period y
  set η := κ ^ d
  have hη : η.IsNullRecurrent y := hy.pow_period
  set s := η.communicatingClass y
  have hs : MeasurableSet s := η.measurableSet_communicatingClass y
  have hclosed : η.IsClosedSet s := hη.isRecurrent.isClosedSet_communicatingClass
  have : IsMarkovKernel (η.subtype hs) := (isMarkovKernel_subtype_iff_isClosedSet hs).mpr hclosed
  have : IsIrreducible Measure.count (η.subtype hs) :=
    hclosed.isIrreducible_subtype_communicatingClass hs
  let y_s : s := ⟨y, mem_communicatingClass_self y⟩
  have haper : (η.subtype hs).IsAperiodic := by
    rw [isAperiodic_iff_period_eq_one y_s, period_subtype hs hclosed]
    exact period_pow_period κ y
  have hy_s : ¬ (η.subtype hs).IsPositiveRecurrent y_s := by
    rw [isPositiveRecurrent_subtype_iff hs y_s]
    exact hη.not_isPositiveRecurrent
  let μ_s : Measure s := μ.comap Subtype.val
  have : IsFiniteMeasure μ_s := μ.isFiniteMeasure_comap_subtype_coe (measure_ne_top μ s)
  have heq (q : ℕ) : ((κ ^ (d * q)) ∘ₘ μ).real {y} =
      (((η.subtype hs) ^ q) ∘ₘ μ_s).real {y_s} := by
    rw [pow_mul]
    conv_lhs => rw [← Measure.restrict_add_restrict_compl hs (μ := μ)]
    rw [Measure.comp_add, measureReal_def, add_apply,
      pow_period_mul_comp_restrict_compl_singleton_eq_zero y μ q, add_zero,
      ← map_comap_subtypeVal hs μ, ← map_pow_comp_subtype η hs hclosed q μ_s,
      (MeasurableEmbedding.subtypeVal hs).map_apply]
    have hpre : (Subtype.val : s → α) ⁻¹' {y_s.val} = {y_s} := by
      rw [← Set.image_singleton, Subtype.coe_injective.preimage_image]
    rw [← measureReal_def]
    exact congrArg (((η.subtype hs) ^ q) ∘ₘ μ_s).real hpre
  simp_rw [heq]
  exact tendsto_pow_comp_real_singleton_of_isAperiodic_of_not_isPositiveRecurrent_finite
    haper hy_s μ_s

/-- **Pointwise decay at null recurrent states.** On a counting-measure-irreducible chain (periodic
or aperiodic), if `y` is null recurrent, then the time-`n` singleton mass at `y` tends to zero from
every finite initial measure. -/
theorem IsNullRecurrent.tendsto_pow_comp_real_singleton {κ : Kernel α α} [IsMarkovKernel κ]
    [IsIrreducible Measure.count κ] {y : α} (hy : κ.IsNullRecurrent y)
    (ν : Measure α) [IsFiniteMeasure ν] :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
  set d := κ.period y
  have hd : 0 < d := hy.isRecurrent.period_pos
  have hres (r : ℕ) : Tendsto (fun q : ℕ => ((κ ^ (d * q + r)) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
    have hcomp (q : ℕ) :
        (κ ^ (d * q + r)) ∘ₘ ν = (κ ^ (d * q)) ∘ₘ ((κ ^ r : Kernel α α) ∘ₘ ν) := by
      rw [pow_add, Measure.comp_assoc]
    simp_rw [hcomp]
    exact tendsto_pow_period_mul_comp_real_singleton_of_isNullRecurrent hy
      ((κ ^ r : Kernel α α) ∘ₘ ν)
  refine tendsto_def.mpr fun U hU => Set.mem_preimage.mp ?_
  have hall : ∀ᶠ n in atTop, ∀ r ∈ Finset.range d,
      ((κ ^ (d * (n / d) + r)) ∘ₘ ν).real {y} ∈ U :=
    (eventually_all_finset (Finset.range d)).mpr fun r _ =>
      ((hres r).comp (Nat.tendsto_div_const_atTop hd.ne')).eventually hU
  exact hall.mono fun n hn => by
    simpa only [Nat.div_add_mod] using hn (n % d) (Finset.mem_range.mpr (Nat.mod_lt n hd))

/-- **Pointwise decay at non-positive-recurrent states.** On a counting-measure-irreducible chain
(periodic or aperiodic), if `y` is not positive recurrent, then the time-`n` singleton mass at `y`
tends to zero from every finite initial measure. -/
theorem tendsto_pow_comp_real_singleton_of_not_isPositiveRecurrent
    (κ : Kernel α α) [IsMarkovKernel κ] [IsIrreducible Measure.count κ]
    {y : α} (hy : ¬ κ.IsPositiveRecurrent y)
    (ν : Measure α) [IsFiniteMeasure ν] :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
  rcases not_isPositiveRecurrent_iff.mp hy with ht | hn
  · simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp
        (κ.tendsto_pow_comp_apply_singleton_zero_of_return_lt_one
          (isTransient_iff_return_probability_lt_one.mp ht) ν)
  · exact hn.tendsto_pow_comp_real_singleton ν

end PeriodDecay

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

/-- On any realization of a counting-measure-irreducible chain (periodic or aperiodic) started from
a finite initial law, the time-`n` measure of occupying a non-positive-recurrent state tends to
zero. -/
theorem tendsto_measureReal_apply_eq_of_not_isPositiveRecurrent
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] {κ : Kernel α α} [IsMarkovKernel κ]
    [Kernel.IsIrreducible Measure.count κ] {ν : Measure α} [IsFiniteMeasure ν]
    {P : Measure Ω} {X : ℕ → Ω → α}
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    {y : α} (hy : ¬ κ.IsPositiveRecurrent y) :
    Tendsto (fun n : ℕ => P.real {ω | X n ω = y}) atTop (𝓝 0) := by
  have heq (n : ℕ) : P.real {ω | X n ω = y} = ((κ ^ n) ∘ₘ ν).real {y} :=
    (hX.eval_markovChainLaw ν κ n).measureReal_eq (measurableSet_singleton y)
  simp_rw [heq]
  exact κ.tendsto_pow_comp_real_singleton_of_not_isPositiveRecurrent hy ν

end ProbabilityTheory.HasLaw
