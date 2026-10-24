/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Probability.Distributions.Poisson.Basic
public import TauCeti.Probability.Distributions.Poisson.Measurability
public import TauCeti.MeasureTheory.Group.ConvolutionPower
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Compound Poisson distributions

This file uses convolution powers as the jump-count kernel of a compound Poisson distribution. Thus
`compoundPoissonMeasure r μ` first draws a Poisson count of rate `r`, then sums that many
independent jumps with law `μ`.

The core API records the Poisson mixture formula and the two degenerate cases: rate zero and jumps
concentrated at zero. These facts are the measure-theoretic foundation for later moment and
transform calculations. The real-valued measurable-set series converges absolutely and gives
singleton masses and a lower bound for the atom at zero.

The main results are that compound Poisson laws with a common jump law convolve by adding their
rates, and that on a second-countable real inner product space with its Borel σ-algebra the
characteristic function is `exp (r * (φ_μ t - 1))`. The rate-additivity proof works on an
arbitrary measurable additive monoid: the convolution powers satisfy
`μ^{∗(m + n)} = μ^{∗m} ∗ μ^{∗n}`, so mixing them commutes with convolution of the mixing laws on
`ℕ`, and the Poisson laws on `ℕ` add their rates.

## Main results

* `TauCeti.Probability.compoundPoissonMeasure_conv_compoundPoissonMeasure` — rates add under
  convolution at a fixed jump law;
* `TauCeti.Probability.charFun_compoundPoissonMeasure` — the characteristic function
  `exp (r * (φ_μ t - 1))`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed.,
  Wiley, 1968, §XII.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Nat MeasureTheory

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [AddMonoid α]

/-- The compound Poisson law with rate `r` and jump measure `μ`: mix the convolution powers of
`μ` against a Poisson-distributed number of jumps. -/
def compoundPoissonMeasure (r : ℝ≥0) (μ : Measure α) : Measure α :=
  (poissonMeasure r).bind μ.convolutionPower

/-- A compound Poisson law is the Poisson mixture of the convolution powers of its jump law. -/
theorem compoundPoissonMeasure_def (r : ℝ≥0) (μ : Measure α) :
    compoundPoissonMeasure r μ = (poissonMeasure r).bind μ.convolutionPower := (rfl)

/-- At a fixed jump measure, the compound Poisson law depends measurably on its rate. -/
@[fun_prop]
theorem measurable_compoundPoissonMeasure (μ : Measure α) :
    Measurable fun r : ℝ≥0 => compoundPoissonMeasure r μ := by
  exact (Measure.measurable_bind' Measurable.of_discrete).comp measurable_poissonMeasure

/-- The compound Poisson law is the Poisson-weighted sum of the convolution powers of its jump
measure. -/
theorem compoundPoissonMeasure_eq_sum (r : ℝ≥0) (μ : Measure α) :
    compoundPoissonMeasure r μ = Measure.sum fun n =>
      ENNReal.ofReal (exp (-r) * r ^ n / n !) • μ.convolutionPower n := by
  rw [compoundPoissonMeasure_def, poissonMeasure, Measure.bind_sum]
  · congr 1
    funext n
    rw [Measure.bind_smul _ _ Measurable.of_discrete.aemeasurable,
      Measure.dirac_bind Measurable.of_discrete]
  · exact Measurable.of_discrete.aemeasurable

/-- A compound Poisson law with a probability jump measure is a probability measure. -/
instance isProbabilityMeasure_compoundPoissonMeasure (r : ℝ≥0) (μ : Measure α)
    [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (compoundPoissonMeasure r μ) := by
  rw [compoundPoissonMeasure_def]
  exact MeasureTheory.isProbabilityMeasure_bind Measurable.of_discrete.aemeasurable
    (ae_of_all _ fun n => inferInstance)

/-- A compound Poisson law with an s-finite jump measure is s-finite. -/
instance sfinite_compoundPoissonMeasure (r : ℝ≥0) (μ : Measure α) [SFinite μ] :
    SFinite (compoundPoissonMeasure r μ) := by
  rw [compoundPoissonMeasure_eq_sum]
  infer_instance

/-- Integration against a compound Poisson law is the Poisson average of integration against its
convolution powers. -/
theorem lintegral_compoundPoissonMeasure (r : ℝ≥0) (μ : Measure α) (f : α → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, f x ∂compoundPoissonMeasure r μ =
      ∫⁻ n, ∫⁻ x, f x ∂μ.convolutionPower n ∂poissonMeasure r := by
  rw [compoundPoissonMeasure_def]
  exact Measure.lintegral_bind Measurable.of_discrete.aemeasurable
    hf.aemeasurable

/-- The mass assigned by a compound Poisson law to a measurable set is the Poisson average of
the masses assigned by its convolution powers. -/
theorem compoundPoissonMeasure_apply (r : ℝ≥0) (μ : Measure α) {s : Set α}
    (hs : MeasurableSet s) :
    compoundPoissonMeasure r μ s =
      ∫⁻ n, μ.convolutionPower n s ∂poissonMeasure r := by
  rw [compoundPoissonMeasure_def, Measure.bind_apply hs Measurable.of_discrete.aemeasurable]

/-- The measurable-set formula for a compound Poisson law as a Poisson-weighted series. -/
theorem compoundPoissonMeasure_apply_eq_tsum (r : ℝ≥0) (μ : Measure α) {s : Set α}
    (hs : MeasurableSet s) :
    compoundPoissonMeasure r μ s =
      ∑' n, ENNReal.ofReal (exp (-r) * r ^ n / n !) * μ.convolutionPower n s := by
  rw [compoundPoissonMeasure_eq_sum, Measure.sum_apply _ hs]
  simp_rw [Measure.smul_apply, smul_eq_mul]

/-- The Poisson-weighted series of convolution-power probabilities converges to the compound
probability of every measurable set. Its nonnegative terms also give absolute convergence. -/
theorem hasSum_compoundPoissonMeasure_real_apply (r : ℝ≥0) (μ : Measure α)
    [IsProbabilityMeasure μ] {s : Set α} (hs : MeasurableSet s) :
    HasSum (fun n : ℕ => (exp (-(r : ℝ)) * (r : ℝ) ^ n / n !) *
      (μ.convolutionPower n).real s) ((compoundPoissonMeasure r μ).real s) := by
  have hsum := (ENNReal.summable.hasSum_iff.mpr
    (compoundPoissonMeasure_apply_eq_tsum r μ hs).symm).toReal (measure_ne_top _ _)
  rw [← measureReal_def] at hsum
  convert hsum using 1
  funext n
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ← measureReal_def]

/-- Native singleton masses are the absolutely convergent Poisson-weighted series of the
singleton masses of the convolution powers. This applies in particular to `ℕ` and `ℤ` jumps. -/
theorem compoundPoissonMeasure_real_singleton [MeasurableSingletonClass α]
    (r : ℝ≥0) (μ : Measure α) [IsProbabilityMeasure μ] (k : α) :
    (compoundPoissonMeasure r μ).real {k} =
      ∑' n : ℕ, (exp (-(r : ℝ)) * (r : ℝ) ^ n / n !) *
        (μ.convolutionPower n).real {k} :=
  (hasSum_compoundPoissonMeasure_real_apply r μ (measurableSet_singleton k)).tsum_eq.symm

/-- The probability of no jumps gives a lower bound for the atom at zero. Nonempty sums can
also vanish, so equality need not hold for a general jump law. -/
theorem exp_neg_le_compoundPoissonMeasure_real_singleton_zero [MeasurableSingletonClass α]
    (r : ℝ≥0) (μ : Measure α) [IsProbabilityMeasure μ] :
    exp (-(r : ℝ)) ≤ (compoundPoissonMeasure r μ).real {0} := by
  have hsum := hasSum_compoundPoissonMeasure_real_apply r μ (measurableSet_singleton 0)
  rw [← hsum.tsum_eq]
  simpa using hsum.summable.le_tsum 0 (fun _ _ => by positivity)

/-- The compound Poisson law is jointly measurable in its rate and probability jump law. -/
@[fun_prop]
theorem measurable_compoundPoissonMeasure_probability [MeasurableAdd₂ α] :
    Measurable fun p : ℝ≥0 × ProbabilityMeasure α =>
      compoundPoissonMeasure p.1 (p.2 : Measure α) := by
  refine Measure.measurable_measure.2 fun s hs => ?_
  simp_rw [compoundPoissonMeasure_apply_eq_tsum _ _ hs]
  refine Measurable.tsum fun n => ?_
  exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul
    ((Measure.measurable_coe hs).comp
      ((Measure.measurable_convolutionPower n).comp measurable_snd))

/-- At rate zero, no jumps occur and the compound Poisson law is concentrated at zero. -/
@[simp]
theorem compoundPoissonMeasure_zero (μ : Measure α) :
    compoundPoissonMeasure 0 μ = Measure.dirac 0 := by
  rw [compoundPoissonMeasure_def, poissonMeasure_zero,
    Measure.dirac_bind Measurable.of_discrete]
  exact Measure.convolutionPower_zero μ

/-- If every jump is zero, the compound Poisson sum is zero at every rate. -/
@[simp]
theorem compoundPoissonMeasure_dirac_zero [MeasurableAdd₂ α] (r : ℝ≥0) :
    compoundPoissonMeasure r (Measure.dirac (0 : α)) = Measure.dirac 0 := by
  rw [compoundPoissonMeasure_def]
  rw [Measure.bind_congr_right
    (ae_of_all _ fun n => Measure.convolutionPower_dirac_zero (α := α) n)]
  simp

/-- A compound Poisson law with a Dirac jump law is the pushforward of its Poisson count by
repeated addition of the atom. -/
theorem compoundPoissonMeasure_dirac [MeasurableAdd₂ α] (r : ℝ≥0) (x : α) :
    compoundPoissonMeasure r (Measure.dirac x) =
      (poissonMeasure r).map fun n => n • x := by
  rw [compoundPoissonMeasure_def]
  rw [Measure.bind_congr_right
    (ae_of_all _ fun n => Measure.convolutionPower_dirac x n)]
  exact Measure.bind_dirac_eq_map _ Measurable.of_discrete

/-- Compound Poisson laws with the same jump law convolve by adding their rates. -/
theorem compoundPoissonMeasure_conv_compoundPoissonMeasure [MeasurableAdd₂ α] (r s : ℝ≥0)
    (μ : Measure α) [SFinite μ] :
    compoundPoissonMeasure r μ ∗ compoundPoissonMeasure s μ = compoundPoissonMeasure (r + s) μ := by
  simp only [compoundPoissonMeasure_def]
  rw [Measure.bind_conv_bind (Measure.convolutionPower_add μ), poissonMeasure_conv_poissonMeasure]

/-- Pushing a compound Poisson law forward along a measurable additive monoid homomorphism
pushes its jump law forward and keeps its rate. -/
theorem map_compoundPoissonMeasure [MeasurableAdd₂ α] {β : Type*} [MeasurableSpace β]
    [AddMonoid β] [MeasurableAdd₂ β] (r : ℝ≥0) (μ : Measure α) [SFinite μ] (f : α →+ β)
    (hf : Measurable f) :
    (compoundPoissonMeasure r μ).map f = compoundPoissonMeasure r (μ.map f) := by
  rw [compoundPoissonMeasure_def, compoundPoissonMeasure_def,
    Measure.map_bind Measurable.of_discrete.aemeasurable hf.aemeasurable]
  exact congrArg _ (funext (Measure.map_convolutionPower μ f hf))

/-- The sum of two independent random variables with compound Poisson laws of rates `r` and `s`
and a common jump law `μ` is compound Poisson with rate `r + s` and jump law `μ`. -/
theorem _root_.ProbabilityTheory.IndepFun.hasLaw_add_compoundPoissonMeasure {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] [MeasurableAdd₂ α] {r s : ℝ≥0}
    {μ : Measure α} [SFinite μ] {X Y : Ω → α}
    (hXY : IndepFun X Y P) (hX : HasLaw X (compoundPoissonMeasure r μ) P)
    (hY : HasLaw Y (compoundPoissonMeasure s μ) P) :
    HasLaw (X + Y) (compoundPoissonMeasure (r + s) μ) P := by
  have := hX.isFiniteMeasure_iff.mp inferInstance
  have := hY.isFiniteMeasure_iff.mp inferInstance
  rw [← compoundPoissonMeasure_conv_compoundPoissonMeasure]
  exact hXY.hasLaw_add hX hY

/-- The characteristic function of the compound Poisson law with rate `r` and jump law `μ` is
`t ↦ exp (r * (φ_μ t - 1))`, where `φ_μ` is the characteristic function of `μ`.

The series computation follows the proof of `ProbabilityTheory.charFun_map_cast_poissonMeasure`
in Mathlib. -/
theorem charFun_compoundPoissonMeasure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (r : ℝ≥0) (μ : Measure E)
    [IsProbabilityMeasure μ] (t : E) :
    charFun (compoundPoissonMeasure r μ) t = Complex.exp (r * (charFun μ t - 1)) := by
  have hint : Integrable (fun x => Complex.exp (inner ℝ x t * Complex.I))
      (compoundPoissonMeasure r μ) :=
    (integrable_const (1 : ℝ)).mono (by fun_prop) (by simp)
  rw [charFun_apply]
  rw [compoundPoissonMeasure_eq_sum] at hint ⊢
  rw [integral_sum_measure hint]
  simp_rw [integral_smul_measure, ← charFun_apply, Measure.charFun_convolutionPower]
  calc ∑' n, (ENNReal.ofReal (Real.exp (-r) * r ^ n / n !)).toReal • charFun μ t ^ n
  _ = ∑' n, (Real.exp (-r) : ℂ) * ((r * charFun μ t) ^ n / n !) := by
      congr with n
      rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
      push_cast
      ring
  _ = (Real.exp (-r) : ℂ) * Complex.exp (r * charFun μ t) := by
      rw [tsum_mul_left, (NormedSpace.expSeries_div_hasSum_exp (r * charFun μ t)).tsum_eq,
        Complex.exp_eq_exp_ℂ]
  _ = Complex.exp (r * (charFun μ t - 1)) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      push_cast
      ring_nf

end TauCeti.Probability
