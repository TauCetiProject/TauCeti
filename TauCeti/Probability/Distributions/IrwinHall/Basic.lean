/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Uniform.Basic
public import TauCeti.Probability.Independence.ConvolutionPower

/-!
# Irwin–Hall distributions

The Irwin–Hall law of order `n` is the distribution of the sum of `n` independent unit-uniform
variables. This file defines it using convolution powers, identifies the product-measure
construction, and proves convolution by addition of orders, almost-sure bounds, and absolute
continuity for positive orders. Order zero is the point mass at zero.

The convolution recursion provides the measure identity used to integrate successive uniform
summands when calculating densities and cumulative probabilities.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 26.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory

namespace TauCeti.Probability

/-- The law of a sum of `n` independent uniform variables on the unit interval.
The empty sum has law `Measure.dirac 0`. -/
def irwinHallMeasure (n : ℕ) : Measure ℝ :=
  (uniformMeasure 0 1).convolutionPower n

/-- The Irwin–Hall law is the convolution power of the unit-uniform law. -/
theorem irwinHallMeasure_def (n : ℕ) :
    irwinHallMeasure n = (uniformMeasure 0 1).convolutionPower n := (rfl)

/-- Every Irwin–Hall law is a probability measure, including order zero. -/
instance isProbabilityMeasure_irwinHallMeasure (n : ℕ) :
    IsProbabilityMeasure (irwinHallMeasure n) := by
  rw [irwinHallMeasure_def]
  infer_instance

/-- Order zero is the empty-sum point mass. -/
@[simp]
theorem irwinHallMeasure_zero : irwinHallMeasure 0 = Measure.dirac 0 := by
  rw [irwinHallMeasure_def, Measure.convolutionPower_zero]

/-- Order one is the unit-uniform law. -/
@[simp]
theorem irwinHallMeasure_one : irwinHallMeasure 1 = uniformMeasure 0 1 := by
  rw [irwinHallMeasure_def, Measure.convolutionPower_one]

/-- Independent Irwin–Hall sums convolve by adding their orders. -/
theorem irwinHallMeasure_conv_irwinHallMeasure (m n : ℕ) :
    irwinHallMeasure m ∗ irwinHallMeasure n = irwinHallMeasure (m + n) := by
  simp only [irwinHallMeasure_def, Measure.convolutionPower_add]

/-- Appending one independent unit uniform gives the next Irwin–Hall law. -/
theorem irwinHallMeasure_succ (n : ℕ) :
    irwinHallMeasure (n + 1) = irwinHallMeasure n ∗ uniformMeasure 0 1 := by
  rw [← irwinHallMeasure_one, irwinHallMeasure_conv_irwinHallMeasure]

/-- Summing the coordinates of a finite product of unit-uniform laws gives the Irwin–Hall law.
This includes the empty product. -/
theorem map_sum_pi_uniformMeasure_zero_one {ι : Type*} [Fintype ι] :
    (Measure.pi fun _ : ι ↦ uniformMeasure 0 1).map (fun x ↦ ∑ i, x i) =
      irwinHallMeasure (Fintype.card ι) := by
  simpa only [irwinHallMeasure_def] using
    Measure.map_sum_pi_eq_convolutionPower (ι := ι) (uniformMeasure 0 1)

/-- An Irwin–Hall variable of order `n` lies in `[0, n]` almost surely. -/
theorem ae_mem_Icc_irwinHallMeasure (n : ℕ) :
    ∀ᵐ x ∂irwinHallMeasure n, x ∈ Icc 0 (n : ℝ) := by
  rw [← Fintype.card_fin n, ← map_sum_pi_uniformMeasure_zero_one]
  apply (ae_map_iff (by fun_prop) measurableSet_Icc).2
  have hcoord (i : Fin n) : ∀ᵐ x ∂Measure.pi (fun _ : Fin n ↦ uniformMeasure 0 1),
      x i ∈ Ioc (0 : ℝ) 1 :=
    (measurePreserving_eval (fun _ : Fin n ↦ uniformMeasure 0 1) i).quasiMeasurePreserving.ae
      ae_mem_Ioc_uniformMeasure
  filter_upwards [ae_all_iff.2 hcoord] with x hx
  constructor
  · exact Finset.sum_nonneg fun i _ ↦ (hx i).1.le
  · simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ (hx i).2)

/-- Positive-order Irwin–Hall laws are absolutely continuous with respect to Lebesgue measure.
Order zero is a Dirac measure instead. -/
theorem irwinHallMeasure_absolutelyContinuous {n : ℕ} (hn : 0 < n) :
    irwinHallMeasure n ≪ volume := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [irwinHallMeasure_def]
  apply Measure.convolutionPower_succ_absolutelyContinuous
  rw [uniformMeasure_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- Positive-order Irwin–Hall laws have no atoms. -/
instance nullSingletonClass_irwinHallMeasure (n : ℕ) [NeZero n] :
    NullSingletonClass (irwinHallMeasure n) :=
  ⟨fun x ↦ irwinHallMeasure_absolutelyContinuous (Nat.pos_of_ne_zero (NeZero.ne n))
    (measure_singleton x)⟩

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- A finite sum of independent unit-uniform variables has the Irwin–Hall law. -/
theorem iIndepFun.hasLaw_sum_irwinHallMeasure {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) (uniformMeasure 0 1) P) :
    HasLaw (∑ i, X i) (irwinHallMeasure (Fintype.card ι)) P := by
  have := hindep.isProbabilityMeasure
  rw [irwinHallMeasure_def]
  exact hindep.hasLaw_sum_convolutionPower hX

/-- The sum of independent Irwin–Hall variables adds their orders. -/
theorem IndepFun.hasLaw_add_irwinHallMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ} {m n : ℕ}
    (hXY : IndepFun X Y P) (hX : HasLaw X (irwinHallMeasure m) P)
    (hY : HasLaw Y (irwinHallMeasure n) P) :
    HasLaw (X + Y) (irwinHallMeasure (m + n)) P := by
  have := hX.isProbabilityMeasure
  rw [← irwinHallMeasure_conv_irwinHallMeasure]
  exact hXY.hasLaw_add hX hY

end ProbabilityTheory
