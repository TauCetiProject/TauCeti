/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Kernel.Basic
import TauCeti.Topology.UnitInterval.NNReal

/-!
# Parameter measurability for the Bernoulli distribution

The Bernoulli measure `Ber(x, y, p)` depends measurably on its two atoms and its success
probability jointly, so measurable parameter maps produce measurable measure-valued Bernoulli
families, in particular the Markov kernel `ProbabilityTheory.Kernel.bernoulli`, as well as
`ProbabilityTheory.bernoulliMeasure_apply_singleton_bool` for evaluating `Ber(true, false, p)` on
singleton sets.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Evaluating `bernoulliMeasure true false p` at `{b}` gives `p` for `true` and `1 - p` for
`false`. -/
theorem bernoulliMeasure_apply_singleton_bool (p : unitInterval) (b : Bool) :
    bernoulliMeasure true false p {b} =
      ((if b then unitInterval.toNNReal p else 1 - unitInterval.toNNReal p : ℝ≥0) : ENNReal) := by
  cases b
  · simp [unitInterval.toNNReal_symm]
  · simp

end ProbabilityTheory

/-- **The Bernoulli family is measurable in its parameters**: if the atoms `x`, `y` and the
success probability `p` depend measurably on `a`, then so does `Ber(x a, y a, p a)`. -/
@[fun_prop]
theorem Measurable.bernoulliMeasure {α X : Type*} [MeasurableSpace α] [MeasurableSpace X]
    {x y : α → X} {p : α → unitInterval} (hx : Measurable x) (hy : Measurable y)
    (hp : Measurable p) : Measurable fun a => Ber(x a, y a, p a) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [bernoulliMeasure_def, add_apply, smul_apply, Measure.dirac_apply' _ hs]
  fun_prop (disch := exact hs)

namespace ProbabilityTheory.Kernel

/-- The location-dependent Bernoulli Markov kernel placing mass `p x` at `a` and `1 - p x` at
`b`. Endpoint values `0` and `1` and coinciding points `a = b` are allowed. -/
noncomputable def bernoulli {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
    (a b : E) {p : X → unitInterval} (hp : Measurable p) : Kernel X E where
  toFun x := bernoulliMeasure a b (p x)
  measurable' := measurable_const.bernoulliMeasure measurable_const hp

/-- Evaluating `Kernel.bernoulli` at a location yields the corresponding Bernoulli measure. -/
@[simp]
theorem bernoulli_apply {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
    (a b : E) {p : X → unitInterval} (hp : Measurable p) (x : X) :
    Kernel.bernoulli a b hp x = bernoulliMeasure a b (p x) := (rfl)

/-- A location-dependent Bernoulli kernel is a Markov kernel. -/
instance {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
    (a b : E) {p : X → unitInterval} (hp : Measurable p) :
    IsMarkovKernel (Kernel.bernoulli a b hp) where
  isProbabilityMeasure x := by
    rw [bernoulli_apply]
    infer_instance

/-- A constant success probability recovers the constant Bernoulli kernel. -/
@[simp]
theorem bernoulli_const {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
    (a b : E) (p : unitInterval) :
    Kernel.bernoulli a b (p := fun _ : X => p) measurable_const =
      Kernel.const X (bernoulliMeasure a b p) := by
  ext x
  rw [bernoulli_apply, Kernel.const_apply]

/-- Evaluating `Kernel.bernoulli a b hp` at `{a}` when `a ≠ b` gives `p x`. -/
theorem bernoulli_apply_singleton_left {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
    {a b : E} (ha : MeasurableSet ({a} : Set E)) (hab : a ≠ b) {p : X → unitInterval}
    (hp : Measurable p) (x : X) :
    Kernel.bernoulli a b hp x {a} = (unitInterval.toNNReal (p x) : ENNReal) :=
  bernoulliMeasure_apply_of_mem_of_notMem (p x) ha rfl hab.symm

/-- Evaluating `Kernel.bernoulli a b hp` at `{b}` when `a ≠ b` gives `1 - p x`
(`unitInterval.symm (p x)`). -/
theorem bernoulli_apply_singleton_right {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
    {a b : E} (hb : MeasurableSet ({b} : Set E)) (hab : a ≠ b) {p : X → unitInterval}
    (hp : Measurable p) (x : X) :
    Kernel.bernoulli a b hp x {b} = (unitInterval.toNNReal (unitInterval.symm (p x)) : ENNReal) :=
  bernoulliMeasure_apply_of_notMem_of_mem (p x) hb hab rfl

end ProbabilityTheory.Kernel
