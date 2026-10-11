/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Dirac measures: pushforwards and additive rigidity

Mathlib's `MeasureTheory.Measure.map_dirac'` computes `(Measure.dirac x).map T = Measure.dirac
(T x)` for a measurable `T`. A Dirac measure leaves a map no room to be modified on a null set:
its only null sets avoid `x`, so a `Measure.dirac x`-a.e. measurable map already agrees at `x`
with the measurable representative it is a.e. equal to. The pushforward formula therefore holds
under that weaker hypothesis, which is the one a.e.-measurable interfaces such as
`ProbabilityTheory.HasLaw` provide.

A Dirac measure is also rigid under addition: if two measures sum to a Dirac mass, each is a
multiple of that same Dirac mass. This identifies the atomic extreme rays in cones represented
by positive measures.

## Main results

* `Measure.map_dirac_of_aemeasurable` — the Dirac pushforward formula for a map that is
  only a.e. measurable.
* `Measure.dirac_eq_dirac_of_inseparable` — inseparable points have equal Borel Dirac measures.
* `TauCeti.MeasureTheory.measurePreserving_const_dirac` — a constant map out of a probability
  space onto a point `b` is measure preserving onto `Measure.dirac b`.
* `MeasureTheory.Measure.eq_smul_dirac_of_forall_notMem` — a measure vanishing on measurable sets
  avoiding a point is a multiple of its Dirac measure.
* `TauCeti.eq_smul_dirac_and_eq_smul_dirac_of_add_eq_dirac` — summands of a Dirac measure are
  supported at the same point.
-/

public section

open MeasureTheory

namespace Measure

variable {X : Type*} {Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {T : X → Y}

/-- A Dirac measure leaves a map no room to be modified on a null set: pushing `Measure.dirac x`
forward along a `Measure.dirac x`-a.e. measurable map is evaluating that map at `x`. -/
@[simp]
theorem map_dirac_of_aemeasurable {x : X} (hT : AEMeasurable T (Measure.dirac x)) :
    (Measure.dirac x).map T = Measure.dirac (T x) := by
  have hx : T x = hT.mk T x := by
    by_contra hne
    have h0 : Measure.dirac x {y | ¬T y = hT.mk T y} = 0 := ae_iff.1 hT.ae_eq_mk
    rw [Measure.dirac_apply_of_mem hne] at h0
    exact one_ne_zero h0
  rw [Measure.map_congr hT.ae_eq_mk, Measure.map_dirac' hT.measurable_mk, ← hx]

/-- Dirac measures at topologically inseparable points agree: Borel measurable sets cannot
separate the points. -/
theorem dirac_eq_dirac_of_inseparable [TopologicalSpace X] [BorelSpace X]
    {x y : X} (hxy : Inseparable x y) : Measure.dirac x = Measure.dirac y := by
  apply MeasureTheory.dirac_eq_dirac_iff_forall_mem_iff_mem.2
  exact fun _ hs ↦ hxy.mem_measurableSet_iff hs

end Measure

namespace MeasureTheory.Measure

/-- A measure vanishing on every measurable set avoiding `x` is its total mass times the
Dirac measure at `x`. No measurability assumption on `{x}` is needed. -/
theorem eq_smul_dirac_of_forall_notMem {X : Type*} [MeasurableSpace X]
    (κ : Measure X) (x : X)
    (hk : ∀ s, MeasurableSet s → x ∉ s → κ s = 0) :
    κ = κ Set.univ • Measure.dirac x := by
  apply Measure.ext
  intro s hs
  by_cases hx : x ∈ s
  · rw [Measure.smul_apply, Measure.dirac_apply' _ hs,
      Set.indicator_of_mem hx, Pi.one_apply, smul_eq_mul, mul_one]
    exact measure_of_measure_compl_eq_zero (hk sᶜ hs.compl (by simpa))
  · rw [Measure.smul_apply, Measure.dirac_apply' _ hs,
      Set.indicator_of_notMem hx, smul_eq_mul, mul_zero]
    exact hk s hs hx

end MeasureTheory.Measure

namespace TauCeti

/-- If a sum of measures is a Dirac mass, both summands are multiples of that Dirac mass. -/
theorem eq_smul_dirac_and_eq_smul_dirac_of_add_eq_dirac {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {x : X}
    (h : μ + ν = Measure.dirac x) :
    μ = μ Set.univ • Measure.dirac x ∧ ν = ν Set.univ • Measure.dirac x := by
  have hzero (s : Set X) (hs : MeasurableSet s) (hx : x ∉ s) :
      μ s = 0 ∧ ν s = 0 := by
    have h' := congrArg (fun η : Measure X => η s) h
    rw [Measure.add_apply, Measure.dirac_apply' _ hs,
      Set.indicator_of_notMem hx] at h'
    exact add_eq_zero.mp h'
  exact ⟨μ.eq_smul_dirac_of_forall_notMem x (fun s hs hx => (hzero s hs hx).1),
    ν.eq_smul_dirac_of_forall_notMem x (fun s hs hx => (hzero s hs hx).2)⟩

end TauCeti

namespace TauCeti

namespace MeasureTheory

variable {X : Type*} {Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A constant map out of a probability space onto a point `b` is measure preserving onto
`Measure.dirac b`, with no hypothesis on either measurable space. -/
theorem measurePreserving_const_dirac {μ : Measure X} [IsProbabilityMeasure μ] (b : Y) :
    MeasurePreserving (fun _ : X => b) μ (Measure.dirac b) :=
  ⟨measurable_const, by rw [Measure.map_const, measure_univ, one_smul]⟩

end MeasureTheory

end TauCeti
