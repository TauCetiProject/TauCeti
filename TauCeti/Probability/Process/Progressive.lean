/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.Order.Cadlag
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Progressive measurability of right-continuous adapted processes

A strongly adapted process in nonnegative real time with everywhere right-continuous paths is
strongly progressive, on its original filtration. No completeness or right continuity of the
filtration is required. In particular, the result applies to adapted càdlàg processes and permits
use of the progressive stopped-evaluation API.

On each fixed horizon, right-endpoint samples are capped at that horizon. These approximations
are measurable for the horizon's product sigma algebra; they need not be adapted at earlier
times. Almost-sure path regularity alone does not give the literal conclusion for a raw version.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §1.
-/

public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology

private noncomputable def rightSample (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (⌈(t : ℝ) * (n + 1)⌉₊ : ℝ≥0) / (n + 1)

private lemma le_rightSample (n : ℕ) (t : ℝ≥0) : t ≤ rightSample n t := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ≥0) < n + 1)).mpr
  exact_mod_cast Nat.le_ceil ((t : ℝ) * (n + 1))

private lemma tendsto_rightSample (t : ℝ≥0) :
    Tendsto (fun n => rightSample n t) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  simpa only [Function.comp_def, rightSample, NNReal.coe_div, NNReal.coe_natCast,
    NNReal.coe_add, NNReal.coe_one,
    Nat.cast_add, Nat.cast_one] using
    (tendsto_nat_ceil_mul_div_atTop t.coe_nonneg).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))

/-- A strongly adapted process with everywhere right-continuous paths is strongly progressive
on its original filtration. The state space need not be separable. -/
theorem MeasureTheory.StronglyAdapted.isStronglyProgressive_of_isRightContinuous
    {Ω E : Type*} {m : MeasurableSpace Ω} [TopologicalSpace E] [PseudoMetrizableSpace E]
    {ℱ : Filtration ℝ≥0 m} {u : ℝ≥0 → Ω → E} (hu : StronglyAdapted ℱ u)
    (hc : ∀ ω, IsRightContinuous (fun t => u t ω)) : IsStronglyProgressive ℱ u := by
  intro T
  let : MeasurableSpace Ω := ℱ T
  have hm (n : ℕ) : StronglyMeasurable
      (fun p : Iic T × Ω => u (min (rightSample n p.1) T) p.2) := by
    have hs : StronglyMeasurable (Function.uncurry
        (fun k : ℕ => u (min ((k : ℝ≥0) / (n + 1)) T))) :=
      stronglyMeasurable_uncurry_of_countable fun k => (hu _).mono (ℱ.mono (min_le_right _ _))
    have hmap : Measurable (fun p : Iic T × Ω =>
        (⌈((p.1 : ℝ≥0) : ℝ) * (n + 1)⌉₊, p.2)) :=
      ((NNReal.continuous_coe.measurable.comp
        (measurable_subtype_coe.comp measurable_fst)).mul_const
          (n + 1 : ℝ)).nat_ceil.prodMk measurable_snd
    simpa only [Function.uncurry_def, Function.comp_def, rightSample] using
      hs.comp_measurable hmap
  apply stronglyMeasurable_of_tendsto atTop hm
  apply tendsto_pi_nhds.mpr
  intro p
  apply (continuousWithinAt_Ioi_iff_Ici.mp (hc p.2 p.1)).tendsto.comp
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, .of_forall fun n => ?_⟩
  · have h := (tendsto_rightSample p.1).min (tendsto_const_nhds (x := T))
    rw [min_eq_left (α := ℝ≥0) p.1.property] at h
    exact h
  · exact le_min (le_rightSample n p.1) p.1.property

/-- An adapted process with everywhere right-continuous paths in a second-countable
pseudometrizable Borel state space is progressive, without usual-filtration assumptions. -/
theorem MeasureTheory.Adapted.isProgressive_of_isRightContinuous
    {Ω E : Type*} {m : MeasurableSpace Ω} [TopologicalSpace E] [PseudoMetrizableSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {ℱ : Filtration ℝ≥0 m} {u : ℝ≥0 → Ω → E} (hu : Adapted ℱ u)
    (hc : ∀ ω, IsRightContinuous (fun t => u t ω)) : IsProgressive ℱ u :=
  ((stronglyAdapted_iff_adapted.mpr hu).isStronglyProgressive_of_isRightContinuous hc).isProgressive
