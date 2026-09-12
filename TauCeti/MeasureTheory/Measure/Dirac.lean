/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Dirac measures and their pushforwards

Mathlib's `MeasureTheory.Measure.map_dirac'` computes `(Measure.dirac x).map T = Measure.dirac
(T x)` for a measurable `T`. A Dirac measure leaves a map no room to be modified on a null set:
its only null sets avoid `x`, so a `Measure.dirac x`-a.e. measurable map already agrees at `x`
with the measurable representative it is a.e. equal to. The pushforward formula therefore holds
under that weaker hypothesis, which is the one a.e.-measurable interfaces such as
`ProbabilityTheory.HasLaw` provide.

## Main results

* `Measure.map_dirac_of_aemeasurable` — the Dirac pushforward formula for a map that is
  only a.e. measurable.
* `Measure.dirac_eq_dirac_of_inseparable` — inseparable points have equal Borel Dirac measures.
* `Measure.pi_dirac` — a finite product of Dirac measures is the Dirac measure at the product
  point.
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

/-- **A finite product of Dirac measures is a Dirac measure**, at the point assembled from the
individual ones. -/
theorem pi_dirac {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (x : ∀ i, α i) : (Measure.pi fun i => Measure.dirac (x i)) = Measure.dirac x := by
  refine Measure.pi_eq (μ' := Measure.dirac x) fun s hs => ?_
  by_cases h : ∀ i, x i ∈ s i
  · rw [Measure.dirac_apply_of_mem (Set.mem_univ_pi.2 h)]
    exact (Finset.prod_eq_one fun i _ => Measure.dirac_apply_of_mem (h i)).symm
  · simp only [not_forall] at h
    obtain ⟨i, hi⟩ := h
    rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs),
      Set.indicator_of_notMem fun hx => hi (Set.mem_univ_pi.1 hx i)]
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    rw [Measure.dirac_apply' _ (hs i), Set.indicator_of_notMem hi]

end Measure
