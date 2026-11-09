/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.IntegerValued.Selection
public import TauCeti.MeasureTheory.Measure.Sub

/-!
# Measurable enumeration of finite integer-valued measures

A measurable family of finite integer-valued measures on a standard Borel space admits
an enumeration of its occurrences. Each coordinate is measurable, repeated locations
record multiplicity, and the sequence is `none` exactly after its total mass has been
exhausted. Summing the selected Dirac occurrences recovers the original measure.

This finite-window enumeration permits attaching independent marks to occurrences,
including several occurrences at the same location. The construction iterates the
optional occurrence selector, subtracting one Dirac measure at each step.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapter 6 (measurable enumeration and multiplicities).
-/

public section

open MeasureTheory Set Function
open scoped ENNReal

namespace MeasureTheory.Measure

/-- A measurable family of finite integer-valued measures can be enumerated measurably.
The enumeration stops exactly at the total number of occurrences, and its Dirac sum
reconstructs the measure. No ordering of the locations or topology on the parameter
space is required. -/
theorem _root_.Measurable.exists_finite_occurrence_enumeration
    {α X : Type*} [MeasurableSpace α] [MeasurableSpace X] [StandardBorelSpace X]
    {μ : α → Measure X} (hm : Measurable μ)
    (hfinite : ∀ a, IsFiniteMeasure (μ a)) (hint : ∀ a, (μ a).IsIntegerValued) :
    ∃ e : α → ℕ → Option X, Measurable e ∧
      (∀ a n, e a n = none ↔ μ a univ ≤ n) ∧
      ∀ a, μ a = Measure.sum (fun n => (e a n).elim 0 Measure.dirac) := by
  classical
  -- Choose on the space of all finite integer-valued measures, so the same measurable
  -- removal operation can be iterated for every member of the family.
  let M := {ν : Measure X // IsFiniteMeasure ν ∧ ν.IsIntegerValued}
  have hcoe : Measurable (fun ν : M => (ν : Measure X)) := measurable_subtype_coe
  obtain ⟨pick, hpick, hnone, hmass⟩ := hcoe.exists_option_one_le_singleton
    (fun ν => ν.2.1) (fun ν => ν.2.2)
  let atom : M → Measure X := fun ν => (pick ν).elim 0 Measure.dirac
  have hatom : Measurable atom :=
    (Option.measurable_elim 0 Measure.measurable_dirac).comp hpick
  have hle (ν : M) : atom ν ≤ ν.val := by
    cases h : pick ν with
    | none => simpa only [atom, h, Option.elim_none] using (Measure.zero_le ν.val)
    | some x =>
      simpa only [atom, h, Option.elim_some] using
        (dirac_le_iff_one_le_apply_singleton _ _).2 (hmass ν x h)
  have hfinatom (ν : M) : IsFiniteMeasure (atom ν) := by
    cases h : pick ν <;> simp only [atom, h, Option.elim_none, Option.elim_some] <;> infer_instance
  let step : M → M := fun ν => ⟨ν.val - atom ν, by
    refine ⟨by have := ν.2.1; infer_instance, ?_⟩
    cases h : pick ν with
    | none => simpa [atom, h] using ν.2.2
    | some x => simpa [atom, h] using ν.2.2.sub_dirac x⟩
  have hstep : Measurable step := (hcoe.measure_sub hatom hfinatom hle).subtype_mk
  have hsplit (ν : M) : (step ν).val + atom ν = ν.val := by
    have := hfinatom ν
    exact sub_add_cancel_of_le (hle ν)
  have hzero (ν : M) (h : ν.val = 0) : (step ν).val = 0 := by
    exact le_antisymm (sub_le.trans (by rw [h])) (Measure.zero_le _)
  let start : α → M := fun a => ⟨μ a, hfinite a, hint a⟩
  let rem (n : ℕ) (a : α) : M := step^[n] (start a)
  have hrem (n : ℕ) : Measurable (rem n) :=
    (hstep.iterate n).comp (hm.subtype_mk)
  have hrem_zero (a : α) : (rem 0 a).val = μ a := rfl
  have hrem_succ (n : ℕ) (a : α) : rem (n + 1) a = step (rem n a) :=
    Function.iterate_succ_apply' _ _ _
  -- Every nonempty remainder loses exactly one unit of mass; zero remains zero.
  have hmass_rem (a : α) (n : ℕ) :
      (rem n a).val univ = μ a univ - n := by
    have := hfinite a
    obtain ⟨k, hk⟩ := (hint a).exists_eq_natCast MeasurableSet.univ (measure_lt_top _ _)
    rw [hk]
    induction n with
    | zero => simp only [Nat.cast_zero, tsub_zero, hrem_zero, hk]
    | succ n ih =>
      rw [hrem_succ]
      by_cases hz : (rem n a).val = 0
      · have hkn : k ≤ n := by
          have heq : (k : ℝ≥0∞) ≤ n := tsub_eq_zero_iff_le.mp (by simpa [hz] using ih.symm)
          exact_mod_cast heq
        rw [hzero _ hz]
        simp only [FunLike.coe_zero, Pi.zero_apply]
        exact (tsub_eq_zero_of_le (Nat.cast_le.mpr (hkn.trans (Nat.le_succ n)))).symm
      · have hp : pick (rem n a) ≠ none := fun h => hz ((hnone _).mp h)
        obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hp
        have hs := congrArg (fun ν : Measure X => ν univ) (hsplit (rem n a))
        simp only [add_apply, atom, hx, Option.elim_some, dirac_apply_of_mem (mem_univ x)] at hs
        have hsub : (step (rem n a)).val univ = (rem n a).val univ - 1 := by
          exact ENNReal.eq_sub_of_add_eq (by simp) hs
        rw [hsub, ih]
        rw [tsub_tsub, Nat.cast_add, Nat.cast_one]
  let e : α → ℕ → Option X := fun a n => pick (rem n a)
  have henone (a : α) (n : ℕ) : e a n = none ↔ μ a univ ≤ n := by
    rw [hnone, ← measure_univ_eq_zero, hmass_rem, tsub_eq_zero_iff_le]
  refine ⟨e, measurable_pi_iff.2 (fun n => hpick.comp (hrem n)), henone, fun a => ?_⟩
  -- Telescope the removals, then stop at the original (integer) total mass.
  have hprefix (n : ℕ) :
      (rem n a).val + ∑ i ∈ Finset.range n, atom (rem i a) = μ a := by
    induction n with
    | zero => simp [hrem_zero]
    | succ n ih =>
      rw [Finset.sum_range_succ, hrem_succ]
      calc
        (step (rem n a)).val + (∑ i ∈ Finset.range n, atom (rem i a) + atom (rem n a)) =
            ((step (rem n a)).val + atom (rem n a)) +
              ∑ i ∈ Finset.range n, atom (rem i a) := by ac_rfl
        _ = μ a := by rw [hsplit, ih]
  have := hfinite a
  obtain ⟨k, hk⟩ := (hint a).exists_eq_natCast MeasurableSet.univ (measure_lt_top _ _)
  have hremk : (rem k a).val = 0 := by
    rw [← measure_univ_eq_zero, hmass_rem]
    simp [hk]
  have hsum : μ a = ∑ i ∈ Finset.range k, atom (rem i a) := by
    simpa [hremk] using (hprefix k).symm
  rw [hsum]
  ext s hs
  rw [sum_apply, Measure.sum_apply _ hs, tsum_eq_sum (s := Finset.range k)]
  intro n hn
  have hnone' : e a n = none := (henone a n).2 (by
    rw [hk]
    exact_mod_cast (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)))
  simp [hnone']

end MeasureTheory.Measure
