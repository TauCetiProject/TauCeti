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

-- Removing the selected occurrence reconstructs the measure and reduces its mass by one,
-- with truncated subtraction handling the empty measure as well.
private lemma sub_option_dirac_step {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (x : Option X) (hle : x.elim 0 Measure.dirac ≤ ν)
    (hnone : x = none ↔ ν = 0) :
    (ν - x.elim 0 Measure.dirac) + x.elim 0 Measure.dirac = ν ∧
      (ν - x.elim 0 Measure.dirac) univ = ν univ - 1 := by
  have : IsFiniteMeasure (x.elim 0 Measure.dirac) := by
    cases x <;> simp only [Option.elim_none, Option.elim_some] <;> infer_instance
  refine ⟨sub_add_cancel_of_le hle, ?_⟩
  cases x with
  | none => simp [hnone.mp rfl]
  | some x =>
    have hs := congrArg (fun μ : Measure X => μ univ) (sub_add_cancel_of_le hle)
    simp only [add_apply, Option.elim_some, dirac_apply_of_mem (mem_univ x)] at hs ⊢
    exact ENNReal.eq_sub_of_add_eq (by simp) hs

private abbrev FiniteIntegerMeasure (X : Type*) [MeasurableSpace X] :=
  {ν : Measure X // IsFiniteMeasure ν ∧ ν.IsIntegerValued}

private lemma iterate_mass {X : Type*} [MeasurableSpace X]
    (step : FiniteIntegerMeasure X → FiniteIntegerMeasure X)
    (hmass : ∀ ν, (step ν).val univ = ν.val univ - 1)
    (ν : FiniteIntegerMeasure X) (n : ℕ) :
    (step^[n] ν).val univ = ν.val univ - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply', hmass, ih, tsub_tsub, Nat.cast_add, Nat.cast_one]

private lemma iterate_split {X : Type*} [MeasurableSpace X]
    (step : FiniteIntegerMeasure X → FiniteIntegerMeasure X)
    (atom : FiniteIntegerMeasure X → Measure X)
    (hsplit : ∀ ν, (step ν).val + atom ν = ν.val)
    (ν : FiniteIntegerMeasure X) (n : ℕ) :
    (step^[n] ν).val + ∑ i ∈ Finset.range n, atom (step^[i] ν) = ν.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Function.iterate_succ_apply']
    calc
      (step (step^[n] ν)).val +
          (∑ i ∈ Finset.range n, atom (step^[i] ν) + atom (step^[n] ν)) =
          ((step (step^[n] ν)).val + atom (step^[n] ν)) +
            ∑ i ∈ Finset.range n, atom (step^[i] ν) := by ac_rfl
      _ = ν.val := by rw [hsplit, ih]

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
  let M := FiniteIntegerMeasure X
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
  have hremove (ν : M) := sub_option_dirac_step ν.val (pick ν) (hle ν) (hnone ν)
  let start : α → M := fun a => ⟨μ a, hfinite a, hint a⟩
  let rem (n : ℕ) (a : α) : M := step^[n] (start a)
  have hrem (n : ℕ) : Measurable (rem n) :=
    (hstep.iterate n).comp (hm.subtype_mk)
  -- The one-step mass formula iterates without choosing a natural total mass.
  have hmass_rem (a : α) (n : ℕ) : (rem n a).val univ = μ a univ - n :=
    iterate_mass step (fun ν => (hremove ν).2) (start a) n
  let e : α → ℕ → Option X := fun a n => pick (rem n a)
  have henone (a : α) (n : ℕ) : e a n = none ↔ μ a univ ≤ n := by
    rw [hnone, ← measure_univ_eq_zero, hmass_rem, tsub_eq_zero_iff_le]
  refine ⟨e, measurable_pi_iff.2 (fun n => hpick.comp (hrem n)), henone, fun a => ?_⟩
  -- Telescope the removals, then stop at the original (integer) total mass.
  have hprefix (n : ℕ) :
      (rem n a).val + ∑ i ∈ Finset.range n, atom (rem i a) = μ a :=
    iterate_split step atom (fun ν => (hremove ν).1) (start a) n
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
