/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.IID
public import TauCeti.Probability.Exchangeability.MarkovExchangeable
public import TauCeti.Probability.Exchangeability.Recurrence.Basic
public import TauCeti.Probability.Exchangeability.RowExchangeable
public import TauCeti.Probability.Exchangeability.SuccessorArray
public import Mathlib.Probability.Independence.InfinitePi

/-!
# A recurrent Markov exchangeable process whose successor array is not row exchangeable

The Diaconis–Freedman representation of a Markov exchangeable process passes through its
**successor array** `TauCeti.Probability.successorProcess`, whose `(a, k)`-entry is the state
reached right after the `k`-th visit to `a`. The change of variables back from a row exchangeable
array to a mixture of Markov chains is
`TauCeti.Probability.mixedMarkovChain_of_rowExchangeable_successorProcess`, and its hypothesis is
row exchangeability of that array. This file shows that recurrence and Markov exchangeability do
not supply that hypothesis, and isolates exactly what obstructs it.

The obstruction is not the reordering of genuine transitions but the junk rows. A state the
process never visits has no genuine successors, so its whole row is `Nat.nth`'s junk value: by
`TauCeti.successorArray_eq_successorArray_zero_of_forall_ne` it is constant and equal to the cell
`(x 0, 0)`. Every successor array therefore satisfies the tie

```text
successorArray x a k = successorArray x (x 0) 0    (a never visited)
```

whereas a permutation of the row `x 0` moves the right-hand side while leaving the left-hand side
where it is. `TauCeti.Probability.Recurrent` constrains only the states a process *does* visit, so
it does not exclude this.

To turn that into a counterexample take the three-letter alphabet `Fin 3` and let
`spareStateProcess` be the sequence of coordinates of a fair coin sequence in the two letters `0`
and `1`; the letter `2` is spare and is almost surely never taken. Being i.i.d. the process is
exchangeable (`spareStateProcess_exchangeable`), hence Markov exchangeable
(`spareStateProcess_markovExchangeable`) and recurrent (`spareStateProcess_recurrent`). Yet
swapping the first two entries of the row of the letter `0` — a permutation family of finite
support — changes the law of its successor array
(`spareStateProcess_not_rowExchangeable_successorProcess`), because on the positive-probability
event that the path begins `0, 0, 1, 1` the swap breaks the tie above.

So a row-exchangeability hypothesis on a successor array has to be restricted to the rows the
process actually visits — which is all its consumer reads, since
`TauCeti.eqOn_iff_successorArray_visitCell` describes a finite path event through the cells a
reference path designates, and those lie in visited rows.

## Main results

* `TauCeti.Probability.spareStateProcess_exchangeable`,
  `TauCeti.Probability.spareStateProcess_markovExchangeable` and
  `TauCeti.Probability.spareStateProcess_recurrent` — the example satisfies the Diaconis–Freedman
  hypotheses.
* `TauCeti.Probability.spareStateProcess_not_rowExchangeable_successorProcess` — its successor
  array is nevertheless not row exchangeable.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.

The example uses Mathlib's countable product of probability measures
(`MeasureTheory.Measure.infinitePi`) and the independence of its coordinates
(`ProbabilityTheory.iIndepFun_infinitePi`); it needs no material from
`cameronfreer/exchangeability`, which treats exchangeable rather than Markov exchangeable
sequences.
-/

-- Provenance: the Tau Ceti `Exchangeability` roadmap blueprint, `README.md`, section "Markov
-- exchangeability", which asks for the Diaconis–Freedman representation of a recurrent Markov
-- exchangeable process as a mixture of Markov chains.

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

/-- The fair-coin law on the three-letter alphabet `Fin 3`: mass `2⁻¹` on each of the letters `0`
and `1`, and no mass on the spare letter `2`. -/
@[expose] def spareStateLaw : Measure (Fin 3) :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 0 + Measure.dirac 1)

/-- The value of `spareStateLaw` on an arbitrary set of letters. -/
theorem spareStateLaw_apply (s : Set (Fin 3)) :
    spareStateLaw s =
      (2 : ℝ≥0∞)⁻¹ * (s.indicator 1 (0 : Fin 3) + s.indicator 1 (1 : Fin 3)) := by
  rw [spareStateLaw, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply,
    Measure.dirac_apply, smul_eq_mul]

/-- The spare letter is null. -/
@[simp]
theorem spareStateLaw_singleton_two : spareStateLaw {(2 : Fin 3)} = 0 := by
  rw [spareStateLaw_apply]
  simp

/-- Each of the two letters the process uses carries mass `2⁻¹`. -/
theorem spareStateLaw_singleton_of_ne_two {a : Fin 3} (ha : a ≠ 2) :
    spareStateLaw {a} = (2 : ℝ≥0∞)⁻¹ := by
  rw [spareStateLaw_apply]
  fin_cases a <;> simp_all

instance : IsProbabilityMeasure spareStateLaw := by
  constructor
  rw [spareStateLaw_apply]
  simp only [Set.indicator_univ, Pi.one_apply]
  rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The law of the example: fair-coin i.i.d. sequences in the alphabet `Fin 3`. -/
@[expose] def spareStateMeasure : Measure (ℕ → Fin 3) :=
  Measure.infinitePi fun _ : ℕ => spareStateLaw

instance : IsProbabilityMeasure spareStateMeasure := by
  rw [spareStateMeasure]
  infer_instance

/-- The example's process: the coordinates of a fair-coin sequence in the alphabet `Fin 3`. -/
abbrev spareStateProcess : ℕ → (ℕ → Fin 3) → Fin 3 := fun n x => x n

theorem measurable_spareStateProcess (n : ℕ) : Measurable (spareStateProcess n) :=
  measurable_pi_apply n

/-- Each coordinate of the example has the fair-coin law. -/
theorem spareStateMeasure_map_spareStateProcess (n : ℕ) :
    spareStateMeasure.map (spareStateProcess n) = spareStateLaw :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => spareStateLaw) n).map_eq

/-- The coordinates of the example are independent. -/
theorem spareStateProcess_iIndepFun : iIndepFun spareStateProcess spareStateMeasure :=
  iIndepFun_infinitePi (X := fun _ : ℕ => (id : Fin 3 → Fin 3)) fun _ => measurable_id

theorem spareStateProcess_identDistrib (n : ℕ) :
    IdentDistrib (spareStateProcess n) (spareStateProcess 0) spareStateMeasure
      spareStateMeasure :=
  ⟨(measurable_spareStateProcess n).aemeasurable,
    (measurable_spareStateProcess 0).aemeasurable, by
      rw [spareStateMeasure_map_spareStateProcess, spareStateMeasure_map_spareStateProcess]⟩

/-- **The example is exchangeable**, being i.i.d. -/
theorem spareStateProcess_exchangeable : Exchangeable spareStateMeasure spareStateProcess :=
  Exchangeable.of_iIndepFun_identDistrib spareStateProcess_iIndepFun
    spareStateProcess_identDistrib

/-- **The example is Markov exchangeable**, the first Diaconis–Freedman hypothesis. -/
theorem spareStateProcess_markovExchangeable :
    MarkovExchangeable spareStateMeasure spareStateProcess :=
  spareStateProcess_exchangeable.markovExchangeable fun i =>
    (measurable_spareStateProcess i).aemeasurable

/-- **The example is recurrent**, the second Diaconis–Freedman hypothesis. Recurrence constrains
only the letters the process takes, and says nothing about the spare letter `2`. -/
theorem spareStateProcess_recurrent : Recurrent spareStateMeasure spareStateProcess :=
  spareStateProcess_exchangeable.recurrent fun i => (measurable_spareStateProcess i).aemeasurable

/-- Reading a coordinate law off the product law. -/
private theorem spareStateMeasure_setOf_apply_eq (n : ℕ) (a : Fin 3) :
    spareStateMeasure {x | x n = a} = spareStateLaw {a} := by
  rw [show {x : ℕ → Fin 3 | x n = a} = spareStateProcess n ⁻¹' {a} from rfl,
    ← Measure.map_apply (measurable_spareStateProcess n) (measurableSet_singleton a),
    spareStateMeasure_map_spareStateProcess]

/-- The set of sequences avoiding the spare letter. -/
private def avoidsTwo : Set (ℕ → Fin 3) := {x | ∀ n, x n ≠ 2}

private theorem measurableSet_avoidsTwo : MeasurableSet avoidsTwo := by
  rw [show avoidsTwo = ⋂ n : ℕ, spareStateProcess n ⁻¹' {(2 : Fin 3)}ᶜ by ext x; simp [avoidsTwo]]
  exact MeasurableSet.iInter fun n =>
    (measurable_spareStateProcess n) (measurableSet_singleton _).compl

/-- **The spare letter is almost surely never taken.** -/
private theorem spareStateMeasure_compl_avoidsTwo : spareStateMeasure avoidsTwoᶜ = 0 := by
  rw [show avoidsTwoᶜ = ⋃ n : ℕ, {x : ℕ → Fin 3 | x n = 2} by ext x; simp [avoidsTwo]]
  exact measure_iUnion_null fun n =>
    (spareStateMeasure_setOf_apply_eq n 2).trans spareStateLaw_singleton_two

/-- The prescribed opening of the sample path: `0, 0, 1, 1`. -/
private def openingWord : ℕ → Fin 3 := fun i => if i ≤ 1 then 0 else 1

/-- The cylinder of sequences opening with `0, 0, 1, 1`. -/
private def opening : Set (ℕ → Fin 3) :=
  Set.pi (↑({0, 1, 2, 3} : Finset ℕ)) fun i => {openingWord i}

private theorem mem_opening {x : ℕ → Fin 3} :
    x ∈ opening ↔ x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 1 ∧ x 3 = 1 := by
  simp [opening, openingWord]

/-- The opening has probability `16⁻¹`, in particular positive probability. -/
private theorem spareStateMeasure_opening : spareStateMeasure opening = (16 : ℝ≥0∞)⁻¹ := by
  rw [spareStateMeasure, opening,
    Measure.infinitePi_pi _ fun i _ => measurableSet_singleton (openingWord i)]
  have hword : ∀ i, openingWord i ≠ 2 := by
    intro i
    unfold openingWord
    split <;> decide
  rw [Finset.prod_congr rfl fun i _ =>
    spareStateLaw_singleton_of_ne_two (hword i), Finset.prod_const]
  norm_num
  rw [← ENNReal.inv_pow]
  norm_num

/-- The successor array of the example read at a sample path. -/
private theorem successorProcess_spareStateProcess_apply (p : Fin 3 × ℕ) (x : ℕ → Fin 3) :
    successorProcess spareStateProcess p x = successorArray x p.1 p.2 :=
  successorProcess_apply spareStateProcess p x

/-- The successor-array entries the opening pins down: the spare row's head is `0`, while the
second entry of the row of `0` and the head of the row of `1` are both `1`. -/
private theorem successorArray_of_mem_opening {x : ℕ → Fin 3} (hx : x ∈ opening)
    (h2 : x ∈ avoidsTwo) :
    successorArray x 2 0 = 0 ∧ successorArray x 0 1 = 1 ∧ successorArray x 1 0 = 1 := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := mem_opening.1 hx
  refine ⟨?_, ?_, ?_⟩
  · rw [successorArray_eq_of_forall_ne h2, hx1]
  · have hcount : visitCount x 0 1 = 1 := by
      rw [visitCount_succ_of_eq hx0, visitCount_zero]
    rw [successorArray_def, visitTime_eq_iff.2 (Or.inl ⟨hx1, hcount⟩), hx2]
  · have hcount : visitCount x 1 2 = 0 := by
      refine visitCount_eq_zero_of_forall_ne fun i hi => ?_
      interval_cases i
      · rw [hx0]; decide
      · rw [hx1]; decide
    rw [successorArray_def, visitTime_eq_iff.2 (Or.inl ⟨hx2, hcount⟩), hx3]

/-- **The spare row is tied to the head of the row the path starts in.** For every sequence that
avoids the spare letter, the spare row's head repeats one of the two heads that are genuinely
read. -/
private theorem successorArray_two_zero_eq {x : ℕ → Fin 3} (h2 : x ∈ avoidsTwo) :
    successorArray x 2 0 = successorArray x 0 0 ∨
      successorArray x 2 0 = successorArray x 1 0 := by
  have hcases : ∀ a : Fin 3, a ≠ 2 → a = 0 ∨ a = 1 := by decide
  rw [successorArray_eq_successorArray_zero_of_forall_ne h2]
  rcases hcases (x 0) (h2 0) with h0 | h0 <;> rw [h0]
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The array event of the tie: the head of the spare row agrees with the head of the row of `0`
or with the head of the row of `1`. -/
private def tiedSpareRow : Set (Fin 3 × ℕ → Fin 3) :=
  {A | A (2, 0) = A (0, 0) ∨ A (2, 0) = A (1, 0)}

private theorem measurableSet_setOf_apply_eq_apply (p q : Fin 3 × ℕ) :
    MeasurableSet {A : Fin 3 × ℕ → Fin 3 | A p = A q} := by
  have h : {A : Fin 3 × ℕ → Fin 3 | A p = A q} =
      (fun A : Fin 3 × ℕ → Fin 3 => (A p, A q)) ⁻¹' {y : Fin 3 × Fin 3 | y.1 = y.2} := rfl
  rw [h]
  exact ((measurable_pi_apply p).prodMk (measurable_pi_apply q))
    (Set.to_countable _).measurableSet

private theorem measurableSet_tiedSpareRow : MeasurableSet tiedSpareRow :=
  (measurableSet_setOf_apply_eq_apply (2, 0) (0, 0)).union
    (measurableSet_setOf_apply_eq_apply (2, 0) (1, 0))

/-- The family of row permutations that breaks the tie: swap the first two entries of the row of
the letter `0`, and leave the other two rows alone. It moves only two cells. -/
private def swapRowZeroHead : Fin 3 → Equiv.Perm ℕ :=
  fun a => if a = 0 then Equiv.swap 0 1 else 1

private theorem swapRowZeroHead_zero : swapRowZeroHead 0 = Equiv.swap 0 1 := by
  rw [swapRowZeroHead]
  simp

private theorem swapRowZeroHead_of_ne {a : Fin 3} (ha : a ≠ 0) : swapRowZeroHead a = 1 := by
  rw [swapRowZeroHead]
  simp [ha]

private theorem measurable_successorProcess_reindex (π : Fin 3 → Equiv.Perm ℕ) :
    Measurable fun x : ℕ → Fin 3 => fun p : Fin 3 × ℕ =>
      successorProcess spareStateProcess (p.1, π p.1 p.2) x := by
  refine Measurable.of_eval fun p => ?_
  simp only [successorProcess_spareStateProcess_apply]
  exact measurable_successorArray_apply p.1 (π p.1 p.2) (measurableSet_singleton p.1)

/-- **The successor array of a recurrent Markov exchangeable process need not be row
exchangeable.** Row exchangeability would move the head of the row of `0` while leaving the spare
row where it is, and the two are tied by
`TauCeti.successorArray_eq_successorArray_zero_of_forall_ne`. On the positive-probability opening
`0, 0, 1, 1` the tie is broken, so the reindexed array almost never satisfies an identity the
original array always satisfies.

Together with `spareStateProcess_markovExchangeable` and `spareStateProcess_recurrent` this shows
that the row-exchangeability input of
`TauCeti.Probability.mixedMarkovChain_of_rowExchangeable_successorProcess` cannot be obtained from
recurrence and Markov exchangeability alone: it has to be restricted to the rows the process
visits. -/
theorem spareStateProcess_not_rowExchangeable_successorProcess :
    ¬ RowExchangeable spareStateMeasure (successorProcess spareStateProcess) := by
  intro hrow
  have hmeas₁ := measurable_successorProcess_reindex swapRowZeroHead
  have hmeas₀ : Measurable fun x : ℕ → Fin 3 => fun p : Fin 3 × ℕ =>
      successorProcess spareStateProcess p x := by
    refine Measurable.of_eval fun p => ?_
    simp only [successorProcess_spareStateProcess_apply]
    exact measurable_successorArray_apply p.1 p.2 (measurableSet_singleton p.1)
  -- The original array always lies in the tie event.
  have horig : spareStateMeasure
      ((fun x (p : Fin 3 × ℕ) => successorProcess spareStateProcess p x) ⁻¹'
        tiedSpareRow) = 1 := by
    refine le_antisymm prob_le_one ?_
    have havoid : spareStateMeasure avoidsTwo = 1 :=
      (prob_compl_eq_zero_iff measurableSet_avoidsTwo).1 spareStateMeasure_compl_avoidsTwo
    rw [← havoid]
    refine measure_mono fun x hx => ?_
    simpa only [Set.mem_preimage, tiedSpareRow, Set.mem_ofPred_eq,
      successorProcess_spareStateProcess_apply] using successorArray_two_zero_eq hx
  -- Row exchangeability would transport that to the reindexed array.
  have hswap : spareStateMeasure
      ((fun x (p : Fin 3 × ℕ) =>
        successorProcess spareStateProcess (p.1, swapRowZeroHead p.1 p.2) x) ⁻¹'
          tiedSpareRow) = 1 := by
    rw [← Measure.map_apply hmeas₁ measurableSet_tiedSpareRow,
      rowExchangeable_def.1 hrow swapRowZeroHead,
      Measure.map_apply hmeas₀ measurableSet_tiedSpareRow]
    exact horig
  -- But the opening breaks the tie, and it has positive probability.
  have hcompl := (prob_compl_eq_zero_iff (hmeas₁ measurableSet_tiedSpareRow)).2 hswap
  have hnull : spareStateMeasure (opening ∩ avoidsTwo) = 0 := by
    refine measure_mono_null (fun x hx => ?_) hcompl
    obtain ⟨h0, h1, h2⟩ := successorArray_of_mem_opening hx.1 hx.2
    simp only [Set.mem_compl_iff, Set.mem_preimage, tiedSpareRow, Set.mem_ofPred_eq,
      successorProcess_spareStateProcess_apply, swapRowZeroHead_zero,
      swapRowZeroHead_of_ne (by decide : (1 : Fin 3) ≠ 0),
      swapRowZeroHead_of_ne (by decide : (2 : Fin 3) ≠ 0), Equiv.Perm.one_apply,
      Equiv.swap_apply_left, h0, h1, h2]
    decide
  rw [measure_inter_conull spareStateMeasure_compl_avoidsTwo] at hnull
  have h16 : (16 : ℝ≥0∞)⁻¹ = 0 := by rw [← spareStateMeasure_opening, hnull]
  exact ENNReal.inv_ne_zero.2 (by simp) h16

end Probability

end TauCeti

end

end
