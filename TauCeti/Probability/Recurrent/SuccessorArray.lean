/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.LastExit
public import TauCeti.Probability.Recurrent.Basic

/-!
# Recurrence and successor arrays

For a recurrent path, the visit times of a visited state are genuine, strictly increasing visits,
and the visit counts along them run through every natural number; so the successor-array row of
such a state is an infinite list of genuine transitions, read off at those times. Rows indexed by
unvisited states remain unconstrained and may contain `Nat.nth`'s junk values.

Combined with `successorArray_def`, which reads a row entry off the visit time, these are the
facts that make every entry of a visited-state row a genuine transition of the path. Recovering
the path from its successor array needs none of this — `pathOfSuccessors_successorArray` inverts
the decomposition of an arbitrary sequence — but an argument that permutes the entries within a
row does need them to be real transitions rather than junk.

The same recurrence makes row permutations that move finitely many cells on attained rows
eventually last-exit admissible (`Recurrent.ae_eventually_lastExitAdmissible`), the hypothesis
under which `TauCeti.Combinatorics.Enumerative.LastExit` rebuilds a finite prefix from reindexed
successor rows with the same endpoint and transition counts.

## Main results

* `TauCeti.Probability.Recurrent.ae_apply_visitTime` and
  `TauCeti.Probability.Recurrent.ae_strictMono_visitTime` — the visit times of a visited state are
  genuine, strictly increasing visits;
* `TauCeti.Probability.Recurrent.ae_visitCount_visitTime` and
  `TauCeti.Probability.Recurrent.ae_tendsto_visitCount_atTop` — the visit counts along them run
  through every natural number, so every visited row is infinite;
* `TauCeti.Probability.Recurrent.ae_eventually_lastExitAdmissible` — a family of row
  permutations moving almost surely finitely many cells on attained rows is almost surely
  last-exit admissible for every long enough prefix.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
* S. Fortini, L. Ladelli, G. Petris, and E. Regazzini, "On mixtures of distributions of Markov
  chains", *Stochastic Processes and their Applications* 100 (2002), 147–165, Lemma 1(b).
-/

public section

noncomputable section

open Filter MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → α}

/-- **The visit times of a visited state are genuine visits.** Off a recurrent path the later
entries of `visitTime` are `Nat.nth`'s junk value; on one they are the times at which the process
really is at that state. -/
theorem Recurrent.ae_apply_visitTime (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k j : ℕ, X (visitTime (fun n => X n ω) (X k ω) j) ω = X k ω := by
  filter_upwards [h.ae_infinite_setOf_eq] with ω hω k j
  exact apply_visitTime_of_infinite (hω k) j

/-- The visit times of a visited state of a recurrent process are strictly increasing, so the
successor-array row of that state is read off at distinct times, in order. -/
theorem Recurrent.ae_strictMono_visitTime (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, StrictMono (visitTime (fun n => X n ω) (X k ω)) := by
  filter_upwards [h.ae_infinite_setOf_eq] with ω hω k
  exact visitTime_strictMono_of_infinite (hω k)

/-- The `j`-th visit of a recurrent process to one of its states really is preceded by exactly
`j` earlier visits. -/
theorem Recurrent.ae_visitCount_visitTime (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k j : ℕ,
      visitCount (fun n => X n ω) (X k ω) (visitTime (fun n => X n ω) (X k ω) j) = j := by
  classical
  filter_upwards [h.ae_infinite_setOf_eq] with ω hω k j
  rw [visitCount_eq_count, visitTime_def]
  exact Nat.count_nth_of_infinite (hω k) j

/-- **Each visited row of the successor array is infinite.** A recurrent process accumulates
unboundedly many visits to every state it attains. -/
theorem Recurrent.ae_tendsto_visitCount_atTop (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, Tendsto (visitCount (fun n => X n ω) (X k ω)) atTop atTop := by
  filter_upwards [h.ae_visitCount_visitTime] with ω hω k
  refine tendsto_atTop_atTop.2 fun b => ⟨visitTime (fun n => X n ω) (X k ω) b, fun n hn => ?_⟩
  calc b = visitCount (fun n => X n ω) (X k ω) (visitTime (fun n => X n ω) (X k ω) b) :=
        (hω k b).symm
    _ ≤ visitCount (fun n => X n ω) (X k ω) n := visitCount_monotone _ _ hn

/-- **A family of successor-row permutations moving almost surely finitely many cells on attained
rows is almost surely eventually last-exit admissible for a recurrent process.** This is the
almost-sure form of `TauCeti.eventually_lastExitAdmissible_of_recurrent`; only the cells on rows
the sampled path attains need be finitely many, so a finitely supported `π` is a special case. -/
theorem Recurrent.ae_eventually_lastExitAdmissible (h : Recurrent μ X)
    (π : α → Equiv.Perm ℕ)
    (hπ : ∀ᵐ ω ∂μ, {p : α × ℕ | π p.1 p.2 ≠ p.2 ∧ ∃ t, X t ω = p.1}.Finite) :
    ∀ᵐ ω ∂μ, ∀ᶠ m in atTop, LastExitAdmissible π (fun n => X n ω) m := by
  filter_upwards [h.ae_infinite_setOf_eq, hπ] with ω hω hπω
  exact eventually_lastExitAdmissible_of_recurrent
    (fun _ _ ⟨t, ht⟩ => by simpa only [ht] using hω t) hπω

end Probability

end TauCeti

end

end
