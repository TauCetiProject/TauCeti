/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Priority.Injury.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.Lattice

/-!
# Counting the causes of injury

An injury budget counts distinct numbers, rather than actions or stages. If every actual
injuring entry is supplied by a higher-priority contributor, and contributor `i` supplies at
most `b i` distinct numbers, the total injury budget is at most the sum of these bounds.
In particular, contributors supplying at most one number each give a budget of `e` for
requirement `e`.

The contribution sets may overlap and the stages may enumerate several numbers at once.
Neither theorem assumes monotone stages: repeated entry of the same number does not enlarge
the injury-number set. Monotonicity is needed separately to bound injury stages or obtain an
injury-free tail, using the results of `TauCeti.Computability.Priority.Injury.Basic`.

The covering hypothesis concerns every entry in `injuriesAt`, so a contribution ledger alone
does not establish the bound. Each conclusion includes finiteness, since `Set.ncard` by itself
does not distinguish an infinite set from an empty one.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VII.1.
-/

public section

namespace TauCeti.Priority

open Set

variable {A : ℕ → Finset ℕ} {r : ℕ → ℕ → Option ℕ} {e : ℕ}

/-- Distinct numbers injuring `e` are bounded by the sum of the higher-priority contribution
budgets. The hypothesis `hcover` accounts for actual injuring entries, not just a ledger of
possible contributions. Neither disjoint contributions nor monotone stages are required. -/
theorem finite_injurySet_and_ncard_le_sum_of_causes (C : ℕ → Set ℕ) (b : ℕ → ℕ)
    (hbudget : ∀ i < e, (C i).Finite ∧ (C i).ncard ≤ b i)
    (hcover : ∀ s x, x ∈ injuriesAt A r e s → ∃ i < e, x ∈ C i) :
    (injurySet A r e).Finite ∧ (injurySet A r e).ncard ≤ ∑ i ∈ Finset.range e, b i := by
  have hsub : injurySet A r e ⊆ ⋃ i ∈ Finset.range e, C i := by
    intro x hx
    obtain ⟨s, hs⟩ := mem_injurySet.mp hx
    obtain ⟨i, hi, hxi⟩ := hcover s x hs
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr hi, hxi⟩
  have hfin : (⋃ i ∈ Finset.range e, C i).Finite :=
    (Finset.range e).finite_toSet.biUnion fun i hi =>
      (hbudget i (Finset.mem_range.mp hi)).1
  refine ⟨hfin.subset hsub, (ncard_le_ncard hsub hfin).trans ?_⟩
  exact ((Finset.range e).set_ncard_biUnion_le C).trans
    (Finset.sum_le_sum fun i hi => (hbudget i (Finset.mem_range.mp hi)).2)

/-- If every higher-priority contributor supplies at most one distinct number, there are at
most `e` distinct numbers injuring `e`. Empty contribution sets are allowed. This counts
numbers even when they enter together or the same number enters repeatedly. -/
theorem finite_injurySet_and_ncard_le_of_subsingleton_causes (C : ℕ → Set ℕ)
    (hunique : ∀ i < e, (C i).Subsingleton)
    (hcover : ∀ s x, x ∈ injuriesAt A r e s → ∃ i < e, x ∈ C i) :
    (injurySet A r e).Finite ∧ (injurySet A r e).ncard ≤ e := by
  simpa using finite_injurySet_and_ncard_le_sum_of_causes C (fun _ => 1)
    (fun i hi => ⟨(hunique i hi).finite,
      (Set.ncard_le_one (hunique i hi).finite).mpr (hunique i hi)⟩) hcover

end TauCeti.Priority
