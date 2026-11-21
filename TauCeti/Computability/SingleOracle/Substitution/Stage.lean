/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Substitution.Bounded
public import TauCeti.Computability.SingleOracle.Stage
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite

/-!
# Oracle substitution at normalized stages

The raw inlining and replay results extend to stages that also bound the program index and
output. A finite list of successful inlined runs admits replay at a common stage preserving
each output exactly when the shared base-oracle use bound covers the largest use recorded by
the original inlined runs. Each replay records its intermediate-oracle use.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, III.1.7–9.
-/

public section

open Encodable Filter

namespace TauCeti.Oracle.Single.Code

variable {σ : ℕ → Option ℕ} {c d : Code} {j k u x : ℕ} {r : Halt}

/-- Inlining a successful outer stage run gives a successful compiled stage run with the same
output at any stage large enough for the combined fuel, program index and output. -/
theorem exists_evalStage_subst_of_evalStage_boundedAnswers {s : ℕ}
    (h : evalStage (d.boundedAnswers σ j u) k c x = some r)
    (hks : j + k ≤ s) (hcs : encode (c.subst d) < s) :
    ∃ t, evalStage σ s (c.subst d) x = some t ∧ t.output = r.output ∧ t.use ≤ u := by
  obtain ⟨-, hr, hy⟩ := evalStage_eq_some_iff.1 h
  obtain ⟨t, ht, he, hu⟩ := exists_evaln_subst_of_evaln_boundedAnswers hr
  exact ⟨t, evalStage_eq_some_of_evaln ht hks hcs (he ▸ hy.trans_le (by omega)), he, hu⟩

/-- A successful compiled stage run can be replayed once the outer stage reaches the compiled
stage and exceeds the original program's index. Query fuel at least the compiled stage
suffices when the use bound covers the compiled run's use. -/
theorem exists_evalStage_boundedAnswers_of_evalStage_subst {s : ℕ}
    (h : evalStage σ k (c.subst d) x = some r) (hj : k ≤ j) (hu : r.use ≤ u)
    (hks : k ≤ s) (hcs : encode c < s) :
    ∃ t, evalStage (d.boundedAnswers σ j u) s c x = some t ∧ t.output = r.output := by
  obtain ⟨-, hr, hy⟩ := evalStage_eq_some_iff.1 h
  obtain ⟨t, ht, he⟩ := exists_evaln_boundedAnswers_of_evaln_subst hr hj hu
  exact ⟨t, evalStage_eq_some_of_evaln ht hks hcs (he ▸ hy.trans_le hks), he⟩

/-- For finitely many successful inlined runs, possibly witnessed at different stages, there
is a common query fuel and outer stage at which replay preserves each output exactly when
the shared bound covers the largest base-oracle use recorded by the original inlined runs.
Each replay records its intermediate-oracle use. Each entry gives an outer program, its input
and the inlined run's outcome. -/
theorem exists_evalStage_boundedAnswers_forall_mem_iff {runs : List (Code × ℕ × Halt)}
    (h : ∀ p ∈ runs, ∃ k, evalStage σ k (p.1.subst d) p.2.1 = some p.2.2) :
    (∃ j s, ∀ p ∈ runs, ∃ t,
      evalStage (d.boundedAnswers σ j u) s p.1 p.2.1 = some t ∧
        t.output = p.2.2.output) ↔ runs.toFinset.sup (fun p => p.2.2.use) ≤ u := by
  classical
  rw [Finset.sup_le_iff]
  simp only [List.mem_toFinset]
  constructor
  · rintro ⟨j, s, hs⟩ p hp
    obtain ⟨k, hk⟩ := h p hp
    obtain ⟨t, ht, -⟩ := hs p hp
    exact (exists_evaln_boundedAnswers_iff_use_le (evalStage_eq_some_iff.1 hk).2.1).1
      ⟨j, s, t, (evalStage_eq_some_iff.1 ht).2.1⟩
  · intro hu
    have houter (p) (hp : p ∈ runs.toFinset) :
        ∀ᶠ s in atTop, ∃ t, evalStage (d.boundedAnswers σ s u) s p.1 p.2.1 = some t ∧
          t.output = p.2.2.output := by
      obtain ⟨k, hk⟩ := h p (List.mem_toFinset.1 hp)
      refine eventually_atTop.2 ⟨max k (encode p.1 + 1), fun s hs => ?_⟩
      have hks : k ≤ s := (le_max_left _ _).trans hs
      exact exists_evalStage_boundedAnswers_of_evalStage_subst hk hks
        (hu p (List.mem_toFinset.1 hp)) hks
        (Nat.lt_of_succ_le ((le_max_right _ _).trans hs))
    obtain ⟨s, hs⟩ := ((eventually_all_finset runs.toFinset).2 houter).exists
    exact ⟨s, s, fun p hp => hs p (List.mem_toFinset.2 hp)⟩

end TauCeti.Oracle.Single.Code
