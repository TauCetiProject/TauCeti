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

Raw inlining and replay produce runs at normalized stages that also bound the destination
program index and output. A finite list of successful inlined runs admits replay at a common
stage preserving each output exactly when the shared base-oracle use bound covers the largest
use recorded by the original inlined runs. Each replay records its intermediate-oracle use.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, III.1.7–9.
-/

public section

open Encodable Filter

namespace TauCeti.Oracle.Single.Code

variable {σ : ℕ → Option ℕ} {c d : Code} {j k u x : ℕ} {r : Halt}

/-- Inlining a successful raw outer run preserves the output and gives base-oracle use at
most `u` at any stage large enough for the combined fuel, program index and output. -/
theorem exists_evalStage_subst_of_evaln_boundedAnswers {s : ℕ}
    (h : evaln (d.boundedAnswers σ j u) k c x = some r)
    (hks : j + k ≤ s) (hcs : encode (c.subst d) < s) (hy : r.output < s) :
    ∃ t, evalStage σ s (c.subst d) x = some t ∧ t.output = r.output ∧ t.use ≤ u := by
  obtain ⟨t, ht, he, hu⟩ := exists_evaln_subst_of_evaln_boundedAnswers h
  exact ⟨t, evalStage_eq_some_of_evaln ht hks hcs (he ▸ hy), he, hu⟩

/-- A successful raw compiled run can be replayed once the outer stage reaches the compiled
fuel and exceeds the original program's index and the output. Query fuel at least the compiled
fuel suffices when the use bound covers the compiled run's base-oracle use. The replay
preserves the output and records its use in the intermediate oracle. -/
theorem exists_evalStage_boundedAnswers_of_evaln_subst {s : ℕ}
    (h : evaln σ k (c.subst d) x = some r) (hj : k ≤ j) (hu : r.use ≤ u)
    (hks : k ≤ s) (hcs : encode c < s) (hy : r.output < s) :
    ∃ t, evalStage (d.boundedAnswers σ j u) s c x = some t ∧ t.output = r.output := by
  obtain ⟨t, ht, he⟩ := exists_evaln_boundedAnswers_of_evaln_subst h hj hu
  exact ⟨t, evalStage_eq_some_of_evaln ht hks hcs (he ▸ hy), he⟩

/-- For finitely many successful raw inlined runs, possibly witnessed at different fuels, there
is a common query fuel and outer stage at which replay preserves each output exactly when
the shared bound covers the largest base-oracle use recorded by the original inlined runs.
Each replay records its intermediate-oracle use. Each entry gives an outer program, its input
and the inlined run's outcome. -/
theorem exists_forall_mem_exists_evalStage_boundedAnswers_iff_sup_use_le
    {runs : List (Code × ℕ × Halt)}
    (h : ∀ p ∈ runs, ∃ k, evaln σ k (p.1.subst d) p.2.1 = some p.2.2) :
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
    exact (exists_evaln_boundedAnswers_iff_use_le hk).1
      ⟨j, s, t, (evalStage_eq_some_iff.1 ht).2.1⟩
  · intro hu
    have houter (p) (hp : p ∈ runs.toFinset) :
        ∀ᶠ s in atTop, ∃ t, evalStage (d.boundedAnswers σ s u) s p.1 p.2.1 = some t ∧
          t.output = p.2.2.output := by
      obtain ⟨k, hk⟩ := h p (List.mem_toFinset.1 hp)
      refine eventually_atTop.2 ⟨max k (max (encode p.1) p.2.2.output + 1), fun s hs => ?_⟩
      have hks : k ≤ s := (le_max_left _ _).trans hs
      exact exists_evalStage_boundedAnswers_of_evaln_subst hk hks
        (hu p (List.mem_toFinset.1 hp)) hks (by omega) (by omega)
    obtain ⟨s, hs⟩ := ((eventually_all_finset runs.toFinset).2 houter).exists
    exact ⟨s, s, fun p hp => hs p (List.mem_toFinset.2 hp)⟩

end TauCeti.Oracle.Single.Code
