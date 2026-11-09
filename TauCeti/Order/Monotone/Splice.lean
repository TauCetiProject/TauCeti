/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.WellFounded

/-!
# Diagonal splicing of sequences

Given stages `σ 0, σ 1, …` of sequences, where each stage keeps the first `N j` terms of the
previous one and `N` is strictly increasing, a single sequence agrees with every stage on its
first `N j` terms (`TauCeti.exists_forall_lt_eq_of_strictMono`). This lets a sequence be built by
appending finitely many terms at a time.

## Main results

* `TauCeti.exists_forall_lt_eq_of_strictMono`: the diagonal limit of stages that agree on longer
  and longer prefixes.
-/

public section

namespace TauCeti

/-- **Diagonal splicing.** If the stages `σ j` are sequences such that `σ (j + 1)` agrees with
`σ j` on its first `N j` terms, and `N` is strictly increasing, then a single sequence agrees with
every stage `σ j` on its first `N j` terms. -/
theorem exists_forall_lt_eq_of_strictMono {α : Type*} (σ : ℕ → ℕ → α) {N : ℕ → ℕ}
    (hN : StrictMono N) (hσ : ∀ j, ∀ k < N j, σ (j + 1) k = σ j k) :
    ∃ e : ℕ → α, ∀ j, ∀ k < N j, e k = σ j k := by
  -- Later stages keep the terms of earlier stages.
  have hstable {j j' : ℕ} (hjj' : j ≤ j') {k : ℕ} (hk : k < N j) : σ j' k = σ j k := by
    induction j', hjj' using Nat.le_induction with
    | base => rfl
    | succ j' hjj' ih => exact (hσ j' k (hk.trans_le (hN.monotone hjj'))).trans ih
  refine ⟨fun k => σ (k + 1) k, fun j k hk => ?_⟩
  rcases le_total (k + 1) j with hkj | hjk
  · exact (hstable hkj ((Nat.lt_succ_self k).trans_le (hN.id_le (k + 1)))).symm
  · exact hstable hjk hk

end TauCeti
