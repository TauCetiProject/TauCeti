/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.RankBounded

/-!
# Examples: the Friedman–Stanley obstruction

For an analytic class the obstruction is the contrapositive of the non-Borelness of Borel complete
isomorphism relations, whatever the rank: the class is an analytic subset of itself, so some level
is the whole class. In particular no rank on the coded graphs satisfies both hypotheses.
-/

public section

open FirstOrder FirstOrder.Language MeasureTheory Ordinal TauCeti RelationalConfiguration Set

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]

-- For an analytic class, hypothesis (b) makes some level `K_α` with `α < ω₁` the whole class.
example {K : Set (RelationalConfiguration L ℕ)} (hK : AnalyticSet K)
    (ρ : RelationalConfiguration L ℕ → Ordinal.{0})
    (hb : ∀ A ⊆ K, AnalyticSet A → ∃ α < ω₁, ∀ c ∈ A, ρ c ≤ α) :
    ∃ α < ω₁, K ∩ {c | ρ c ≤ α} = K := by
  obtain ⟨α, hα, hρ⟩ := hb K subset_rfl hK
  exact ⟨α, hα, inter_eq_left.2 hρ⟩

-- With `ρ = 0` every level is the whole class, and the obstruction says that a class whose
-- isomorphism relation is Borel is not Borel complete.
example {K : Set (RelationalConfiguration L ℕ)}
    (h : MeasurableSet {p : K × K | classIso K p.1 p.2}) : ¬ BorelComplete K := by
  refine not_borelComplete_of_rank_bounded (fun _ ↦ 0) (fun α _ ↦ ?_)
    fun _ _ _ ↦ ⟨0, omega_pos 1, fun _ _ ↦ le_rfl⟩
  rw [show K ∩ {_c | (0 : Ordinal.{0}) ≤ α} = K by simp]
  exact h

-- No rank on the coded graphs satisfies both hypotheses: they are Borel complete.
example (ρ : RelationalConfiguration Language.graph ℕ → Ordinal.{0}) :
    ¬ ((∀ α < ω₁, MeasurableSet {p : ↥(graphClass ∩ {c | ρ c ≤ α}) ×
        ↥(graphClass ∩ {c | ρ c ≤ α}) | classIso (graphClass ∩ {c | ρ c ≤ α}) p.1 p.2}) ∧
      ∀ A ⊆ graphClass, AnalyticSet A → ∃ α < ω₁, ∀ c ∈ A, ρ c ≤ α) :=
  fun h ↦ not_borelComplete_of_rank_bounded ρ h.1 h.2 borelComplete_graphClass
