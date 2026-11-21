/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Substitution.Basic
public import TauCeti.Computability.SingleOracle.Evaln

/-!
# Bounded oracle substitution and use

An outer program can be run against a table of bounded computations of its query program.
Only the entries read by the outer run need to converge. An entry is supplied when the query
program halts within the allotted fuel, with use at most the prescribed bound on the base oracle.

The two simulations relate this way of running the programs to substitution in the program
syntax. Inlining a successful outer run adds at most the inner fuel to its own fuel. Conversely,
a successful inlined run can be replayed when the query program gets at least the inlined fuel
at every address and the use bound covers the inlined run's recorded base-oracle use. This
recorded use is the least bound that permits replay with bounded query answers.
-/

public section

namespace TauCeti.Oracle.Single.Code

variable {σ : ℕ → Option ℕ} {c d : Code} {j k u x : ℕ} {r : Halt}

private theorem evaln_succ_use_eq_zero_of_basic
    (hc : c = zero ∨ c = succ ∨ c = left ∨ c = right)
    (h : evaln σ (k + 1) c x = some r) : r.use = 0 := by
  rcases hc with rfl | rfl | rfl | rfl <;> simp_all

/-- An outer run using bounded query answers can be inlined by adding the query fuel to its own
fuel. The inlined run has the same output and obeys the bound on the base-oracle use. -/
theorem exists_evaln_subst_of_evaln_boundedAnswers
    (h : evaln (d.boundedAnswers σ j u) k c x = some r) :
    ∃ t, evaln σ (j + k) (c.subst d) x = some t ∧ t.output = r.output ∧ t.use ≤ u := by
  induction k generalizing c x r with
  | zero => simp at h
  | succ k ih =>
    induction c generalizing x r <;> simp only [Nat.add_succ, zero_subst, succ_subst,
      left_subst, right_subst, oracle_subst, pair_subst, comp_subst, prec_subst, rfind'_subst]
    case zero | succ | left | right =>
      have hzero := evaln_succ_use_eq_zero_of_basic (by simp) h
      exact ⟨r, evaln_mono (by omega) (evaln_eq_some_of_use_eq_zero σ h hzero), rfl,
        by simp [hzero]⟩
    case oracle =>
      obtain ⟨-, _, ha, rfl⟩ := evaln_succ_oracle_eq_some.1 h
      obtain ⟨t, ht, hu, rfl⟩ := boundedAnswers_eq_some_iff.1 ha
      exact ⟨t, evaln_mono (by omega) ht, rfl, hu⟩
    case pair cf cg hf hg =>
      obtain ⟨hx, f, g, h₁, h₂, rfl⟩ := evaln_succ_pair_eq_some.1 h
      obtain ⟨f', hf', ef, huf⟩ := hf h₁
      obtain ⟨g', hg', eg, hug⟩ := hg h₂
      exact ⟨_, evaln_succ_pair_eq_some.2 ⟨by omega, _, _, hf', hg', rfl⟩,
        by simp [ef, eg], max_le huf hug⟩
    case comp cf cg hf hg =>
      obtain ⟨hx, g, f, h₁, h₂, rfl⟩ := evaln_succ_comp_eq_some.1 h
      obtain ⟨g', hg', eg, hug⟩ := hg h₁
      obtain ⟨f', hf', ef, huf⟩ := hf h₂
      exact ⟨_, evaln_succ_comp_eq_some.2 ⟨by omega, _, _, hg', eg ▸ hf', rfl⟩, ef, max_le hug huf⟩
    case prec cf cg hf hg =>
      obtain ⟨⟨a, m⟩, rfl⟩ := Nat.pairEquiv.surjective x
      cases m with
      | zero =>
        obtain ⟨hx, h⟩ := evaln_succ_prec_zero_eq_some.1 h
        obtain ⟨t, ht, he, hu⟩ := hf h
        exact ⟨t, evaln_succ_prec_zero_eq_some.2 ⟨by omega, ht⟩, he, hu⟩
      | succ m =>
        obtain ⟨hx, i, g, hi, hg₀, rfl⟩ := evaln_succ_prec_succ_eq_some.1 h
        obtain ⟨i', hi', ei, hui⟩ := ih hi
        obtain ⟨g', hg', eg, hug⟩ := hg hg₀
        rw [prec_subst] at hi'
        exact ⟨_, evaln_succ_prec_succ_eq_some.2 ⟨by omega, _, _, hi', ei ▸ hg', rfl⟩,
          eg, max_le hui hug⟩
    case rfind' cf hf =>
      rw [← Nat.pair_unpair x] at h ⊢
      obtain ⟨hx, f, h₀, h⟩ := evaln_succ_rfind'_eq_some.1 h
      obtain ⟨f', hf', ef, huf⟩ := hf h₀
      rcases h with ⟨hz, rfl⟩ | ⟨hn, t, ht, rfl⟩
      · exact ⟨_, evaln_succ_rfind'_eq_some.2 ⟨by omega, _, hf', .inl ⟨ef.trans hz, rfl⟩⟩, rfl, huf⟩
      · obtain ⟨t', ht', et, hut⟩ := ih ht
        exact ⟨_, evaln_succ_rfind'_eq_some.2
          ⟨by omega, _, hf', .inr ⟨ef ▸ hn, _, by simpa only [rfind'_subst] using ht', rfl⟩⟩,
          et, max_le huf hut⟩

/-! ### Replay and least-use bounds -/

/-- A successful inlined run can be replayed by supplying bounded answers of the query program.
Fuel at least the inlined fuel and a use bound at least its recorded use suffice for the
intermediate addresses read by the replay. Other entries may remain undefined.
The replay has the same output. Its recorded use is in the intermediate oracle. -/
theorem exists_evaln_boundedAnswers_of_evaln_subst (h : evaln σ k (c.subst d) x = some r)
    (hj : k ≤ j) (hu : r.use ≤ u) :
    ∃ t, evaln (d.boundedAnswers σ j u) k c x = some t ∧ t.output = r.output := by
  induction k generalizing c x r with
  | zero => simp at h
  | succ k ih =>
    induction c generalizing x r <;> simp only [zero_subst, succ_subst, left_subst,
      right_subst, oracle_subst, pair_subst, comp_subst, prec_subst, rfind'_subst] at h
    case zero | succ | left | right =>
      have hzero := evaln_succ_use_eq_zero_of_basic (by simp) h
      exact ⟨r, evaln_eq_some_of_use_eq_zero _ h hzero, rfl⟩
    case oracle =>
      exact ⟨_, evaln_succ_oracle_eq_some.2
        ⟨by have := evaln_bound h; omega, _, boundedAnswers_eq_some_iff.2
          ⟨r, evaln_mono hj h, hu, rfl⟩, rfl⟩, rfl⟩
    case pair cf cg hf hg =>
      obtain ⟨hx, f, g, hf₀, hg₀, rfl⟩ := evaln_succ_pair_eq_some.1 h
      obtain ⟨f', hf', ef⟩ := hf hf₀ ((le_max_left _ _).trans hu)
      obtain ⟨g', hg', eg⟩ := hg hg₀ ((le_max_right _ _).trans hu)
      exact ⟨_, evaln_succ_pair_eq_some.2 ⟨hx, _, _, hf', hg', rfl⟩, by simp [ef, eg]⟩
    case comp cf cg hf hg =>
      obtain ⟨hx, g, f, hg₀, hf₀, rfl⟩ := evaln_succ_comp_eq_some.1 h
      obtain ⟨g', hg', eg⟩ := hg hg₀ ((le_max_left _ _).trans hu)
      obtain ⟨f', hf', ef⟩ := hf hf₀ ((le_max_right _ _).trans hu)
      exact ⟨_, evaln_succ_comp_eq_some.2 ⟨hx, _, _, hg', eg ▸ hf', rfl⟩, ef⟩
    case prec cf cg hf hg =>
      obtain ⟨⟨a, m⟩, rfl⟩ := Nat.pairEquiv.surjective x
      cases m with
      | zero =>
        obtain ⟨hx, h⟩ := evaln_succ_prec_zero_eq_some.1 h
        obtain ⟨t, ht, he⟩ := hf h hu
        exact ⟨t, evaln_succ_prec_zero_eq_some.2 ⟨hx, ht⟩, he⟩
      | succ m =>
        obtain ⟨hx, i, g, hi, hg₀, rfl⟩ := evaln_succ_prec_succ_eq_some.1 h
        rw [← prec_subst] at hi
        obtain ⟨i', hi', ei⟩ := ih hi (k.le_succ.trans hj) ((le_max_left _ _).trans hu)
        obtain ⟨g', hg', eg⟩ := hg hg₀ ((le_max_right _ _).trans hu)
        exact ⟨_, evaln_succ_prec_succ_eq_some.2 ⟨hx, _, _, hi', ei ▸ hg', rfl⟩, eg⟩
    case rfind' cf hf =>
      rw [← Nat.pair_unpair x] at h ⊢
      obtain ⟨hx, f, hf₀, ⟨hz, rfl⟩ | ⟨hn, t, ht, rfl⟩⟩ := evaln_succ_rfind'_eq_some.1 h
      · obtain ⟨f', hf', ef⟩ := hf hf₀ hu
        exact ⟨_, evaln_succ_rfind'_eq_some.2 ⟨hx, _, hf', .inl ⟨ef.trans hz, rfl⟩⟩, rfl⟩
      · obtain ⟨f', hf', ef⟩ := hf hf₀ ((le_max_left _ _).trans hu)
        rw [← rfind'_subst] at ht
        obtain ⟨t', ht', et⟩ := ih ht (k.le_succ.trans hj) ((le_max_right _ _).trans hu)
        exact ⟨_, evaln_succ_rfind'_eq_some.2 ⟨hx, _, hf', .inr ⟨ef ▸ hn, _, ht', rfl⟩⟩, et⟩

/-- The recorded use of a successful inlined run is the least bound on the base-oracle prefix
that supports any successful replay using bounded query answers. -/
theorem exists_evaln_boundedAnswers_iff_use_le (h : evaln σ k (c.subst d) x = some r) :
    (∃ j k' t, evaln (d.boundedAnswers σ j u) k' c x = some t) ↔ r.use ≤ u := by
  constructor
  · rintro ⟨j, k', t, ht⟩
    obtain ⟨s, hs, -, hu⟩ := exists_evaln_subst_of_evaln_boundedAnswers ht
    exact evaln_unique h hs ▸ hu
  · intro hu
    obtain ⟨t, ht, -⟩ := exists_evaln_boundedAnswers_of_evaln_subst h le_rfl hu
    exact ⟨k, k, t, ht⟩

end TauCeti.Oracle.Single.Code
