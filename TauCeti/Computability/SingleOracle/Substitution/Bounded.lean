/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Substitution.Basic
public import TauCeti.Computability.SingleOracle.Stage

/-!
# Bounded oracle substitution and use

An outer program can be run against a table of bounded computations of its query program.
Only the entries read by the outer run need to converge. An entry is supplied when the query
program halts within the allotted fuel, with use at most the prescribed bound on the base oracle.

The two simulations relate this way of running the programs to substitution in the program
syntax. Inlining a successful outer run adds at most the inner fuel to its own fuel. Conversely,
a successful inlined run can be reproduced by giving the query program the inlined fuel at every
address. For a fixed successful inlined run, its recorded base-oracle use is the least bound
that permits a successful replay of that run using bounded query answers.

These are raw fuel comparisons. The normalized-stage results additionally bound the program
index and output, as in R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987,
III.1.7–9.
-/

public section

open Encodable Primrec

namespace TauCeti.Oracle.Single.Code

/-- The answer computed by `d` at an address using fuel `k` and at most the first `u` base-oracle
coordinates. A missing run or a run using a larger prefix supplies no answer. -/
def boundedAnswers (d : Code) (σ : ℕ → Option ℕ) (k u : ℕ) (x : ℕ) : Option ℕ :=
  (evaln σ k d x).bind fun h => if h.use ≤ u then some h.output else none

variable {σ : ℕ → Option ℕ} {c d : Code} {j k u x y : ℕ} {r : Halt}

/-- A bounded answer is supplied precisely by a successful run within the use bound. -/
@[simp]
theorem boundedAnswers_eq_some_iff :
    d.boundedAnswers σ j u x = some y ↔
      ∃ h, evaln σ j d x = some h ∧ h.use ≤ u ∧ h.output = y := by
  simp only [boundedAnswers, Option.bind_eq_some_iff]
  refine exists_congr fun h => and_congr_right fun _ => ?_
  split_ifs <;> simp_all

/-- A bounded answer is missing if evaluation fails or the successful run exceeds the use bound. -/
@[simp]
theorem boundedAnswers_eq_none_iff :
    d.boundedAnswers σ j u x = none ↔
      evaln σ j d x = none ∨ ∃ h, evaln σ j d x = some h ∧ u < h.use := by
  cases h : evaln σ j d x with
  | none => simp [boundedAnswers, h]
  | some t =>
    by_cases ht : t.use ≤ u
    · simp [boundedAnswers, h, ht, not_lt.2 ht]
    · simp [boundedAnswers, h, ht, lt_of_not_ge ht]

/-- If the supplied answers represent `O`, the values computed by `d` are exactly the bounded
answers supplied at some common fuel and use bound. -/
theorem mem_eval_iff_exists_boundedAnswers {O : ℕ →. ℕ}
    (hσ : ∀ z v, σ z = some v ↔ v ∈ O z) :
    y ∈ eval O d x ↔ ∃ k, d.boundedAnswers σ k k x = some y := by
  rw [mem_eval_iff_exists_evaln hσ]
  constructor
  · rintro ⟨k, h, hk, rfl⟩
    exact ⟨k, boundedAnswers_eq_some_iff.2 ⟨h, hk, evaln_use_le hk, rfl⟩⟩
  · rintro ⟨k, hk⟩
    obtain ⟨h, hh, -, hy⟩ := boundedAnswers_eq_some_iff.1 hk
    exact ⟨k, h, hh, hy⟩

/-- Enlarging either bound retains any answer already supplied by a query program. -/
theorem boundedAnswers_eq_some_of_le {j' u' : ℕ} (hj : j ≤ j') (hu : u ≤ u')
    (h : d.boundedAnswers σ j u x = some y) : d.boundedAnswers σ j' u' x = some y := by
  obtain ⟨r, hr, hru, rfl⟩ := boundedAnswers_eq_some_iff.1 h
  exact boundedAnswers_eq_some_iff.2 ⟨r, evaln_mono hj hr, hru.trans hu, rfl⟩

/-- Query answers depend only on the allowed prefix of the base oracle, including when the
answer is missing. -/
theorem boundedAnswers_eq_of_eqOn {τ : ℕ → Option ℕ} (h : Set.EqOn σ τ (Set.Iio u)) :
    d.boundedAnswers σ j u x = d.boundedAnswers τ j u x := by
  apply Option.ext
  intro v
  simp only [boundedAnswers_eq_some_iff]
  constructor <;> rintro ⟨r, hr, hu, rfl⟩
  · exact ⟨r, evaln_eq_some_of_eqOn hr (h.mono (Set.Iio_subset_Iio hu)), hu, rfl⟩
  · exact ⟨r, evaln_eq_some_of_eqOn hr (h.symm.mono (Set.Iio_subset_Iio hu)), hu, rfl⟩

/-- Bounded query answers are primitive recursive in finite oracle data, the two bounds,
the program and the address. -/
theorem primrec_boundedAnswers {α : Type*} [Primcodable α]
    {answers : α → ℕ → Option ℕ} (hσ : Primrec₂ answers) :
    Primrec fun p : (α × ℕ × Code × ℕ) × ℕ =>
      p.1.2.2.1.boundedAnswers (answers p.1.1) p.1.2.1 p.2 p.1.2.2.2 := by
  refine option_bind ((primrec_evaln hσ).comp fst) <| .mk <| Primrec.ite
    (Primrec.nat_le.comp (Halt.primrec_use.comp snd) (snd.comp fst))
    (option_some.comp (Halt.primrec_output.comp snd)) (const none)

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
      obtain ⟨a, m, rfl⟩ : ∃ a m, x = Nat.pair a m := ⟨_, _, (Nat.pair_unpair x).symm⟩
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

/-! ### A counterexample to the maximum fuel bound -/

private def searchAnswers (x : ℕ) : Option ℕ :=
  if x = 1 then some 1 else if x = 2 then some 0 else none

private theorem pair_zero_zero : Nat.pair 0 0 = 0 := by decide
private theorem pair_zero_one : Nat.pair 0 1 = 1 := by decide

private def shiftQuery : Code :=
  comp oracle succ

private theorem evaln_shiftQuery_zero :
    evaln searchAnswers 3 shiftQuery 0 = some ⟨1, 2⟩ :=
  evaln_succ_comp_eq_some.2 ⟨by decide, ⟨1, 0⟩, ⟨1, 2⟩, by simp, by simp [searchAnswers], rfl⟩

private theorem evaln_shiftQuery_one :
    evaln searchAnswers 3 shiftQuery 1 = some ⟨0, 3⟩ :=
  evaln_succ_comp_eq_some.2 ⟨by decide, ⟨2, 0⟩, ⟨0, 3⟩, by simp, by simp [searchAnswers], rfl⟩

private theorem evaln_shiftQuery_one_fuel_two :
    evaln searchAnswers 2 shiftQuery 1 = none := by
  apply Option.eq_none_iff_forall_ne_some.2
  intro r h
  rw [shiftQuery, evaln_succ_comp_eq_some] at h
  obtain ⟨-, g, f, hg, hf, -⟩ := h
  obtain ⟨-, rfl⟩ := evaln_succ_succ_eq_some.1 hg
  exact (lt_irrefl 2) (evaln_bound hf)

-- The outer search sees nonzero at address zero, then zero at address one.
private theorem evaln_search_boundedAnswers :
    evaln (shiftQuery.boundedAnswers searchAnswers 3 3) 3 (rfind' oracle) (Nat.pair 0 0) =
      some ⟨1, 2⟩ := by
  have ha : shiftQuery.boundedAnswers searchAnswers 3 3 (Nat.pair 0 0) = some 1 := by
    rw [pair_zero_zero]
    exact boundedAnswers_eq_some_iff.2 ⟨⟨1, 2⟩, evaln_shiftQuery_zero, by decide, rfl⟩
  have hb : shiftQuery.boundedAnswers searchAnswers 3 3 (Nat.pair 0 1) = some 0 := by
    rw [pair_zero_one]
    exact boundedAnswers_eq_some_iff.2 ⟨⟨0, 3⟩, evaln_shiftQuery_one, le_rfl, rfl⟩
  have htail :
      evaln (shiftQuery.boundedAnswers searchAnswers 3 3) 2 (rfind' oracle) (Nat.pair 0 1) =
        some ⟨1, 2⟩ :=
    evaln_succ_rfind'_eq_some.2 ⟨by decide, ⟨0, 2⟩,
      evaln_succ_oracle_eq_some.2 ⟨by decide, 0, hb, rfl⟩, .inl ⟨rfl, rfl⟩⟩
  exact evaln_succ_rfind'_eq_some.2 ⟨by decide, ⟨1, 1⟩,
    evaln_succ_oracle_eq_some.2 ⟨by decide, 1, ha, rfl⟩, .inr ⟨by decide, _, htail, rfl⟩⟩

private theorem evaln_search_subst_fuel_three :
    evaln searchAnswers 3 ((rfind' oracle).subst shiftQuery) (Nat.pair 0 0) = none := by
  apply Option.eq_none_iff_forall_ne_some.2
  intro t ht
  rw [rfind'_subst, oracle_subst, evaln_succ_rfind'_eq_some] at ht
  obtain ⟨-, f, hf, hcase⟩ := ht
  rw [pair_zero_zero] at hf
  have hf' : f = ⟨1, 2⟩ := evaln_unique hf evaln_shiftQuery_zero
  subst f
  obtain ⟨-, g, hg, -⟩ := hcase.resolve_left (by simp)
  obtain ⟨-, v, hv, -⟩ := evaln_succ_rfind'_eq_some.1 hg
  rw [pair_zero_one, evaln_shiftQuery_one_fuel_two] at hv
  contradiction

/-- The maximum of the two separate fuels can be too small for inlining, even when the
intermediate oracle's answers are furnished by a single successful query at each address read. -/
theorem exists_evaln_boundedAnswers_and_evaln_subst_eq_none_at_max :
    ∃ (σ : ℕ → Option ℕ) (c d : Code) (x j k : ℕ) (r : Halt),
      evaln (d.boundedAnswers σ j j) k c x = some r ∧
        evaln σ (max j k) (c.subst d) x = none :=
  ⟨searchAnswers, rfind' oracle, shiftQuery, Nat.pair 0 0, 3, 3, ⟨1, 2⟩,
    evaln_search_boundedAnswers, evaln_search_subst_fuel_three⟩

/-! ### Replay and least-use bounds -/

/-- A successful inlined run can be replayed by supplying bounded answers of the query program.
Fuel at least the inlined fuel and use at least its actual use suffice for every such answer.
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
      obtain ⟨a, m, rfl⟩ : ∃ a m, x = Nat.pair a m := ⟨_, _, (Nat.pair_unpair x).symm⟩
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

-- With a large enough fuel the inlined run has base use three.
private theorem evaln_search_subst :
    evaln searchAnswers 4 ((rfind' oracle).subst shiftQuery) (Nat.pair 0 0) = some ⟨1, 3⟩ := by
  rw [rfind'_subst, oracle_subst, evaln_succ_rfind'_eq_some]
  have htail : evaln searchAnswers 3 (rfind' shiftQuery) (Nat.pair 0 1) = some ⟨1, 3⟩ :=
    evaln_succ_rfind'_eq_some.2
      ⟨by decide, ⟨0, 3⟩, pair_zero_one.symm ▸ evaln_shiftQuery_one, .inl ⟨rfl, rfl⟩⟩
  exact ⟨by decide, ⟨1, 2⟩, pair_zero_zero.symm ▸ evaln_mono (by decide) evaln_shiftQuery_zero,
    .inr ⟨by decide, _, htail, rfl⟩⟩

example : ¬ ∃ j k t, evaln (shiftQuery.boundedAnswers searchAnswers j 2) k (rfind' oracle)
      (Nat.pair 0 0) = some t := by
  rw [exists_evaln_boundedAnswers_iff_use_le evaln_search_subst]
  decide

example : ∃ t, evaln searchAnswers 6 ((rfind' oracle).subst shiftQuery) (Nat.pair 0 0) =
    some t ∧ t.output = 1 ∧ t.use ≤ 3 :=
  exists_evaln_subst_of_evaln_boundedAnswers evaln_search_boundedAnswers

/-- Inlining a successful outer stage run gives a successful compiled stage run with the same
output at any stage large enough for the combined fuel, program index and output. -/
theorem exists_evalStage_subst_of_evalStage_boundedAnswers {s : ℕ}
    (h : evalStage (d.boundedAnswers σ j u) k c x = some r)
    (hks : j + k ≤ s) (hcs : encode (c.subst d) < s) :
    ∃ t, evalStage σ s (c.subst d) x = some t ∧ t.output = r.output ∧ t.use ≤ u := by
  obtain ⟨-, hr, hy⟩ := evalStage_eq_some_iff.1 h
  obtain ⟨t, ht, he, hu⟩ := exists_evaln_subst_of_evaln_boundedAnswers hr
  exact ⟨t, evalStage_eq_some_of_evaln ht hks hcs (he ▸ hy.trans_le (by omega)), he, hu⟩

/-- A successful compiled stage run can be replayed as an outer stage run. The stage must allow
the original program's index, and the query bounds must cover the compiled stage and use. -/
theorem exists_evalStage_boundedAnswers_of_evalStage_subst {s : ℕ}
    (h : evalStage σ k (c.subst d) x = some r) (hj : k ≤ j) (hu : r.use ≤ u)
    (hks : k ≤ s) (hcs : encode c < s) :
    ∃ t, evalStage (d.boundedAnswers σ j u) s c x = some t ∧ t.output = r.output := by
  obtain ⟨-, hr, hy⟩ := evalStage_eq_some_iff.1 h
  obtain ⟨t, ht, he⟩ := exists_evaln_boundedAnswers_of_evaln_subst hr hj hu
  exact ⟨t, evalStage_eq_some_of_evaln ht hks hcs (he ▸ hy.trans_le hks), he⟩

/-- For finitely many successful inlined runs, possibly witnessed at different stages, the same
query fuel and outer stage can replay them all exactly when the permitted base-oracle use covers
their largest use. Each entry records an outer program, its input and the inlined run's outcome. -/
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
    let stage (p : ↥runs.toFinset) := (h p.val (List.mem_toFinset.1 p.property)).choose
    let k := runs.toFinset.attach.sup stage
    have hk (p : ↥runs.toFinset) :
        evalStage σ k (p.val.1.subst d) p.val.2.1 = some p.val.2.2 :=
      evalStage_mono (Finset.le_sup (f := stage) (Finset.mem_attach _ p))
        (h p.val (List.mem_toFinset.1 p.property)).choose_spec
    let s := max k (runs.toFinset.sup fun p => encode p.1 + 1)
    refine ⟨k, s, fun p hp => exists_evalStage_boundedAnswers_of_evalStage_subst
      (hk ⟨p, List.mem_toFinset.2 hp⟩) le_rfl (hu p hp) (le_max_left _ _) ?_⟩
    have hidx := (Finset.le_sup
      (f := fun p : Code × ℕ × Halt => encode p.1 + 1) (List.mem_toFinset.2 hp))
    exact (Nat.lt_succ_self _).trans_le (hidx.trans (le_max_right _ _))

end TauCeti.Oracle.Single.Code
