/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Code

/-!
# Bounded evaluation of oracle programs, with use

This file defines `TauCeti.Oracle.Single.Code.evaln σ k c n`, the run of the program `c` on the
input `n` with fuel `k` against the oracle answers `σ : ℕ → Option ℕ`. A successful run records its
output together with its **use**: one more than the largest oracle address it queried, or `0` when
it made no query. An answer `σ z = none` means that no answer is supplied at `z`, not a negative
answer; a run that queries there fails. A finite oracle string `l` is the case `fun z => l[z]?`,
and a total oracle `O : ℕ → ℕ` the case `fun z => some (O z)`.

Bounded evaluation follows Mathlib's `Nat.Partrec.Code.evaln`: at fuel `k + 1` a run fails on
inputs above `k`, and the recursions of `prec` and `rfind'` consume fuel. Hence a run at fuel `k`
has input below `k` and queries only addresses below `k`, so its use is at most `k`.

Use is what makes oracle computations finitary: a successful run reads only the answers below its
use, so it succeeds unchanged against any answers agreeing there, and its output is then a value of
the program relative to every oracle extending those answers.

## Main definitions

* `TauCeti.Oracle.Single.Code.Halt`: the output and use of a successful run.
* `TauCeti.Oracle.Single.Code.evaln`: bounded evaluation against oracle answers.

## Main results

* `TauCeti.Oracle.Single.Code.evaln_succ_pair_eq_some` and its neighbours: the clauses of bounded
  evaluation, one for each program constructor.
* `TauCeti.Oracle.Single.Code.evaln_mono`: a successful run persists, with the same output and
  use, at larger fuel; `TauCeti.Oracle.Single.Code.evaln_unique`: its output and use do not
  depend on the fuel.
* `TauCeti.Oracle.Single.Code.evaln_bound`, `TauCeti.Oracle.Single.Code.evaln_use_le`: the input
  and the use of a run at fuel `k` are below `k`, respectively at most `k`.
* `TauCeti.Oracle.Single.Code.evaln_eq_some_of_eqOn`: the **use principle**, a run succeeds with
  the same output and use against answers agreeing below its use.
* `TauCeti.Oracle.Single.Code.evaln_sound`: the output of a successful run is a value of the
  program relative to every oracle whose values include the answers below the use.
* `TauCeti.Oracle.Single.Code.mem_eval_iff_exists_evaln`: when the answers are exactly the values
  of an oracle, the values of a program relative to that oracle are exactly the outputs of its
  successful runs.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.1, in
  particular the use principle III.1.9.
* The definition and the proofs of persistence, soundness and completeness follow Mathlib's
  `Nat.Partrec.Code.evaln`, `Nat.Partrec.Code.evaln_mono`, `Nat.Partrec.Code.evaln_sound` and
  `Nat.Partrec.Code.evaln_complete`, extended by the oracle instruction and the use.
-/

public section

namespace TauCeti.Oracle.Single.Code

/-- A successful finite run of a program: its `output`, and its `use`, one more than the largest
oracle address it queried, or `0` when it made no query. -/
@[ext]
structure Halt where
  /-- The output of the run. -/
  output : ℕ
  /-- One more than the largest address queried, or `0` when the run made no query. -/
  use : ℕ
  deriving DecidableEq

/-- Bounded evaluation of a program with fuel `k` against the oracle answers `σ`, where `σ z = none`
means that no answer is supplied at `z`. A successful run returns its output and its use; see
`TauCeti.Oracle.Single.Code.Halt`.

As in `Nat.Partrec.Code.evaln`, at fuel `k + 1` each instruction fails on inputs above `k`, and the
recursive calls of `prec` and `rfind'` at the next argument use fuel `k`. The `oracle` instruction
queries `σ` at its input `n` and has use `n + 1`; the other basic instructions have use `0`, and a
compound program has the largest use of the runs it makes. -/
def evaln (σ : ℕ → Option ℕ) : ℕ → Code → ℕ → Option Halt
  | 0, _ => fun _ => none
  | k + 1, zero => fun n => do
    guard (n ≤ k)
    return ⟨0, 0⟩
  | k + 1, succ => fun n => do
    guard (n ≤ k)
    return ⟨n + 1, 0⟩
  | k + 1, left => fun n => do
    guard (n ≤ k)
    return ⟨n.unpair.1, 0⟩
  | k + 1, right => fun n => do
    guard (n ≤ k)
    return ⟨n.unpair.2, 0⟩
  | k + 1, oracle => fun n => do
    guard (n ≤ k)
    let y ← σ n
    return ⟨y, n + 1⟩
  | k + 1, pair cf cg => fun n => do
    guard (n ≤ k)
    let df ← evaln σ (k + 1) cf n
    let dg ← evaln σ (k + 1) cg n
    return ⟨Nat.pair df.output dg.output, max df.use dg.use⟩
  | k + 1, comp cf cg => fun n => do
    guard (n ≤ k)
    let dg ← evaln σ (k + 1) cg n
    let df ← evaln σ (k + 1) cf dg.output
    return ⟨df.output, max dg.use df.use⟩
  | k + 1, prec cf cg => fun n => do
    guard (n ≤ k)
    n.unpaired fun a n =>
      n.casesOn (evaln σ (k + 1) cf a) fun y => do
        let di ← evaln σ k (prec cf cg) (Nat.pair a y)
        let d ← evaln σ (k + 1) cg (Nat.pair a (Nat.pair y di.output))
        return ⟨d.output, max di.use d.use⟩
  | k + 1, rfind' cf => fun n => do
    guard (n ≤ k)
    n.unpaired fun a m => do
      let dx ← evaln σ (k + 1) cf (Nat.pair a m)
      if dx.output = 0 then
        return ⟨m, dx.use⟩
      else
        let d ← evaln σ k (rfind' cf) (Nat.pair a (m + 1))
        return ⟨d.output, max dx.use d.use⟩

variable {σ : ℕ → Option ℕ}

/-- Nothing succeeds without fuel. -/
@[simp]
theorem evaln_zero (c : Code) (n : ℕ) : evaln σ 0 c n = none := by
  rw [evaln]

variable {k n : ℕ} {d : Halt}

/-- The `zero` instruction returns `0` without queries. -/
@[simp]
theorem evaln_succ_zero_eq_some : evaln σ (k + 1) zero n = some d ↔ n ≤ k ∧ d = ⟨0, 0⟩ := by
  simp only [evaln, bind, Option.bind_eq_some_iff, Option.guard_eq_some', exists_const]
  grind

/-- The `succ` instruction returns the successor of its input without queries. -/
@[simp]
theorem evaln_succ_succ_eq_some : evaln σ (k + 1) succ n = some d ↔ n ≤ k ∧ d = ⟨n + 1, 0⟩ := by
  simp only [evaln, bind, Option.bind_eq_some_iff, Option.guard_eq_some', exists_const]
  grind

/-- The `left` instruction returns the first component of its input without queries. -/
@[simp]
theorem evaln_succ_left_eq_some :
    evaln σ (k + 1) left n = some d ↔ n ≤ k ∧ d = ⟨n.unpair.1, 0⟩ := by
  simp only [evaln, bind, Option.bind_eq_some_iff, Option.guard_eq_some', exists_const]
  grind

/-- The `right` instruction returns the second component of its input without queries. -/
@[simp]
theorem evaln_succ_right_eq_some :
    evaln σ (k + 1) right n = some d ↔ n ≤ k ∧ d = ⟨n.unpair.2, 0⟩ := by
  simp only [evaln, bind, Option.bind_eq_some_iff, Option.guard_eq_some', exists_const]
  grind

/-- The `oracle` instruction returns the answer at its input `n`, when one is supplied, with use
`n + 1`. -/
@[simp]
theorem evaln_succ_oracle_eq_some :
    evaln σ (k + 1) oracle n = some d ↔ n ≤ k ∧ ∃ y, σ n = some y ∧ d = ⟨y, n + 1⟩ := by
  simp only [evaln, bind, Option.bind_eq_some_iff, Option.guard_eq_some', exists_const]
  grind

/-- `pair cf cg` pairs the outputs of runs of `cf` and `cg`, with the larger of their uses. -/
@[simp]
theorem evaln_succ_pair_eq_some {cf cg : Code} :
    evaln σ (k + 1) (pair cf cg) n = some d ↔ n ≤ k ∧ ∃ df dg,
      evaln σ (k + 1) cf n = some df ∧ evaln σ (k + 1) cg n = some dg ∧
        d = ⟨Nat.pair df.output dg.output, max df.use dg.use⟩ := by
  simp only [evaln, bind, Option.bind_eq_some_iff, Option.guard_eq_some', exists_const]
  grind

/-- `comp cf cg` runs `cg`, then `cf` on its output, with the larger of their uses. -/
@[simp]
theorem evaln_succ_comp_eq_some {cf cg : Code} :
    evaln σ (k + 1) (comp cf cg) n = some d ↔ n ≤ k ∧ ∃ dg df,
      evaln σ (k + 1) cg n = some dg ∧ evaln σ (k + 1) cf dg.output = some df ∧
        d = ⟨df.output, max dg.use df.use⟩ := by
  simp only [evaln, bind, Option.bind_eq_some_iff, Option.guard_eq_some', exists_const]
  grind

/-- Primitive recursion at zero runs the base program. -/
@[simp]
theorem evaln_succ_prec_zero_eq_some {cf cg : Code} {a : ℕ} :
    evaln σ (k + 1) (prec cf cg) (Nat.pair a 0) = some d ↔
      Nat.pair a 0 ≤ k ∧ evaln σ (k + 1) cf a = some d := by
  simp only [evaln, Nat.unpaired, Nat.unpair_pair, Nat.rec_zero, bind, Option.bind_eq_some_iff,
    Option.guard_eq_some', exists_const]

/-- Primitive recursion at a successor runs the recursion at the previous argument with one less
fuel, then the step program, with the larger of their uses. -/
@[simp]
theorem evaln_succ_prec_succ_eq_some {cf cg : Code} {a y : ℕ} :
    evaln σ (k + 1) (prec cf cg) (Nat.pair a (y + 1)) = some d ↔ Nat.pair a (y + 1) ≤ k ∧
      ∃ di d', evaln σ k (prec cf cg) (Nat.pair a y) = some di ∧
        evaln σ (k + 1) cg (Nat.pair a (Nat.pair y di.output)) = some d' ∧
          d = ⟨d'.output, max di.use d'.use⟩ := by
  simp only [evaln, Nat.unpaired, Nat.unpair_pair, bind, Option.bind_eq_some_iff,
    Option.guard_eq_some', exists_const]
  grind

/-- `rfind' cf` at `m` runs `cf` at `m`. On output `0` it returns `m`; otherwise it continues the
search at `m + 1` with one less fuel. Its use is the largest use of the runs of `cf` it makes. -/
@[simp]
theorem evaln_succ_rfind'_eq_some {cf : Code} {a m : ℕ} :
    evaln σ (k + 1) (rfind' cf) (Nat.pair a m) = some d ↔ Nat.pair a m ≤ k ∧
      ∃ dx, evaln σ (k + 1) cf (Nat.pair a m) = some dx ∧
        (dx.output = 0 ∧ d = ⟨m, dx.use⟩ ∨ dx.output ≠ 0 ∧
          ∃ d', evaln σ k (rfind' cf) (Nat.pair a (m + 1)) = some d' ∧
            d = ⟨d'.output, max dx.use d'.use⟩) := by
  simp only [evaln, Nat.unpaired, Nat.unpair_pair, bind, Option.bind_eq_some_iff,
    Option.guard_eq_some', exists_const]
  refine and_congr_right fun _ => exists_congr fun dx => and_congr_right fun _ => ?_
  split_ifs with h <;>
    simp only [h, Option.pure_def, Option.some.injEq, Option.bind_eq_some_iff] <;> grind

/-- A successful run at fuel `k` has input below `k`. -/
theorem evaln_bound : ∀ {k c n d}, evaln σ k c n = some d → n < k
  | 0, c, n, d, h => by simp at h
  | k + 1, c, n, d, h => by
    suffices ∀ {o : Option Halt}, (do guard (n ≤ k); o) = some d → n < k + 1 by
      cases c <;> rw [evaln] at h <;> exact this h
    simpa [Option.bind_eq_some_iff] using Nat.lt_succ_of_le

/-- Every input is a pairing `Nat.pair a m`, the form in which the clauses for `prec` and
`rfind'` are stated. -/
private theorem exists_eq_pair (n : ℕ) : ∃ a m, n = Nat.pair a m :=
  ⟨_, _, (Nat.pair_unpair n).symm⟩

/-- **Persistence.** A successful run persists, with the same output and use, at larger fuel. -/
theorem evaln_mono : ∀ {k₁ k₂ c n d}, k₁ ≤ k₂ → evaln σ k₁ c n = some d →
    evaln σ k₂ c n = some d
  | 0, _, _, _, _, _, h => by simp at h
  | k + 1, 0, _, _, _, hl, _ => absurd hl (by omega)
  | k + 1, k₂ + 1, c, n, d, hl, h => by
    have hl' := Nat.le_of_succ_le_succ hl
    induction c generalizing n d with
    | zero | succ | left | right | oracle =>
      simp only [evaln_succ_zero_eq_some, evaln_succ_succ_eq_some, evaln_succ_left_eq_some,
        evaln_succ_right_eq_some, evaln_succ_oracle_eq_some] at h ⊢
      exact ⟨h.1.trans hl', h.2⟩
    | pair cf cg hf hg =>
      rw [evaln_succ_pair_eq_some] at h ⊢
      obtain ⟨hn, df, dg, hdf, hdg, rfl⟩ := h
      exact ⟨hn.trans hl', df, dg, hf _ _ hdf, hg _ _ hdg, rfl⟩
    | comp cf cg hf hg =>
      rw [evaln_succ_comp_eq_some] at h ⊢
      obtain ⟨hn, dg, df, hdg, hdf, rfl⟩ := h
      exact ⟨hn.trans hl', dg, df, hg _ _ hdg, hf _ _ hdf, rfl⟩
    | prec cf cg hf hg =>
      obtain ⟨a, m, rfl⟩ := exists_eq_pair n
      cases m with
      | zero =>
        rw [evaln_succ_prec_zero_eq_some] at h ⊢
        exact ⟨h.1.trans hl', hf _ _ h.2⟩
      | succ m =>
        rw [evaln_succ_prec_succ_eq_some] at h ⊢
        obtain ⟨hn, di, d', hdi, hd', rfl⟩ := h
        exact ⟨hn.trans hl', di, d', evaln_mono hl' hdi, hg _ _ hd', rfl⟩
    | rfind' cf hf =>
      obtain ⟨a, m, rfl⟩ := exists_eq_pair n
      rw [evaln_succ_rfind'_eq_some] at h ⊢
      obtain ⟨hn, dx, hdx, h⟩ := h
      exact ⟨hn.trans hl', dx, hf _ _ hdx,
        h.imp_right (And.imp_right (Exists.imp fun _ => And.imp_left (evaln_mono hl')))⟩

/-- **Uniqueness.** Two successful runs of a program on the same input, at any two fuels, have the
same output and the same use. -/
theorem evaln_unique {k₁ k₂ : ℕ} {c : Code} {d₁ d₂ : Halt} (h₁ : evaln σ k₁ c n = some d₁)
    (h₂ : evaln σ k₂ c n = some d₂) : d₁ = d₂ :=
  Option.some.inj <| (evaln_mono (le_max_left k₁ k₂) h₁).symm.trans
    (evaln_mono (le_max_right k₁ k₂) h₂)

/-- A successful run at fuel `k` has use at most `k`: it queries only addresses below `k`. -/
theorem evaln_use_le : ∀ {k c n d}, evaln σ k c n = some d → d.use ≤ k
  | 0, _, _, _, h => by simp at h
  | k + 1, c, n, d, h => by
    induction c generalizing n d with
    | zero | succ | left | right | oracle =>
      simp only [evaln_succ_zero_eq_some, evaln_succ_succ_eq_some, evaln_succ_left_eq_some,
        evaln_succ_right_eq_some, evaln_succ_oracle_eq_some] at h
      grind
    | pair cf cg hf hg =>
      obtain ⟨-, df, dg, hdf, hdg, rfl⟩ := evaln_succ_pair_eq_some.1 h
      exact max_le (hf _ _ hdf) (hg _ _ hdg)
    | comp cf cg hf hg =>
      obtain ⟨-, dg, df, hdg, hdf, rfl⟩ := evaln_succ_comp_eq_some.1 h
      exact max_le (hg _ _ hdg) (hf _ _ hdf)
    | prec cf cg hf hg =>
      obtain ⟨a, m, rfl⟩ := exists_eq_pair n
      cases m with
      | zero => exact hf _ _ (evaln_succ_prec_zero_eq_some.1 h).2
      | succ m =>
        obtain ⟨-, di, d', hdi, hd', rfl⟩ := evaln_succ_prec_succ_eq_some.1 h
        exact max_le ((evaln_use_le hdi).trans k.le_succ) (hg _ _ hd')
    | rfind' cf hf =>
      obtain ⟨a, m, rfl⟩ := exists_eq_pair n
      obtain ⟨-, dx, hdx, ⟨-, rfl⟩ | ⟨-, d', hd', rfl⟩⟩ := evaln_succ_rfind'_eq_some.1 h
      · exact hf _ dx hdx
      · exact max_le (hf _ _ hdx) ((evaln_use_le hd').trans k.le_succ)

/-- **The use principle.** A successful run against the answers `σ` succeeds with the same output
and use against any answers `τ` agreeing with `σ` below its use. -/
theorem evaln_eq_some_of_eqOn {τ : ℕ → Option ℕ} : ∀ {k c n d}, evaln σ k c n = some d →
    Set.EqOn σ τ (Set.Iio d.use) → evaln τ k c n = some d
  | 0, _, _, _, h, _ => by simp at h
  | k + 1, c, n, d, h, hστ => by
    induction c generalizing n d with
    | zero | succ | left | right =>
      simp only [evaln_succ_zero_eq_some, evaln_succ_succ_eq_some, evaln_succ_left_eq_some,
        evaln_succ_right_eq_some] at h ⊢
      exact h
    | oracle =>
      obtain ⟨hn, y, hy, rfl⟩ := evaln_succ_oracle_eq_some.1 h
      exact evaln_succ_oracle_eq_some.2
        ⟨hn, y, (hστ (Set.mem_Iio.2 n.lt_succ_self)).symm.trans hy, rfl⟩
    | pair cf cg hf hg =>
      obtain ⟨hn, df, dg, hdf, hdg, rfl⟩ := evaln_succ_pair_eq_some.1 h
      exact evaln_succ_pair_eq_some.2 ⟨hn, df, dg,
        hf _ _ hdf (hστ.mono (Set.Iio_subset_Iio (le_max_left _ _))),
        hg _ _ hdg (hστ.mono (Set.Iio_subset_Iio (le_max_right _ _))), rfl⟩
    | comp cf cg hf hg =>
      obtain ⟨hn, dg, df, hdg, hdf, rfl⟩ := evaln_succ_comp_eq_some.1 h
      exact evaln_succ_comp_eq_some.2 ⟨hn, dg, df,
        hg _ _ hdg (hστ.mono (Set.Iio_subset_Iio (le_max_left _ _))),
        hf _ _ hdf (hστ.mono (Set.Iio_subset_Iio (le_max_right _ _))), rfl⟩
    | prec cf cg hf hg =>
      obtain ⟨a, m, rfl⟩ := exists_eq_pair n
      cases m with
      | zero =>
        obtain ⟨hn, h⟩ := evaln_succ_prec_zero_eq_some.1 h
        exact evaln_succ_prec_zero_eq_some.2 ⟨hn, hf _ _ h hστ⟩
      | succ m =>
        obtain ⟨hn, di, d', hdi, hd', rfl⟩ := evaln_succ_prec_succ_eq_some.1 h
        exact evaln_succ_prec_succ_eq_some.2 ⟨hn, di, d',
          evaln_eq_some_of_eqOn hdi (hστ.mono (Set.Iio_subset_Iio (le_max_left _ _))),
          hg _ _ hd' (hστ.mono (Set.Iio_subset_Iio (le_max_right _ _))), rfl⟩
    | rfind' cf hf =>
      obtain ⟨a, m, rfl⟩ := exists_eq_pair n
      obtain ⟨hn, dx, hdx, ⟨hx0, rfl⟩ | ⟨hx0, d', hd', rfl⟩⟩ := evaln_succ_rfind'_eq_some.1 h
      · exact evaln_succ_rfind'_eq_some.2 ⟨hn, dx, hf _ _ hdx hστ, Or.inl ⟨hx0, rfl⟩⟩
      · exact evaln_succ_rfind'_eq_some.2 ⟨hn, dx,
          hf _ _ hdx (hστ.mono (Set.Iio_subset_Iio (le_max_left _ _))), Or.inr ⟨hx0, d',
            evaln_eq_some_of_eqOn hd' (hστ.mono (Set.Iio_subset_Iio (le_max_right _ _))), rfl⟩⟩

/-- **The zero-query case.** A successful run with use `0` succeeds with the same output against
every oracle answers. -/
theorem evaln_eq_some_of_use_eq_zero (τ : ℕ → Option ℕ) {c : Code} (h : evaln σ k c n = some d)
    (hd : d.use = 0) : evaln τ k c n = some d :=
  evaln_eq_some_of_eqOn h <| by simp [hd]

/-- Soundness against answers that are all correct for `O`. -/
private theorem evaln_sound_of_forall {O : ℕ →. ℕ} (hσ : ∀ z y, σ z = some y → y ∈ O z) :
    ∀ {k c n d}, evaln σ k c n = some d → d.output ∈ eval O c n
  | 0, _, _, _, h => by simp at h
  | k + 1, c, n, d, h => by
    induction c generalizing n d with
    | zero => obtain ⟨-, rfl⟩ := evaln_succ_zero_eq_some.1 h; simp
    | succ => obtain ⟨-, rfl⟩ := evaln_succ_succ_eq_some.1 h; simp
    | left => obtain ⟨-, rfl⟩ := evaln_succ_left_eq_some.1 h; simp
    | right => obtain ⟨-, rfl⟩ := evaln_succ_right_eq_some.1 h; simp
    | oracle =>
      obtain ⟨-, y, hy, rfl⟩ := evaln_succ_oracle_eq_some.1 h
      rw [eval_oracle]
      exact hσ _ _ hy
    | pair cf cg hf hg =>
      obtain ⟨-, df, dg, hdf, hdg, rfl⟩ := evaln_succ_pair_eq_some.1 h
      exact mem_eval_pair.2 ⟨_, hf _ _ hdf, _, hg _ _ hdg, rfl⟩
    | comp cf cg hf hg =>
      obtain ⟨-, dg, df, hdg, hdf, rfl⟩ := evaln_succ_comp_eq_some.1 h
      rw [eval_comp]
      exact Part.mem_bind (hg _ _ hdg) (hf _ df hdf)
    | prec cf cg hf hg =>
      obtain ⟨a, m, rfl⟩ := exists_eq_pair n
      cases m with
      | zero =>
        rw [eval_prec_zero]
        exact hf _ _ (evaln_succ_prec_zero_eq_some.1 h).2
      | succ m =>
        obtain ⟨-, di, d', hdi, hd', rfl⟩ := evaln_succ_prec_succ_eq_some.1 h
        rw [eval_prec_succ]
        exact Part.mem_bind (evaln_sound_of_forall hσ hdi) (hg _ d' hd')
    | rfind' cf hf =>
      obtain ⟨a, m, rfl⟩ := exists_eq_pair n
      obtain ⟨-, dx, hdx, ⟨hx0, rfl⟩ | ⟨hx0, d', hd', rfl⟩⟩ := evaln_succ_rfind'_eq_some.1 h
      · exact mem_eval_rfind'.2 ⟨_, hf _ _ hdx, Or.inl ⟨hx0, rfl⟩⟩
      · exact mem_eval_rfind'.2
          ⟨_, hf _ _ hdx, Or.inr ⟨hx0, evaln_sound_of_forall hσ (d := d') hd'⟩⟩

/-- **Soundness.** If a run against the answers `σ` succeeds, and every answer `σ` gives below its
use is a value of the oracle `O`, then the output of the run is a value of the program relative
to `O`. Answers at or above the use are not read, so they need not be correct. -/
theorem evaln_sound {O : ℕ →. ℕ} {k : ℕ} {c : Code} (h : evaln σ k c n = some d)
    (hσ : ∀ z < d.use, ∀ y, σ z = some y → y ∈ O z) : d.output ∈ eval O c n := by
  classical
  -- discard the answers at or above the use, which the run does not read
  refine evaln_sound_of_forall (σ := fun z => if z < d.use then σ z else none) ?_
    (evaln_eq_some_of_eqOn h fun z hz => by simp [Set.mem_Iio.1 hz])
  intro z y hy
  split_ifs at hy with hz
  exact hσ z hz y hy

/-- **Completeness.** If the answers `σ` give every value of the oracle `O`, every value of a
program relative to `O` is the output of a successful run against `σ` at some fuel. The answers
may go beyond `O` at addresses where `O` is undefined. -/
theorem exists_evaln_eq_some_of_mem_eval {O : ℕ →. ℕ} (hσ : ∀ z y, y ∈ O z → σ z = some y)
    {c : Code} {y : ℕ} (h : y ∈ eval O c n) : ∃ k d, evaln σ k c n = some d ∧ d.output = y := by
  induction c generalizing n y with
  | zero =>
    rw [eval_zero, Part.mem_some_iff] at h
    exact ⟨n + 1, _, evaln_succ_zero_eq_some.2 ⟨le_rfl, rfl⟩, h.symm⟩
  | succ =>
    rw [eval_succ, Part.mem_some_iff] at h
    exact ⟨n + 1, _, evaln_succ_succ_eq_some.2 ⟨le_rfl, rfl⟩, h.symm⟩
  | left =>
    rw [eval_left, Part.mem_some_iff] at h
    exact ⟨n + 1, _, evaln_succ_left_eq_some.2 ⟨le_rfl, rfl⟩, h.symm⟩
  | right =>
    rw [eval_right, Part.mem_some_iff] at h
    exact ⟨n + 1, _, evaln_succ_right_eq_some.2 ⟨le_rfl, rfl⟩, h.symm⟩
  | oracle =>
    rw [eval_oracle] at h
    exact ⟨n + 1, _, evaln_succ_oracle_eq_some.2 ⟨le_rfl, y, hσ n y h, rfl⟩, rfl⟩
  | pair cf cg hf hg =>
    obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_eval_pair.1 h
    obtain ⟨k₁, d₁, hd₁, rfl⟩ := hf h₁
    obtain ⟨k₂, d₂, hd₂, rfl⟩ := hg h₂
    have := evaln_bound hd₁
    exact ⟨max k₁ k₂ + 1, _, evaln_succ_pair_eq_some.2
      ⟨by omega, d₁, d₂, evaln_mono (by omega) hd₁, evaln_mono (by omega) hd₂, rfl⟩, rfl⟩
  | comp cf cg hf hg =>
    rw [eval_comp] at h
    obtain ⟨z, hz, hy⟩ := Part.mem_bind_iff.1 h
    obtain ⟨k₁, d₁, hd₁, rfl⟩ := hg hz
    obtain ⟨k₂, d₂, hd₂, rfl⟩ := hf hy
    have := evaln_bound hd₁
    exact ⟨max k₁ k₂ + 1, _, evaln_succ_comp_eq_some.2
      ⟨by omega, d₁, d₂, evaln_mono (by omega) hd₁, evaln_mono (by omega) hd₂, rfl⟩, rfl⟩
  | prec cf cg hf hg =>
    obtain ⟨a, m, rfl⟩ := exists_eq_pair n
    induction m generalizing y with
    | zero =>
      rw [eval_prec_zero] at h
      obtain ⟨k, d, hd, rfl⟩ := hf h
      exact ⟨max k (Nat.pair a 0) + 1, d,
        evaln_succ_prec_zero_eq_some.2 ⟨by omega, evaln_mono (by omega) hd⟩, rfl⟩
    | succ m ih =>
      rw [eval_prec_succ] at h
      obtain ⟨i, hi, hy⟩ := Part.mem_bind_iff.1 h
      obtain ⟨k₁, d₁, hd₁, rfl⟩ := ih hi
      obtain ⟨k₂, d₂, hd₂, rfl⟩ := hg hy
      exact ⟨max (max k₁ k₂) (Nat.pair a (m + 1)) + 1, _, evaln_succ_prec_succ_eq_some.2
        ⟨by omega, d₁, d₂, evaln_mono (by omega) hd₁, evaln_mono (by omega) hd₂, rfl⟩, rfl⟩
  | rfind' cf hf =>
    obtain ⟨a, m, rfl⟩ := exists_eq_pair n
    -- induction on the distance `y - m` the search still has to cover
    obtain ⟨j, rfl⟩ : ∃ j, y = j + m := ⟨y - m, by have := le_of_mem_eval_rfind' h; omega⟩
    induction j generalizing m with
    | zero =>
      obtain ⟨x, hx, ⟨rfl, -⟩ | ⟨-, hy⟩⟩ := mem_eval_rfind'.1 h
      · obtain ⟨k, dx, hdx, hx0⟩ := hf hx
        exact ⟨max k (Nat.pair a m) + 1, _, evaln_succ_rfind'_eq_some.2
          ⟨by omega, dx, evaln_mono (by omega) hdx, Or.inl ⟨hx0, rfl⟩⟩, by simp⟩
      · have := le_of_mem_eval_rfind' hy
        omega
    | succ j ih =>
      obtain ⟨x, hx, ⟨-, hy⟩ | ⟨hx0, hy⟩⟩ := mem_eval_rfind'.1 h
      · omega
      · obtain ⟨k₁, dx, hdx, rfl⟩ := hf hx
        obtain ⟨k₂, d', hd', hd'y⟩ := ih (m + 1) (by rwa [← Nat.add_assoc, Nat.add_right_comm])
        exact ⟨max (max k₁ k₂) (Nat.pair a m) + 1, _, evaln_succ_rfind'_eq_some.2
          ⟨by omega, dx, evaln_mono (by omega) hdx,
            Or.inr ⟨hx0, d', evaln_mono (by omega) hd', rfl⟩⟩, by simp [hd'y]; omega⟩

/-- **Correspondence with evaluation.** If the answers `σ` are exactly the values of the oracle
`O`, the values of a program relative to `O` are exactly the outputs of its successful runs
against `σ`. -/
theorem mem_eval_iff_exists_evaln {O : ℕ →. ℕ} (hσ : ∀ z y, σ z = some y ↔ y ∈ O z)
    {c : Code} {y : ℕ} : y ∈ eval O c n ↔ ∃ k d, evaln σ k c n = some d ∧ d.output = y :=
  ⟨exists_evaln_eq_some_of_mem_eval fun z y => (hσ z y).2, fun ⟨_, _, h, hy⟩ =>
    hy ▸ evaln_sound h fun z _ y' hy' => (hσ z y').1 hy'⟩

end TauCeti.Oracle.Single.Code
