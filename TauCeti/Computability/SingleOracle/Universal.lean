/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Primrec
import TauCeti.Computability.SingleOracle.Staged.Search

/-!
# A universal oracle program

This file constructs a **universal program** `TauCeti.Oracle.Single.Code.universal`: a single
program which, relative to every total oracle `O : ℕ → ℕ`, computes on the input `Nat.pair e x`
the value of the program numbered `e` on `x`. The program is the same for every oracle. This is
the uniform form of evaluation: adequacy (`TauCeti.Oracle.Single.Code.exists_code`) gives, for
one fixed oracle, a program for each partial function recursive in it, whereas the universal
program works for all oracles at once.

On the input `Nat.pair e x`, the universal program searches for the least fuel `k` at which the
run of the program numbered `e` on `x` against the finite oracle string `O 0, …, O (k - 1)`
succeeds, and returns the output of that run. The search is built via
`TauCeti.Oracle.Single.Code.exists_code_rfindOpt_answers`. A successful run is correct by
the use principle, and every computation relative to `O` is found at some fuel
(`TauCeti.Oracle.Single.Code.mem_eval_iff_exists_evaln_range_map`).
Mathlib's `Nat.Partrec.Code.eval_eq_rfindOpt` gives the analogous bounded search for ordinary
programs.

The construction needs a total oracle: the universal program queries the oracle at every address
below the fuel before running anything, so relative to a partial oracle it would diverge at an
undefined address that the simulated program never queries.

## Main definitions

* `TauCeti.Oracle.Single.Code.universal`: a universal program.

## Main results

* `TauCeti.Oracle.Single.Code.eval_universal`: the universal program computes the value of the
  program numbered `e` on `x` from `Nat.pair e x`, relative to every total oracle.
* `TauCeti.Oracle.Single.Code.recursiveIn₂_eval`: evaluation of programs is recursive in a total
  oracle, uniformly in the program. This is the oracle-relative form of Mathlib's
  `Nat.Partrec.Code.eval_part`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter I.3 (the
  enumeration theorem) and Chapter III.1 (its relativization).
-/

public section

open Encodable Denumerable Primrec

namespace TauCeti.Oracle.Single.Code

/-! ### The universal program -/

/-- The run searched for by the universal program: on `(n, k, l)`, the run of the program numbered
by the first coordinate of `n` on its second coordinate, with fuel `k`, against the oracle
string `l`. -/
private def run (p : ℕ × ℕ × List ℕ) : Option Halt :=
  evaln (fun z => p.2.2[z]?) p.2.1 (ofNat Code p.1.unpair.1) p.1.unpair.2

private theorem primrec_run : Primrec run :=
  primrec_evaln_list.comp <| (snd.comp snd).pair <| (fst.comp snd).pair <|
    ((Primrec.ofNat _).comp (fst.comp (Primrec.unpair.comp fst))).pair
      (snd.comp (Primrec.unpair.comp fst))

/-- A universal program exists. -/
private theorem exists_universal : ∃ u : Code, ∀ (O : ℕ → ℕ) (e x : ℕ),
    eval (O : ℕ →. ℕ) u (Nat.pair e x) =
      eval (O : ℕ →. ℕ) (ofNat Code e) x := by
  obtain ⟨u, hu⟩ := exists_code_rfindOpt_answers (g := fun p => (run p).map Halt.output)
    (option_map₁ Halt.primrec_output |>.comp primrec_run)
  refine ⟨u, fun O e x => ?_⟩
  rw [hu O (Nat.pair e x)]
  ext y
  rw [Nat.rfindOpt_mono, mem_eval_iff_exists_evaln_range_map]
  · simp only [run, Nat.unpair_pair, Option.mem_def, Option.map_eq_some_iff]
  · intro z s t hst hs
    simp only [run, Nat.unpair_pair, Option.mem_def, Option.map_eq_some_iff,
      evaln_range_map] at hs ⊢
    obtain ⟨d, hd, hy⟩ := hs
    exact ⟨d, evaln_mono hst hd, hy⟩

/-- A **universal program**: relative to every total oracle `O`, on the input `Nat.pair e x` it
computes the value of the program numbered `e` on `x`. -/
noncomputable def universal : Code :=
  exists_universal.choose

/-- Relative to every total oracle, the universal program computes the value of the program
numbered `e` on `x` from `Nat.pair e x`. -/
@[simp]
theorem eval_universal (O : ℕ → ℕ) (e x : ℕ) :
    eval (O : ℕ →. ℕ) universal (Nat.pair e x) =
      eval (O : ℕ →. ℕ) (ofNat Code e) x :=
  exists_universal.choose_spec O e x

/-- **Evaluation is recursive in a total oracle**, uniformly in the program: the function
`(c, x) ↦ eval O c x` is recursive in `O`. -/
theorem recursiveIn₂_eval (O : ℕ → ℕ) :
    RecursiveIn₂ {(O : ℕ →. ℕ)} (eval (O : ℕ →. ℕ)) := by
  unfold RecursiveIn₂ RecursiveIn
  refine (recursiveIn_eval _ universal).of_eq fun n => ?_
  conv_lhs => rw [← Nat.pair_unpair n, eval_universal]
  simp [Part.map_id']

end TauCeti.Oracle.Single.Code
