/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Primrec
import TauCeti.Computability.SingleOracle.Staged.Search
import TauCeti.Data.PFun.Basic

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
succeeds, and returns the output of that run. The stage program gathers the string by querying
the oracle and runs the primitive-recursive finite-string evaluator. The search is compiled by
`TauCeti.Oracle.Single.Code.searchStages`. A successful run is correct by
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

/-- A program sending `Nat.pair a k` to the code of the string `O 0, …, O (k - 1)`, relative to
every total oracle `O`. -/
private theorem exists_code_answers : ∃ c : Code, ∀ (O : ℕ → ℕ) a k,
    eval (O : ℕ →. ℕ) c (Nat.pair a k) =
      Part.some (encode ((List.range k).map O)) := by
  -- appending a number to a coded string is primitive recursive
  obtain ⟨cs, hcs⟩ := exists_code_of_computable (g := fun m =>
      encode (ofNat (List ℕ) m.unpair.1 ++ [m.unpair.2])) <| Primrec.to_comp <|
    Primrec.encode.comp <| list_append.comp ((Primrec.ofNat _).comp (fst.comp Primrec.unpair))
      (list_cons.comp (snd.comp Primrec.unpair) (const []))
  -- by recursion on `k`, append the answer of the oracle at `k`
  refine ⟨prec zero (comp cs (pair (comp right right) (comp oracle (comp left right)))),
    fun O a k => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [eval_prec_succ, ih]
    simp [hcs, Seq.seq, List.range_succ]

/-- A program applying a primitive recursive function `g` to `(n, k, [O 0, …, O (k - 1)])` on the
input `Nat.pair n k`, relative to every total oracle `O`. -/
private theorem exists_code_answers_apply {g : ℕ × ℕ × List ℕ → ℕ} (hg : Primrec g) :
    ∃ c : Code, ∀ (O : ℕ → ℕ) n k, eval (O : ℕ →. ℕ) c (Nat.pair n k) =
      Part.some (g (n, k, (List.range k).map O)) := by
  obtain ⟨ca, hca⟩ := exists_code_answers
  obtain ⟨cg, hcg⟩ := exists_code_of_computable (g := fun m =>
      g (m.unpair.1.unpair.1, m.unpair.1.unpair.2, ofNat (List ℕ) m.unpair.2)) <|
    Primrec.to_comp <| hg.comp <| (fst.comp (Primrec.unpair.comp (fst.comp Primrec.unpair))).pair <|
      (snd.comp (Primrec.unpair.comp (fst.comp Primrec.unpair))).pair <|
        (Primrec.ofNat _).comp (snd.comp Primrec.unpair)
  refine ⟨comp cg (pair (pair left right) ca), fun O n k => ?_⟩
  simp [hca, hcg, Seq.seq]

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
  obtain ⟨c, hc⟩ := exists_code_answers_apply
    (g := fun p => encode ((run p).map Halt.output)) <|
    Primrec.encode.comp (option_map₁ Halt.primrec_output |>.comp primrec_run)
  refine ⟨c.searchStages, fun O e x => ?_⟩
  let A (s : ℕ) := (run (Nat.pair e x, s, (List.range s).map O)).map Halt.output
  rw [eval_searchStages (A := A) (hc O (Nat.pair e x))]
  ext y
  rw [Nat.rfindOpt_mono, mem_eval_iff_exists_evaln_range_map]
  · simp only [A, run, Nat.unpair_pair, Option.mem_def, Option.map_eq_some_iff]
  · intro z s t hst hs
    simp only [A, run, Nat.unpair_pair, Option.mem_def, Option.map_eq_some_iff,
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
