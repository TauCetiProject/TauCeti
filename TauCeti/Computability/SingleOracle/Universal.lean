/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Primrec
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
succeeds, and returns the output of that run. It gathers the string by querying the oracle, and
bounded evaluation against a finite string is primitive recursive. A successful run is correct by
the use principle, and every computation relative to `O` is found at some fuel
(`TauCeti.Oracle.Single.Code.mem_eval_iff_exists_evaln_range_map`).

The construction needs a total oracle: the universal program queries the oracle at every address
below the fuel before running anything, so relative to a partial oracle it would diverge at an
undefined address that the simulated program never queries.

## Main definitions

* `TauCeti.Oracle.Single.Code.universal`: a universal program.

## Main results

* `TauCeti.Oracle.Single.Code.mem_eval_iff_exists_evaln_range_map`: the values of a program
  relative to a total oracle are exactly the outputs of its successful runs against the finite
  initial segments of the oracle.
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

/-! ### Runs against finite initial segments of a total oracle -/

/-- **Evaluation through finite initial segments.** For a total oracle `O`, the values of a
program relative to `O` are exactly the outputs of its successful runs, at some fuel `k`, against
the finite oracle string `O 0, …, O (k - 1)`. -/
theorem mem_eval_iff_exists_evaln_range_map {O : ℕ → ℕ} {c : Code} {n y : ℕ} :
    y ∈ eval (O : ℕ →. ℕ) c n ↔
      ∃ k d, evaln (fun z => ((List.range k).map O)[z]?) k c n = some d ∧ d.output = y := by
  constructor
  · intro h
    obtain ⟨k, d, hd, rfl⟩ := exists_evaln_eq_some_of_mem_eval (σ := fun z => some (O z))
      (fun z y hy => by rw [PFun.coe_val, Part.mem_some_iff] at hy; rw [hy]) h
    -- the run at fuel `k` reads only addresses below `k`, where the string is correct
    refine ⟨k, d, evaln_eq_some_of_eqOn hd fun z hz => ?_, rfl⟩
    simp [(Set.mem_Iio.1 hz).trans_le (evaln_use_le hd)]
  · rintro ⟨k, d, hd, rfl⟩
    exact evaln_sound hd fun z _ y hy => by simp_all [List.getElem?_eq_some_iff]

/-! ### The universal program -/

/-- A primitive recursive function is computed by one program relative to every oracle. -/
private theorem exists_code_of_primrec {g : ℕ → ℕ} (hg : Primrec g) :
    ∃ c : Code, ∀ O n, eval O c n = Part.some (g n) :=
  (exists_forall_eval_eq_of_partrec (Nat.Partrec.of_primrec (Primrec.nat_iff.1 hg))).imp
    fun _ h O n => by simp [h O]

/-- A program sending `Nat.pair a k` to the code of the string `O 0, …, O (k - 1)`, relative to
every total oracle `O`. -/
private theorem exists_code_answers : ∃ c : Code, ∀ (O : ℕ → ℕ) a k,
    eval (O : ℕ →. ℕ) c (Nat.pair a k) =
      Part.some (encode ((List.range k).map O)) := by
  -- appending a number to a coded string is primitive recursive
  obtain ⟨cs, hcs⟩ := exists_code_of_primrec (g := fun m =>
      encode (ofNat (List ℕ) m.unpair.1 ++ [m.unpair.2])) <|
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
  obtain ⟨cg, hcg⟩ := exists_code_of_primrec (g := fun m =>
      g (m.unpair.1.unpair.1, m.unpair.1.unpair.2, ofNat (List ℕ) m.unpair.2)) <|
    hg.comp <| (fst.comp (Primrec.unpair.comp (fst.comp Primrec.unpair))).pair <|
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
  -- `t` tests whether the run at fuel `k` succeeds, and `r` returns its output
  obtain ⟨t, ht⟩ := exists_code_answers_apply (g := fun p => bif (run p).isSome then 0 else 1)
    (Primrec.cond (option_isSome.comp primrec_run) (const 0) (const 1))
  obtain ⟨r, hr⟩ := exists_code_answers_apply (g := fun p => ((run p).map Halt.output).getD 0)
    (option_getD.comp (option_map primrec_run (Halt.primrec_output.comp snd).to₂) (const 0))
  -- search for the least fuel at which the run succeeds, and return the output of that run
  refine ⟨comp r (pair (pair left right) (comp (rfind' t) (pair (pair left right) zero))),
    fun O e x => Part.ext fun y => ?_⟩
  set R : ℕ → Option Halt :=
    fun k => evaln (fun z => ((List.range k).map O)[z]?) k (ofNat Code e) x with hR
  have hrun (k : ℕ) : run (Nat.pair e x, k, (List.range k).map O) = R k := by
    simp only [run, Nat.unpair_pair, hR]
  have hid : eval (O : ℕ →. ℕ) (pair left right) (Nat.pair e x) = Part.some (Nat.pair e x) := by
    simp [Seq.seq]
  have hsearch :
      eval (O : ℕ →. ℕ) (comp (rfind' t) (pair (pair left right) zero)) (Nat.pair e x) =
        Nat.rfind fun k => Part.some (R k).isSome := by
    have hp : (fun k => Part.some !decide (R k = none) : ℕ →. Bool) =
        fun k => Part.some (R k).isSome :=
      funext fun k => by cases R k <;> rfl
    simp [hid, ht, hrun, hp, Seq.seq, Part.map_id', -List.getElem?_map]
  have hout (k : ℕ) : eval (O : ℕ →. ℕ) r (Nat.pair (Nat.pair e x) k) =
      Part.some (((R k).map Halt.output).getD 0) := by
    rw [hr, hrun]
  rw [eval_comp]
  constructor
  · intro h
    obtain ⟨m, hm, hy⟩ := Part.mem_bind_iff.1 h
    obtain ⟨n, hn, k, hk, rfl⟩ := mem_eval_pair.1 hm
    rw [hid, Part.mem_some_iff] at hn
    subst hn
    obtain ⟨hk, -⟩ := Nat.mem_rfind.1 (hsearch ▸ hk)
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 (Part.mem_some_iff.1 hk).symm
    rw [hout, Part.mem_some_iff, hd] at hy
    exact mem_eval_iff_exists_evaln_range_map.2 ⟨k, d, hd, hy.symm⟩
  · intro h
    obtain ⟨k, d, hd, rfl⟩ := mem_eval_iff_exists_evaln_range_map.1 h
    have hex : ∃ k, (R k).isSome := ⟨k, by simp only [hR, hd, Option.isSome_some]⟩
    obtain ⟨d₀, hd₀⟩ := Option.isSome_iff_exists.1 (Nat.find_spec hex)
    have h₀ : d₀.output = d.output := Part.mem_unique
      (mem_eval_iff_exists_evaln_range_map.2 ⟨_, d₀, hd₀, rfl⟩) h
    refine Part.mem_bind (mem_eval_pair.2 ⟨_, by rw [hid]; exact Part.mem_some _, _,
      hsearch ▸ Nat.mem_rfind.2 ⟨Part.mem_some_iff.2 (Nat.find_spec hex).symm, fun hj =>
        Part.mem_some_iff.2 (by simpa using Nat.find_min hex hj)⟩, rfl⟩) ?_
    · rw [hout, hd₀]
      simp [h₀]

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
