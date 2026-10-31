/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Primrec

/-!
# A universal oracle program

This file constructs a **universal program** `TauCeti.Oracle.Single.Code.universal`: one program,
independent of the oracle, which on input `Nat.pair e x` computes the value of the program numbered
`e` on `x`, relative to every total oracle `O : ℕ → ℕ`. In Soare's notation,
`Φ^O_u(⟨e, x⟩) ≃ Φ^O_e(x)` for all `O`, `e` and `x`.

The construction rests on the finite use of oracle computations. Relative to a total oracle `O`,
the values of a program are exactly the outputs of its successful bounded runs at some fuel `k`
against the oracle string `[O 0, …, O (k - 1)]` of the first `k` answers. That oracle string is
computed relative to `O` by primitive recursion, querying the oracle once per step, and bounded
evaluation against an oracle string is primitive recursive. The universal program searches for the
least fuel at which the run succeeds and returns its output.

The order of quantifiers matters: the same program works for every total oracle, unlike adequacy
(`TauCeti.Oracle.Single.Code.exists_code`), which provides a program for one fixed oracle. In
particular the universal function `n ↦ Φ^O_{n.unpair.1}(n.unpair.2)` is recursive in `O`, computed
by the same program for every total oracle `O`.

## Main definitions

* `TauCeti.Oracle.Single.Code.universal`: a universal program for total oracles.

## Main results

* `TauCeti.Oracle.Single.Code.mem_eval_iff_exists_evaln_range_map`: relative to a total oracle,
  the values of a program are the outputs of its successful runs against initial segments of the
  oracle.
* `TauCeti.Oracle.Single.Code.eval_universal`: the universal program on `Nat.pair e x` computes
  the program numbered `e` on `x`, relative to every total oracle.
* `TauCeti.Oracle.Single.Code.recursiveIn_eval_ofNat`: the universal function of programs relative
  to a total oracle is recursive in that oracle.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.1, in
  particular the use principle III.1.9.
* The search for a successful bounded run follows the proof of Mathlib's
  `Nat.Partrec.Code.eval_part`, which recovers evaluation of ordinary codes from
  `Nat.Partrec.Code.evaln`.
-/

public section

open Encodable Denumerable

namespace TauCeti.Oracle.Single.Code

/-! ### Runs against initial segments of a total oracle -/

/-- **Finite use, for a total oracle.** Relative to a total oracle `O`, the values of a program are
exactly the outputs of its successful runs at some fuel `k` against the oracle string
`[O 0, …, O (k - 1)]` of the first `k` answers of `O`. -/
theorem mem_eval_iff_exists_evaln_range_map {O : ℕ → ℕ} {c : Code} {n y : ℕ} :
    y ∈ eval (O : ℕ →. ℕ) c n ↔
      ∃ k d, evaln (fun z => ((List.range k).map O)[z]?) k c n = some d ∧ d.output = y := by
  constructor
  · intro h
    obtain ⟨k, d, hd, rfl⟩ := (mem_eval_iff_exists_evaln (σ := fun z => some (O z))
      (by simp [eq_comm])).1 h
    -- the run reads only addresses below its use, which is at most the fuel
    refine ⟨k, d, evaln_eq_some_of_eqOn hd fun z hz => ?_, rfl⟩
    have := evaln_use_le hd
    simp only [Set.mem_Iio] at hz
    simp [List.getElem?_range (show z < k by omega)]
  · rintro ⟨k, d, hd, rfl⟩
    refine evaln_sound hd fun z _ y hy => ?_
    by_cases hz : z < k <;> simp_all

/-! ### Building blocks of the universal program -/

/-- `Part.bind_some` for a continuation typed as a partial function `ℕ →. ℕ`, the form in which
`eval_comp` presents a composition; `simp` does not apply `Part.bind_some` there. -/
private theorem some_bind_eq (m : ℕ) (f : ℕ →. ℕ) : Part.some m >>= f = f m :=
  Part.bind_some _ _

/-- A primitive recursive function is computed by a query-free program, relative to every
oracle. -/
private theorem exists_eval_eq_some_of_primrec {g : ℕ → ℕ} (hg : Primrec g) :
    ∃ c : Code, ∀ (O : ℕ →. ℕ) n, eval O c n = Part.some (g n) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hg.to_comp)
  exact ⟨c.toSingleOracleCode, fun O n => by rw [eval_toSingleOracleCode, hc]; rfl⟩

/-- A program computing, from `k`, the number of the oracle string of the first `k` answers of a
total oracle, relative to every total oracle. -/
private theorem exists_eval_eq_encode_range_map :
    ∃ c : Code, ∀ (O : ℕ → ℕ) k,
      eval (O : ℕ →. ℕ) c k = Part.some (encode ((List.range k).map O)) := by
  -- the step appends the oracle answer `v` to the oracle string numbered `i`, given `⟨i, v⟩`
  obtain ⟨ca, hca⟩ := exists_eval_eq_some_of_primrec (g := fun p =>
    encode (ofNat (List ℕ) p.unpair.1 ++ [p.unpair.2])) <|
    Primrec.encode.comp <| Primrec.list_concat.comp
      ((Primrec.ofNat _).comp (Primrec.fst.comp Primrec.unpair)) (Primrec.snd.comp Primrec.unpair)
  -- primitive recursion on `⟨0, k⟩`, querying the oracle at `y` in the step from `y` to `y + 1`
  refine ⟨comp (prec zero (comp ca (pair (comp right right) (comp oracle (comp left right)))))
    (pair zero (pair left right)), fun O k => ?_⟩
  have hk : eval (O : ℕ →. ℕ) (pair zero (pair left right)) k =
      Part.some (Nat.pair 0 k) := by
    simp [Seq.seq]
  rw [eval_comp, hk, some_bind_eq]
  clear hk
  induction k with
  | zero => simp
  | succ k ih =>
    rw [eval_prec_succ, ih]
    simp [Seq.seq, hca, List.range_succ, some_bind_eq]

/-- A program computing `g a k [O 0, …, O (k - 1)]` from `Nat.pair a k`, relative to every total
oracle `O`, for every primitive recursive `g`. -/
private theorem exists_eval_pair_eq_some {g : ℕ → ℕ → List ℕ → ℕ}
    (hg : Primrec fun p : ℕ × ℕ × List ℕ => g p.1 p.2.1 p.2.2) :
    ∃ c : Code, ∀ (O : ℕ → ℕ) a k,
      eval (O : ℕ →. ℕ) c (Nat.pair a k) =
        Part.some (g a k ((List.range k).map O)) := by
  obtain ⟨cl, hcl⟩ := exists_eval_eq_encode_range_map
  obtain ⟨cg, hcg⟩ := exists_eval_eq_some_of_primrec (g := fun q =>
    g q.unpair.1.unpair.1 q.unpair.1.unpair.2 (ofNat (List ℕ) q.unpair.2)) <|
    hg.comp <| (Primrec.fst.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair).pair <|
      (Primrec.snd.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair).pair <|
        (Primrec.ofNat _).comp <| Primrec.snd.comp Primrec.unpair
  -- pair the input `⟨a, k⟩` with the number of the oracle string, then apply `g`
  refine ⟨comp cg (pair (pair left right) (comp cl right)), fun O a k => ?_⟩
  simp [Seq.seq, hcl, hcg, some_bind_eq]

/-- There is a program which on `Nat.pair e x` computes the program numbered `e` on `x`, relative
to every total oracle. -/
private theorem exists_universal :
    ∃ u : Code, ∀ (O : ℕ → ℕ) e x,
      eval (O : ℕ →. ℕ) u (Nat.pair e x) =
        eval (O : ℕ →. ℕ) (ofNat Code e) x := by
  -- the run of the program numbered `a.unpair.1` on `a.unpair.2` with fuel `k` against `l`
  have hrun : Primrec fun p : ℕ × ℕ × List ℕ =>
      evaln (fun z => p.2.2[z]?) p.2.1 (ofNat Code p.1.unpair.1) p.1.unpair.2 :=
    primrec_evaln_list.comp <| (Primrec.snd.comp Primrec.snd).pair <|
      (Primrec.fst.comp Primrec.snd).pair <|
        ((Primrec.ofNat _).comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))).pair
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
  -- a test with output `0` when the run succeeds and `1` when it fails
  obtain ⟨ct, hct⟩ := exists_eval_pair_eq_some (g := fun a k l =>
    if (evaln (fun z => l[z]?) k (ofNat Code a.unpair.1) a.unpair.2).isSome then 0 else 1) <|
    Primrec.ite (Primrec.eq.comp (Primrec.option_isSome.comp hrun) (Primrec.const true))
      (Primrec.const 0) (Primrec.const 1)
  -- the output of the run, or `0` when it fails
  obtain ⟨cv, hcv⟩ := exists_eval_pair_eq_some (g := fun a k l =>
    ((evaln (fun z => l[z]?) k (ofNat Code a.unpair.1) a.unpair.2).map Halt.output).getD 0) <|
    Primrec.option_getD.comp
      (Primrec.option_map hrun (Halt.primrec_output.comp Primrec.snd).to₂) (Primrec.const 0)
  -- search for the least fuel `k` at which the run succeeds, then return its output
  refine ⟨comp cv (pair (pair left right) (comp (rfind' ct) (pair (pair left right) zero))),
    fun O e x => Part.ext fun y => ?_⟩
  -- the search returns the least fuel `k` at which the run succeeds, paired with the input
  have hs : eval O (pair (pair left right) (comp (rfind' ct) (pair (pair left right) zero)))
      (Nat.pair e x) = (Nat.rfind fun k => Part.some
        (evaln (fun z => ((List.range k).map O)[z]?) k (ofNat Code e) x).isSome).map
        (Nat.pair (Nat.pair e x)) := by
    simp only [eval_pair, Seq.seq, eval_left, Nat.unpair_pair, Part.map_eq_map, Part.map_some,
      eval_right, Part.bind_some, eval_comp, eval_zero, some_bind_eq, eval_rfind', add_zero, hct,
      List.getElem?_map, ite_eq_left_iff, Bool.not_eq_true, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none, one_ne_zero, imp_false, decide_not, implies_true, Part.map_id']
    refine congrArg (Part.map _) (congrArg Nat.rfind (funext fun k => ?_))
    cases evaln (fun z => Option.map O (List.range k)[z]?) k (ofNat Code e) x <;> rfl
  rw [eval_comp, hs]
  refine Part.mem_bind_iff.trans ?_
  simp only [Part.mem_map_iff, exists_exists_and_eq_and, hcv, Nat.unpair_pair, Part.mem_some_iff]
  rw [mem_eval_iff_exists_evaln_range_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 (Part.mem_some_iff.1 (Nat.rfind_spec hk)).symm
    exact ⟨k, d, hd, by rw [hd]; rfl⟩
  · rintro ⟨k₀, d₀, hd₀, rfl⟩
    obtain ⟨k, hk, -⟩ := Nat.rfind_min' (p := fun k =>
      (evaln (fun z => ((List.range k).map O)[z]?) k (ofNat Code e) x).isSome) (m := k₀)
      (by rw [hd₀]; rfl)
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 (Part.mem_some_iff.1 (Nat.rfind_spec hk)).symm
    -- the run found by the search and the given run are both values of the program
    refine ⟨k, hk, ?_⟩
    rw [hd, Option.map_some, Option.getD_some]
    exact Part.mem_unique (mem_eval_iff_exists_evaln_range_map.2 ⟨k₀, d₀, hd₀, rfl⟩)
      (mem_eval_iff_exists_evaln_range_map.2 ⟨k, d, hd, rfl⟩)

/-! ### The universal program -/

/-- A **universal program** for total oracles: on input `Nat.pair e x` it computes the program
numbered `e` on `x`, relative to every total oracle (`eval_universal`). -/
noncomputable def universal : Code :=
  exists_universal.choose

/-- **The universal program.** Relative to every total oracle `O`, the universal program on
`Nat.pair e x` computes the program numbered `e` on `x`. -/
@[simp]
theorem eval_universal (O : ℕ → ℕ) (e x : ℕ) :
    eval (O : ℕ →. ℕ) universal (Nat.pair e x) =
      eval (O : ℕ →. ℕ) (ofNat Code e) x :=
  exists_universal.choose_spec O e x

/-- **The universal function is recursive in the oracle.** Relative to a total oracle `O`, the
function sending `n` to the value of the program numbered `n.unpair.1` on `n.unpair.2` is recursive
in `O`. -/
theorem recursiveIn_eval_ofNat (O : ℕ → ℕ) :
    Nat.RecursiveIn {(O : ℕ →. ℕ)}
      fun n => eval (O : ℕ →. ℕ) (ofNat Code n.unpair.1) n.unpair.2 :=
  (recursiveIn_eval _ universal).of_eq fun n => by
    rw [← eval_universal, Nat.pair_unpair]

end TauCeti.Oracle.Single.Code
