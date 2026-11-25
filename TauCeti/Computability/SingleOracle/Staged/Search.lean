/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Code
import TauCeti.Computability.Partrec.Search
import TauCeti.Data.PFun.Basic

/-!
# Compiling the search of a stage table

A program that computes finite observations on paired inputs can be compiled into a program
that searches those observations in order. The transformation is primitive recursive on code
syntax and is independent of the oracle. The compiler uses Mathlib's encoding of optional
natural numbers, with zero for an absent observation and `y + 1` for an observation of `y`.

The exact semantics also cover a program that fails to return an observation: if it diverges
before the first success, the search cannot reach that success. For a total stage program this
specializes to Mathlib's `Nat.rfindOpt`, and for a persistent stage table it computes the
presented partial function.

## Main results

* `TauCeti.Oracle.Single.Code.exists_code_answers_apply`: a single oracle program applies any
  primitive recursive function to `(n, k)` and the finite oracle prefix `O 0, …, O (k - 1)`,
  uniformly for every total oracle `O`.
* `TauCeti.Oracle.Single.Code.exists_code_rfindOpt_answers`: a single oracle program evaluates to
  the option-valued least search `Nat.rfindOpt` of a primitive recursive function on `(n, k)` and
  `O 0, …, O (k - 1)`, uniformly for every total oracle `O`.
* `TauCeti.Oracle.Single.Code.exists_code_rfind_answers`: a single oracle program evaluates to the
  least witness `k` satisfying a primitive recursive predicate on `(n, k)` and
  `O 0, …, O (k - 1)`, uniformly for every total oracle `O`.
* `TauCeti.Oracle.Single.Code.exists_code_dom_iff_exists_answers`: domain characterization of
  `exists_code_rfind_answers`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter I.3
  (least-number search) and Chapter III.1 (relativization).
-/

public section

open Encodable

namespace TauCeti.Oracle.Single.Code

variable {O : ℕ →. ℕ}

/-- Turn the encoded observation into a test for minimization. An absent observation returns
one, so the search continues, and every present observation returns zero. -/
private def stageSearchTest : Code :=
  comp (prec succ zero) (pair zero (pair left right))

private theorem eval_stageSearchTest (n : ℕ) :
    eval O stageSearchTest n = Part.some (if n = 0 then 1 else 0) := by
  rw [stageSearchTest, eval_comp, eval_pair_zero_left_right, PFun.some_bind]
  induction n with
  | zero => simp
  | succ n ih => simp [eval_prec_succ, ih]

/-- Remove the successor tag used to encode a successful observation. -/
private def stageSearchOutput : Code :=
  comp (prec zero (comp left right)) (pair zero (pair left right))

private theorem eval_stageSearchOutput (n : ℕ) :
    eval O stageSearchOutput n = Part.some n.pred := by
  rw [stageSearchOutput, eval_comp, eval_pair_zero_left_right, PFun.some_bind]
  induction n with
  | zero => simp
  | succ n ih => simp [eval_prec_succ, ih]

/-- Compile a program on paired inputs `Nat.pair x s` returning encoded optional observations.
The compiled program on `x` returns the first present value when every earlier stage explicitly
returns encoded `none`. -/
def searchStages (c : Code) : Code :=
  comp (comp stageSearchOutput c)
    (pair (pair left right) (comp (rfind' (comp stageSearchTest c)) (pair (pair left right) zero)))

/-- Compiling the search of a stage table is primitive recursive on codes. -/
theorem primrec_searchStages : Primrec searchStages :=
  primrec₂_comp.comp (primrec₂_comp.comp (Primrec.const stageSearchOutput) Primrec.id)
    (primrec₂_pair.comp (Primrec.const _) <|
      primrec₂_comp.comp (primrec_rfind'.comp <|
        primrec₂_comp.comp (Primrec.const stageSearchTest) Primrec.id) (Primrec.const _))

private theorem eval_searchStages_index (c : Code) (x : ℕ) :
    eval O (comp (rfind' (comp stageSearchTest c)) (pair (pair left right) zero)) x =
      Nat.rfind fun s => (eval O c (Nat.pair x s)).map (fun n => decide (n ≠ 0)) := by
  rw [eval_comp, eval_pair_left_right_zero, PFun.some_bind, eval_rfind']
  simp only [Nat.add_zero, Part.map_eq_map, Part.map_id' (fun _ => rfl)]
  congr 1
  funext s
  have htest : eval O stageSearchTest = fun n => Part.some (if n = 0 then 1 else 0) :=
    funext eval_stageSearchTest
  rw [eval_comp, htest, Part.bind_eq_bind, Part.bind_some_eq_map, Part.map_map]
  congr 1
  funext n
  by_cases h : n = 0 <;> simp [Function.comp_apply, h]

private theorem eval_searchStages_bind (c : Code) (x : ℕ) :
    eval O c.searchStages x =
      (Nat.rfind fun s => (eval O c (Nat.pair x s)).map (fun n => decide (n ≠ 0))).bind
        fun s => (eval O c (Nat.pair x s)).map Nat.pred := by
  have hout : eval O stageSearchOutput = fun n => Part.some n.pred := funext eval_stageSearchOutput
  rw [searchStages, eval_comp, eval_pair_of_left_eq_some (eval_pair_left_right x),
    eval_searchStages_index]
  refine (Part.bind_map _ _ _).trans ?_
  congr 1
  funext s
  rw [eval_comp, hout, Part.bind_eq_bind, Part.bind_some_eq_map]

/-- The compiled search returns `y` precisely when the source program reports `y` at some
stage and explicitly reports an absent observation at every earlier stage. This holds for
partial oracles and for source programs that themselves may diverge. -/
theorem mem_eval_searchStages {c : Code} {x y : ℕ} :
    y ∈ eval O (c.searchStages) x ↔
      ∃ s, encode (some y) ∈ eval O c (Nat.pair x s) ∧
        ∀ t < s, encode (none : Option ℕ) ∈ eval O c (Nat.pair x t) := by
  rw [eval_searchStages_bind, Part.mem_bind_iff]
  simp only [encode_none, encode_some, encode_nat]
  constructor
  · rintro ⟨s, hfind, hout⟩
    obtain ⟨n, hn, hne⟩ := (Part.mem_map_iff _).1 (Nat.rfind_spec hfind)
    obtain ⟨v, hv, hy⟩ := (Part.mem_map_iff _).1 hout
    have hvn : v = n := Part.mem_unique hv hn
    subst v
    refine ⟨s, ?_, fun t ht => ?_⟩
    · have hz : n ≠ 0 := fun h => by simp [h] at hne
      have he : n = y + 1 :=
        (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hz)).symm.trans (congrArg Nat.succ hy)
      simpa only [he, Nat.succ_eq_add_one] using hn
    · obtain ⟨m, hm, hzero⟩ := (Part.mem_map_iff _).1 (Nat.rfind_min hfind ht)
      by_cases h : m = 0
      · simpa only [h] using hm
      · simp [h] at hzero
  · rintro ⟨s, hs, hbefore⟩
    refine ⟨s, Nat.mem_rfind.2 ⟨?_, fun ht => ?_⟩, (Part.mem_map_iff _).2 ⟨_, hs, rfl⟩⟩
    · exact (Part.mem_map_iff _).2 ⟨_, hs, by simp⟩
    · exact (Part.mem_map_iff _).2 ⟨0, hbefore _ ht, by simp⟩

/-- The compiler realizes least-stage search for any source program that computes a total
table of optional observations relative to the given oracle. -/
theorem eval_searchStages {c : Code} {A : ℕ → Option ℕ} {x : ℕ}
    (hA : ∀ s, eval O c (Nat.pair x s) = Part.some (encode (A s))) :
    eval O c.searchStages x = Nat.rfindOpt A := by
  ext y
  simp only [mem_eval_searchStages, Nat.mem_rfindOpt_iff, hA, Part.mem_some_iff, encode_inj,
    eq_comm]

/-! ### Uniform prefix search over total oracles -/

/-- A program sending `Nat.pair a k` to the code of the string `O 0, …, O (k - 1)`, relative to
every total oracle `O`. -/
private theorem exists_code_answers : ∃ c : Code, ∀ (O : ℕ → ℕ) a k,
    eval (O : ℕ →. ℕ) c (Nat.pair a k) =
      Part.some (encode ((List.range k).map O)) := by
  open Primrec in
  obtain ⟨cs, hcs⟩ := exists_code_of_computable (g := fun m =>
      encode (Denumerable.ofNat (List ℕ) m.unpair.1 ++ [m.unpair.2])) <| Primrec.to_comp <|
    Primrec.encode.comp <| list_append.comp ((Primrec.ofNat _).comp (fst.comp Primrec.unpair))
      (list_cons.comp (snd.comp Primrec.unpair) (const []))
  refine ⟨prec zero (comp cs (pair (comp right right) (comp oracle (comp left right)))),
    fun O a k => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [eval_prec_succ, ih]
    simp [hcs, Seq.seq, List.range_succ]

/-- A program applying a primitive recursive function `g` to `(n, k, [O 0, …, O (k - 1)])` on the
input `Nat.pair n k`, relative to every total oracle `O`. -/
theorem exists_code_answers_apply {g : ℕ × ℕ × List ℕ → ℕ} (hg : Primrec g) :
    ∃ c : Code, ∀ (O : ℕ → ℕ) n k, eval (O : ℕ →. ℕ) c (Nat.pair n k) =
      Part.some (g (n, k, (List.range k).map O)) := by
  open Primrec in
  obtain ⟨ca, hca⟩ := exists_code_answers
  obtain ⟨cg, hcg⟩ := exists_code_of_computable (g := fun m =>
      g (m.unpair.1.unpair.1, m.unpair.1.unpair.2, Denumerable.ofNat (List ℕ) m.unpair.2)) <|
    Primrec.to_comp <| hg.comp <| (fst.comp (Primrec.unpair.comp (fst.comp Primrec.unpair))).pair <|
      (snd.comp (Primrec.unpair.comp (fst.comp Primrec.unpair))).pair <|
        (Primrec.ofNat _).comp (snd.comp Primrec.unpair)
  refine ⟨comp cg (pair (pair left right) ca), fun O n k => ?_⟩
  rw [eval_comp, eval_pair, eval_pair_left_right, hca]
  simp [hcg, Seq.seq]

/-- A single program whose evaluation on `n`, relative to every total oracle `O`, is the
option-valued least search `Nat.rfindOpt` of a primitive recursive function `g` on `(n, k)` and
the finite oracle string `O 0, …, O (k - 1)`. -/
theorem exists_code_rfindOpt_answers {g : ℕ × ℕ × List ℕ → Option ℕ} (hg : Primrec g) :
    ∃ c : Code, ∀ (O : ℕ → ℕ) n,
      eval (O : ℕ →. ℕ) c n =
        Nat.rfindOpt fun k => g (n, k, (List.range k).map O) := by
  obtain ⟨t, ht⟩ := exists_code_answers_apply (g := fun q => encode (g q))
    (Primrec.encode.comp hg)
  exact ⟨t.searchStages, fun O n => eval_searchStages (ht O n)⟩

/-- A single program whose evaluation on `n`, relative to every total oracle `O`, is the least
witness `k` at which a primitive recursive predicate holds of `(n, k)` and the finite oracle string
`O 0, …, O (k - 1)`. -/
theorem exists_code_rfind_answers {p : ℕ × ℕ × List ℕ → Bool} (hp : Primrec p) :
    ∃ c : Code, ∀ (O : ℕ → ℕ) n,
      eval (O : ℕ →. ℕ) c n =
        Nat.rfind fun k => Part.some (p (n, k, (List.range k).map O)) := by
  open Primrec in
  obtain ⟨c, hc⟩ := exists_code_rfindOpt_answers
    (g := fun q => bif p q then some q.2.1 else (none : Option ℕ))
    (Primrec.cond hp (option_some.comp (fst.comp snd)) (const none))
  refine ⟨c, fun O n => ?_⟩
  rw [hc]
  ext k
  rw [Nat.mem_rfindOpt_iff,
    Nat.mem_rfind (p := fun k => (Part.some (p (n, k, (List.range k).map O)) : Part Bool))]
  simp

/-- A single program whose domain on `n`, relative to every total oracle `O`, is the set of inputs
admitting a witness `k` at which a primitive recursive predicate holds of `(n, k)` and the finite
oracle string `O 0, …, O (k - 1)`. -/
theorem exists_code_dom_iff_exists_answers {p : ℕ × ℕ × List ℕ → Bool} (hp : Primrec p) :
    ∃ c : Code, ∀ (O : ℕ → ℕ) n,
      (eval (O : ℕ →. ℕ) c n).Dom ↔ ∃ k, p (n, k, (List.range k).map O) = true := by
  obtain ⟨c, hc⟩ := exists_code_rfind_answers hp
  refine ⟨c, fun O n => ?_⟩
  rw [hc]
  exact (Nat.rfind_dom (p := fun k =>
    (Part.some (p (n, k, (List.range k).map O)) : Part Bool))).trans (by simp)

end TauCeti.Oracle.Single.Code
