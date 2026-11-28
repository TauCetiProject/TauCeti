/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Code
import TauCeti.Data.PFun.Basic

/-!
# Boolean combinators and query-free helper programs for oracle programs

This file provides reusable, oracle-independent combinators and query-free helper programs on
`TauCeti.Oracle.Single.Code`:

* `TauCeti.Oracle.Single.Code.boolNot`, `TauCeti.Oracle.Single.Code.boolAnd`, and
  `TauCeti.Oracle.Single.Code.boolOr`: explicit primitive recursive Boolean combinators on
  `0`/`1`-valued programs (`encode false = 0`, `encode true = 1`). Their semantic equations hold
  relative to every partial oracle whenever the operand programs halt with Boolean outputs on the
  given input.
* `TauCeti.Oracle.Single.Code.exists_boolGuardCode` and
  `TauCeti.Oracle.Single.Code.exists_listHeadCode`: existence of query-free programs for
  checking whether an input is Boolean (`< 2`) and for extracting the head of an encoded list of
  naturals.
-/

public section

open Encodable Denumerable

namespace TauCeti.Oracle.Single.Code

/-! ### Boolean code combinators -/

private theorem eval_prec_one (O : ℕ →. ℕ) (cf cg : Code) (a : ℕ) :
    eval O (prec cf cg) (Nat.pair a 1) =
      eval O cf a >>= fun y => eval O cg (Nat.pair a (Nat.pair 0 y)) := by
  rw [← Nat.zero_add 1, eval_prec_succ]
  simp

/-- Explicit oracle-independent Boolean negation on `0`/`1`-valued programs (`encode false = 0`,
`encode true = 1`). -/
def boolNot (c : Code) : Code :=
  comp (prec (comp succ zero) zero) (pair zero c)

/-- Boolean negation of programs is primitive recursive. -/
theorem primrec_boolNot : Primrec boolNot :=
  primrec₂_comp.comp (Primrec.const _) (primrec₂_pair.comp (Primrec.const _) Primrec.id)

/-- Evaluating `boolNot c` when `c` outputs an encoded Boolean `b` returns `encode (!b)`, relative
to every partial oracle. -/
theorem eval_boolNot (O : ℕ →. ℕ) (c : Code) (n : ℕ) (b : Bool)
    (hc : encode b ∈ eval O c n) :
    eval O (boolNot c) n = Part.some (encode (!b)) := by
  have hce : eval O c n = Part.some (encode b) := Part.eq_some_iff.2 hc
  cases b <;> simp [boolNot, hce, Seq.seq, eval_prec_one]

/-- Explicit oracle-independent Boolean conjunction on `0`/`1`-valued programs. -/
def boolAnd (c₁ c₂ : Code) : Code :=
  comp (prec zero left) (pair c₂ c₁)

/-- Boolean conjunction of programs is primitive recursive in both operands. -/
theorem primrec₂_boolAnd : Primrec₂ boolAnd :=
  primrec₂_comp.comp (Primrec.const _) (primrec₂_pair.comp Primrec.snd Primrec.fst)

/-- Evaluating `boolAnd c₁ c₂` when `c₁` and `c₂` output encoded Booleans `b₁` and `b₂` returns
`encode (b₁ && b₂)`, relative to every partial oracle. -/
theorem eval_boolAnd (O : ℕ →. ℕ) (c₁ c₂ : Code) (n : ℕ) (b₁ b₂ : Bool)
    (h₁ : encode b₁ ∈ eval O c₁ n) (h₂ : encode b₂ ∈ eval O c₂ n) :
    eval O (boolAnd c₁ c₂) n = Part.some (encode (b₁ && b₂)) := by
  have he₁ : eval O c₁ n = Part.some (encode b₁) := Part.eq_some_iff.2 h₁
  have he₂ : eval O c₂ n = Part.some (encode b₂) := Part.eq_some_iff.2 h₂
  cases b₁ <;> cases b₂ <;> simp [boolAnd, he₁, he₂, Seq.seq, eval_prec_one]

/-- Explicit oracle-independent Boolean disjunction on `0`/`1`-valued programs. -/
def boolOr (c₁ c₂ : Code) : Code :=
  comp (prec (pair left right) (comp succ zero)) (pair c₂ c₁)

/-- Boolean disjunction of programs is primitive recursive in both operands. -/
theorem primrec₂_boolOr : Primrec₂ boolOr :=
  primrec₂_comp.comp (Primrec.const _) (primrec₂_pair.comp Primrec.snd Primrec.fst)

/-- Evaluating `boolOr c₁ c₂` when `c₁` and `c₂` output encoded Booleans `b₁` and `b₂` returns
`encode (b₁ || b₂)`, relative to every partial oracle. -/
theorem eval_boolOr (O : ℕ →. ℕ) (c₁ c₂ : Code) (n : ℕ) (b₁ b₂ : Bool)
    (h₁ : encode b₁ ∈ eval O c₁ n) (h₂ : encode b₂ ∈ eval O c₂ n) :
    eval O (boolOr c₁ c₂) n = Part.some (encode (b₁ || b₂)) := by
  have he₁ : eval O c₁ n = Part.some (encode b₁) := Part.eq_some_iff.2 h₁
  have he₂ : eval O c₂ n = Part.some (encode b₂) := Part.eq_some_iff.2 h₂
  cases b₁ <;> cases b₂ <;> simp [boolOr, he₁, he₂, Seq.seq, eval_prec_one]

/-! ### Auxiliary query-free programs -/

/-- There is an oracle-independent program that halts exactly on inputs `0` or `1`, returning
`0`. -/
theorem exists_boolGuardCode :
    ∃ c : Code, ∀ (O : ℕ →. ℕ) (n : ℕ),
      eval O c n = Part.assert (n < 2) fun _ => Part.some 0 := by
  have hopt : Computable fun n : ℕ => if n < 2 then some 0 else (none : Option ℕ) :=
    (Primrec.ite (Primrec.nat_lt.comp Primrec.id (Primrec.const 2))
      (Primrec.option_some.comp (Primrec.const 0)) (Primrec.const none)).to_comp
  have hpart : Nat.Partrec fun n : ℕ => Part.assert (n < 2) fun _ => Part.some 0 := by
    refine (Partrec.nat_iff.1 (Computable.ofOption hopt)).of_eq fun n => ?_
    ext y
    by_cases hn : n < 2 <;> simp [Part.assert, hn, eq_comm]
  obtain ⟨c, hc⟩ := exists_forall_eval_eq_of_partrec hpart
  exact ⟨c, fun O n => congrFun (hc O) n⟩

/-- There is an oracle-independent program extracting the head of an encoded list of naturals. -/
theorem exists_listHeadCode :
    ∃ c : Code, ∀ (O : ℕ →. ℕ) (n : ℕ), eval O c n = Part.some (ofNat (List ℕ) n).headI := by
  have hpart : Nat.Partrec fun n : ℕ => ((ofNat (List ℕ) n).headI : Part ℕ) :=
    Nat.Partrec.of_primrec (Primrec.nat_iff.1 (Primrec.list_headI.comp (Primrec.ofNat (List ℕ))))
  obtain ⟨c, hc⟩ := exists_forall_eval_eq_of_partrec hpart
  exact ⟨c, fun O n => by simpa using congrFun (hc O) n⟩

end TauCeti.Oracle.Single.Code
