/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Recursion
import TauCeti.Data.PFun.Basic

/-!
# Boolean combinators and parameterized compilation for oracle programs

This file provides reusable, oracle-independent combinators and compilation helpers on
`TauCeti.Oracle.Single.Code`:

* `TauCeti.Oracle.Single.Code.boolNot`, `TauCeti.Oracle.Single.Code.boolAnd`, and
  `TauCeti.Oracle.Single.Code.boolOr`: explicit primitive recursive Boolean combinators on
  `0`/`1`-valued programs (`encode false = 0`, `encode true = 1`). Their semantic equations hold
  relative to every partial oracle whenever the operand programs halt with Boolean outputs on the
  given input.
* `TauCeti.Oracle.Single.Code.paramCode`: specializes a base program `c` to an encodable
  parameter `a : α` via `Code.curry`, producing a primitive recursive family of programs.
* `TauCeti.Oracle.Single.Code.idCode`, `TauCeti.Oracle.Single.Code.iterCode`, and
  `TauCeti.Oracle.Single.Code.mapTakeCode`: identity, bounded state iteration, and applying a
  total program to a fixed-length prefix of an encoded list of naturals.
* `TauCeti.Oracle.Single.Code.exists_boolGuardCode` and
  `TauCeti.Oracle.Single.Code.exists_listHeadCode`: existence of query-free programs for
  checking whether an output is Boolean (`< 2`) and for extracting the head of an encoded list of
  naturals.
-/

public section

open Encodable Denumerable

namespace TauCeti.Oracle.Single.Code

/-! ### Boolean code combinators -/

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
  cases b <;> simp [boolNot, hce, Seq.seq]

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
  cases b₁ <;> cases b₂ <;> simp [boolAnd, he₁, he₂, Seq.seq]

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
  have hid (x : ℕ) : eval O (pair left right) x = Part.some x := by
    simp [Seq.seq]
  cases b₁ <;> cases b₂ <;> simp [boolOr, he₁, he₂, hid, Seq.seq]

/-! ### Parameterized program specialization -/

/-- Specialize a base program `c` to an encodable parameter `a : α` using `Code.curry`. -/
def paramCode {α : Type*} [Encodable α] (c : Code) (a : α) : Code :=
  curry c (encode a)

/-- Specializing `paramCode c a` is primitive recursive in the parameter `a`. -/
theorem primrec_paramCode {α : Type*} [Primcodable α] (c : Code) :
    Primrec (paramCode c : α → Code) :=
  primrec₂_curry.comp (Primrec.const c) Primrec.encode

/-- Specializing `paramCode c a` is primitive recursive in both the base program `c` and the
parameter `a`. -/
theorem primrec₂_paramCode {α : Type*} [Primcodable α] :
    Primrec₂ (paramCode (α := α)) :=
  primrec₂_curry.comp Primrec.fst (Primrec.encode.comp Primrec.snd)

/-- Evaluating `paramCode c a` on `x` evaluates `c` on `Nat.pair (encode a) x`, relative to
every partial oracle. -/
@[simp]
theorem eval_paramCode {α : Type*} [Encodable α] (O : ℕ →. ℕ) (c : Code) (a : α) (x : ℕ) :
    eval O (paramCode c a) x = eval O c (Nat.pair (encode a) x) :=
  eval_curry O c (encode a) x

/-- Composing a program `d` with `paramCode c a` evaluates `c` on `Nat.pair (encode a) x` and
passes the result to `d`, relative to every partial oracle. -/
theorem eval_comp_paramCode {α : Type*} [Encodable α] (O : ℕ →. ℕ) (d c : Code) (a : α)
    (x : ℕ) :
    eval O (comp d (paramCode c a)) x = eval O c (Nat.pair (encode a) x) >>= eval O d := by
  simp [eval_comp]

/-! ### Identity, iteration, and list-prefix mapping combinators -/

/-- The identity single-oracle program. -/
def idCode : Code :=
  pair left right

/-- Evaluating `idCode` returns the input unchanged, relative to every partial oracle. -/
@[simp]
theorem eval_idCode (O : ℕ →. ℕ) (n : ℕ) : eval O idCode n = Part.some n := by
  simp [idCode, Seq.seq]

private def ifZeroCode (c₀ c₁ : Code) : Code :=
  prec c₀ (comp c₁ (pair left (comp left right)))

private theorem primrec₂_ifZeroCode : Primrec₂ ifZeroCode :=
  (primrec₂_prec.comp Primrec.fst
    (primrec₂_comp.comp Primrec.snd (Primrec.const (pair left (comp left right))))).to₂

private theorem eval_ifZeroCode_dom {O : ℕ →. ℕ} {c₀ c₁ : Code}
    (hc₀ : ∀ a, ∃ y, eval O c₀ a = Part.some y)
    (hc₁ : ∀ a m, ∃ y, eval O c₁ (Nat.pair a m) = Part.some y) (a k : ℕ) :
    ∃ y, eval O (ifZeroCode c₀ c₁) (Nat.pair a k) = Part.some y := by
  induction k with
  | zero =>
    rw [ifZeroCode, eval_prec_zero]
    exact hc₀ a
  | succ k ih =>
    obtain ⟨i, hi⟩ := ih
    dsimp only [ifZeroCode] at hi
    rw [ifZeroCode, eval_prec_succ, hi]
    simp [Seq.seq, hc₁ a k]

private theorem eval_ifZeroCode_zero (O : ℕ →. ℕ) (c₀ c₁ : Code) (a : ℕ) :
    eval O (ifZeroCode c₀ c₁) (Nat.pair a 0) = eval O c₀ a := by
  rw [ifZeroCode, eval_prec_zero]

private theorem eval_ifZeroCode_succ {O : ℕ →. ℕ} {c₀ c₁ : Code}
    (hc₀ : ∀ a, ∃ y, eval O c₀ a = Part.some y)
    (hc₁ : ∀ a m, ∃ y, eval O c₁ (Nat.pair a m) = Part.some y) (a m : ℕ) :
    eval O (ifZeroCode c₀ c₁) (Nat.pair a (m + 1)) = eval O c₁ (Nat.pair a m) := by
  obtain ⟨i, hi⟩ := eval_ifZeroCode_dom hc₀ hc₁ a m
  dsimp only [ifZeroCode] at hi
  rw [ifZeroCode, eval_prec_succ, hi]
  simp [Seq.seq]

/-- Bounded state iteration: on `Nat.pair a d`, computes `init` on `a` and iterates `step` `d`
times on the resulting state. -/
def iterCode (init step : Code) : Code :=
  prec init (comp step (comp right right))

/-- Bounded state iteration is primitive recursive in both `init` and `step`. -/
theorem primrec₂_iterCode : Primrec₂ iterCode :=
  (primrec₂_prec.comp Primrec.fst
    (primrec₂_comp.comp Primrec.snd (Primrec.const (comp right right)))).to₂

/-- When `init` computes `g₀` and `step` computes `g` everywhere, `iterCode init step` on
`Nat.pair a d` computes `g^[d] (g₀ a)`, relative to every partial oracle. -/
theorem eval_iterCode {O : ℕ →. ℕ} {init step : Code} {g₀ g : ℕ → ℕ}
    (hinit : ∀ a, eval O init a = Part.some (g₀ a))
    (hstep : ∀ s, eval O step s = Part.some (g s)) (a d : ℕ) :
    eval O (iterCode init step) (Nat.pair a d) = Part.some (g^[d] (g₀ a)) := by
  induction d with
  | zero =>
    rw [iterCode, eval_prec_zero, hinit]
    rfl
  | succ d ih =>
    dsimp only [iterCode] at ih
    rw [iterCode, eval_prec_succ, ih]
    simpa [hstep] using
      (Function.iterate_succ_apply' g d (g₀ a)).symm.trans (Function.iterate_succ_apply g d (g₀ a))

private def stepSplit (proj : Code) : Code :=
  ifZeroCode (pair idCode zero)
    (pair
      (comp succ (pair (comp proj (comp left right)) left))
      (comp right right))

private theorem primrec_stepSplit : Primrec stepSplit :=
  primrec₂_ifZeroCode.comp (Primrec.const (pair idCode zero))
    (primrec₂_pair.comp
      (primrec₂_comp.comp (Primrec.const succ)
        (primrec₂_pair.comp
          (primrec₂_comp.comp Primrec.id (Primrec.const (comp left right)))
          (Primrec.const left)))
      (Primrec.const (comp right right)))

private def stepSplitFn (f : ℕ → ℕ) : List ℕ × List ℕ → List ℕ × List ℕ
  | (rl, []) => (rl, [])
  | (rl, a :: l) => (f a :: rl, l)

private theorem eval_stepSplit {O : ℕ →. ℕ} {proj : Code} {f : ℕ → ℕ}
    (hproj : ∀ y, eval O proj y = Part.some (f y)) (s : ℕ) :
    eval O (stepSplit proj) s =
      Part.some (Nat.pair
        (encode (stepSplitFn f (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).1)
        (encode (stepSplitFn f (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).2)) := by
  have hc₀ : ∀ a, ∃ y, eval O (pair idCode zero) a = Part.some y := fun a =>
    ⟨Nat.pair a 0, by simp [eval_idCode, Seq.seq]⟩
  have hc₁ : ∀ a m, ∃ y, eval O
      (pair
        (comp succ
          (pair (comp proj (comp left right)) left))
        (comp right right))
      (Nat.pair a m) = Part.some y := fun a m => by
    simp [hproj, Seq.seq]
  conv_lhs => rw [← Nat.pair_unpair s]
  set rl := ofNat (List ℕ) s.unpair.1
  set l := ofNat (List ℕ) s.unpair.2
  have hs1 : s.unpair.1 = encode rl := (encode_ofNat s.unpair.1).symm
  have hs2 : s.unpair.2 = encode l := (encode_ofNat s.unpair.2).symm
  rw [hs1, hs2]
  cases l with
  | nil =>
    rw [stepSplit, encode_list_nil, eval_ifZeroCode_zero]
    simp [stepSplitFn, eval_idCode, Seq.seq]
  | cons a l' =>
    rw [stepSplit, encode_list_cons, eval_ifZeroCode_succ hc₀ hc₁]
    simp [stepSplitFn, hproj, Seq.seq]

private theorem stepSplitFn_iterate (f : ℕ → ℕ) (d : ℕ) (rl l : List ℕ) :
    (stepSplitFn f)^[d] (rl, l) = (((l.take d).map f).reverseAux rl, l.drop d) := by
  induction d generalizing rl l with
  | zero => simp
  | succ d ih =>
    cases l with
    | nil =>
      rw [Function.iterate_succ_apply, stepSplitFn]
      simpa using ih rl []
    | cons a l' =>
      rw [Function.iterate_succ_apply, stepSplitFn, ih]
      simp [List.take_succ_cons]

private def stepRev : Code :=
  comp
    (ifZeroCode (pair zero idCode)
      (pair (comp right right)
        (comp succ (pair (comp left right) left))))
    (pair right left)

private def stepRevFn : List ℕ × List ℕ → List ℕ × List ℕ
  | ([], l) => ([], l)
  | (b :: rl, l) => (rl, b :: l)

private theorem eval_stepRev (O : ℕ →. ℕ) (s : ℕ) :
    eval O stepRev s =
      Part.some (Nat.pair
        (encode (stepRevFn (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).1)
        (encode (stepRevFn (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).2)) := by
  have hc₀ : ∀ a, ∃ y, eval O (pair zero idCode) a = Part.some y := fun a =>
    ⟨Nat.pair 0 a, by simp [eval_idCode, Seq.seq]⟩
  have hc₁ : ∀ a m, ∃ y, eval O
      (pair (comp right right)
        (comp succ (pair (comp left right) left)))
      (Nat.pair a m) = Part.some y := fun a m => by
    simp [Seq.seq]
  set rl := ofNat (List ℕ) s.unpair.1
  set l := ofNat (List ℕ) s.unpair.2
  have hs1 : s.unpair.1 = encode rl := (encode_ofNat s.unpair.1).symm
  have hs2 : s.unpair.2 = encode l := (encode_ofNat s.unpair.2).symm
  rw [stepRev, eval_comp]
  have hswap : eval O (pair right left) s =
      Part.some (Nat.pair (encode l) (encode rl)) := by
    simp [hs1, hs2, Seq.seq]
  rw [hswap, PFun.some_bind]
  cases rl with
  | nil =>
    rw [encode_list_nil, eval_ifZeroCode_zero]
    simp [stepRevFn, eval_idCode, Seq.seq]
  | cons b rl' =>
    rw [encode_list_cons, eval_ifZeroCode_succ hc₀ hc₁]
    simp [stepRevFn, Seq.seq]

private theorem stepRevFn_iterate (d : ℕ) (rl l : List ℕ) (hd : rl.length ≤ d) :
    stepRevFn^[d] (rl, l) = ([], rl.reverseAux l) := by
  induction d generalizing rl l with
  | zero =>
    obtain rfl : rl = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hd)
    rfl
  | succ d ih =>
    cases rl with
    | nil =>
      rw [Function.iterate_succ_apply, stepRevFn]
      exact ih [] l (Nat.zero_le d)
    | cons b rl' =>
      rw [Function.iterate_succ_apply, stepRevFn]
      exact ih rl' (b :: l) (Nat.succ_le_succ_iff.1 hd)

/-- Program combinator that, given `Nat.pair d (encode l)`, maps `proj` over the first `d`
entries of `l : List ℕ` while leaving `l.drop d` unchanged. -/
def mapTakeCode (proj : Code) : Code :=
  let phase1 := comp (iterCode (pair zero idCode) (stepSplit proj)) (pair right left)
  let phase2 := comp (iterCode idCode stepRev) (pair phase1 left)
  comp right phase2

/-- Constructing `mapTakeCode proj` is primitive recursive in `proj`. -/
theorem primrec_mapTakeCode : Primrec mapTakeCode :=
  let hphase1 : Primrec fun proj : Code =>
      comp (iterCode (pair zero idCode) (stepSplit proj)) (pair right left) :=
    primrec₂_comp.comp
      (primrec₂_iterCode.comp (Primrec.const (pair zero idCode)) primrec_stepSplit)
      (Primrec.const (pair right left))
  let hphase2 : Primrec fun proj : Code =>
      comp (iterCode idCode stepRev)
        (pair (comp (iterCode (pair zero idCode) (stepSplit proj)) (pair right left)) left) :=
    primrec₂_comp.comp (Primrec.const (iterCode idCode stepRev))
      (primrec₂_pair.comp hphase1 (Primrec.const left))
  primrec₂_comp.comp (Primrec.const right) hphase2

/-- Evaluating `mapTakeCode proj` on `Nat.pair d (encode l)` applies `f` (the total function
computed by `proj` relative to `O`) to the first `d` entries of `l` and leaves the remaining
entries unchanged. -/
theorem eval_mapTakeCode {O : ℕ →. ℕ} {proj : Code} {f : ℕ → ℕ}
    (hproj : ∀ y, eval O proj y = Part.some (f y)) (d : ℕ) (l : List ℕ) :
    eval O (mapTakeCode proj) (Nat.pair d (encode l)) =
      Part.some (encode ((l.take d).map f ++ l.drop d)) := by
  have hinit1 : ∀ a, eval O (pair zero idCode) a =
      Part.some (Nat.pair (encode ([] : List ℕ)) (encode (ofNat (List ℕ) a))) := fun a => by
    simp [eval_idCode, Seq.seq]
  have hiter1 := eval_iterCode hinit1 (eval_stepSplit hproj)
    (g₀ := fun a => Nat.pair (encode ([] : List ℕ)) (encode (ofNat (List ℕ) a)))
    (g := fun s => Nat.pair
      (encode (stepSplitFn f (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).1)
      (encode (stepSplitFn f (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).2))
  have hstep1 (k : ℕ) (p₁ p₂ : List ℕ) :
      (fun s => Nat.pair
        (encode (stepSplitFn f (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).1)
        (encode (stepSplitFn f (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).2))^[k]
          (Nat.pair (encode p₁) (encode p₂)) =
      Nat.pair (encode ((stepSplitFn f)^[k] (p₁, p₂)).1)
        (encode ((stepSplitFn f)^[k] (p₁, p₂)).2) := by
    induction k generalizing p₁ p₂ with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simpa [Nat.unpair_pair, ofNat_encode] using
        ih (stepSplitFn f (p₁, p₂)).1 (stepSplitFn f (p₁, p₂)).2
  have hinit2 : ∀ a, eval O idCode a = Part.some a := eval_idCode O
  have hiter2 := eval_iterCode hinit2 (eval_stepRev O)
    (g₀ := id)
    (g := fun s => Nat.pair
      (encode (stepRevFn (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).1)
      (encode (stepRevFn (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).2))
  have hstep2 (k : ℕ) (p₁ p₂ : List ℕ) :
      (fun s => Nat.pair
        (encode (stepRevFn (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).1)
        (encode (stepRevFn (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).2))^[k]
          (Nat.pair (encode p₁) (encode p₂)) =
      Nat.pair (encode (stepRevFn^[k] (p₁, p₂)).1) (encode (stepRevFn^[k] (p₁, p₂)).2) := by
    induction k generalizing p₁ p₂ with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simpa [Nat.unpair_pair, ofNat_encode] using
        ih (stepRevFn (p₁, p₂)).1 (stepRevFn (p₁, p₂)).2
  have hphase1 :
      eval O (comp (iterCode (pair zero idCode) (stepSplit proj))
          (pair right left)) (Nat.pair d (encode l)) =
        Part.some (Nat.pair
          (encode (((l.take d).map f).reverseAux [])) (encode (l.drop d))) := by
    rw [eval_comp]
    have hswap : eval O (pair right left) (Nat.pair d (encode l)) =
        Part.some (Nat.pair (encode l) d) := by
      simp [Seq.seq]
    rw [hswap, PFun.some_bind, hiter1, ofNat_encode, hstep1, stepSplitFn_iterate]
  have hlen : (((l.take d).map f).reverseAux []).length ≤ d := by
    simp
  rw [mapTakeCode, eval_comp, eval_comp]
  have hpair2 :
      eval O (pair
          (comp (iterCode (pair zero idCode) (stepSplit proj))
            (pair right left))
          left) (Nat.pair d (encode l)) =
        Part.some (Nat.pair
          (Nat.pair (encode (((l.take d).map f).reverseAux [])) (encode (l.drop d))) d) := by
    simp [eval_pair, hphase1, Seq.seq]
  rw [hpair2, PFun.some_bind, hiter2, PFun.some_bind, id_eq, hstep2, stepRevFn_iterate _ _ _ hlen]
  simp

/-! ### Auxiliary query-free programs -/

/-- An ordinary oracle-independent program that halts precisely on Boolean outputs (`0` or `1`),
returning `0`. -/
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

/-- An ordinary oracle-independent program extracting the head of an encoded list of naturals. -/
theorem exists_listHeadCode :
    ∃ c : Code, ∀ (O : ℕ →. ℕ) (n : ℕ), eval O c n = Part.some (ofNat (List ℕ) n).headI := by
  have hpart : Nat.Partrec fun n : ℕ => ((ofNat (List ℕ) n).headI : Part ℕ) :=
    Nat.Partrec.of_primrec (Primrec.nat_iff.1 (Primrec.list_headI.comp (Primrec.ofNat (List ℕ))))
  obtain ⟨c, hc⟩ := exists_forall_eval_eq_of_partrec hpart
  exact ⟨c, fun O n => by simpa using congrFun (hc O) n⟩

end TauCeti.Oracle.Single.Code
