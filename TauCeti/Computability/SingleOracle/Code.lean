/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.TuringDegree
import TauCeti.Computability.RecursiveIn

/-!
# Programs with one oracle

This file defines `TauCeti.Oracle.Single.Code`, the programs of partial recursive functions with
access to a single oracle. They are Mathlib's codes `Nat.Partrec.Code` with one more basic
instruction, `oracle`, which queries the oracle at its input. Programs are numbered by an explicit
bijection with `ℕ`, and `TauCeti.Oracle.Single.Code.eval O c` interprets the program `c` as a
partial function relative to an oracle `O : ℕ →. ℕ`. A total oracle `O : ℕ → ℕ` is the case
`fun n => Part.some (O n)`, and a set oracle is the case of its characteristic function.

The main result is **adequacy**: for every oracle `O`, the partial functions computed by programs
relative to `O` are exactly Mathlib's `Nat.RecursiveIn {O}` functions. The direction from
programs to `Nat.RecursiveIn` transfers algorithms written as programs to Mathlib's notion; the
direction from `Nat.RecursiveIn` to programs transfers statements quantifying over all programs,
such as non-reducibility, back to Mathlib's notion. In particular `f` is Turing reducible to `g`
exactly when some program computes `f` relative to `g`.

This adequacy is extensional: it is a statement about one fixed oracle, and does not choose a
program uniformly in the oracle.

## Main definitions

* `TauCeti.Oracle.Single.Code`: programs with one oracle.
* `TauCeti.Oracle.Single.Code.encodeCode`, `TauCeti.Oracle.Single.Code.ofNatCode`: the numbering
  of programs and its inverse, packaged as a `Denumerable` instance.
* `TauCeti.Oracle.Single.Code.eval`: the partial function computed by a program relative to an
  oracle.
* `Nat.Partrec.Code.toSingleOracleCode`: the query-free program of an ordinary Mathlib code.

## Main results

* `TauCeti.Oracle.Single.Code.primrec₂_pair` and its neighbours: the program constructors are
  primitive recursive on numbers of programs.
* `TauCeti.Oracle.Single.Code.encode_lt_pair` and its neighbours: the components of a compound
  program have smaller numbers.
* `TauCeti.Oracle.Single.Code.primrec_casesOn`: case analysis on programs is primitive recursive.
* `TauCeti.Oracle.Single.Code.mem_eval_pair`, `TauCeti.Oracle.Single.Code.mem_eval_rfind'`: the
  values of a pairing, and one step of a search.
* `TauCeti.Oracle.Single.Code.eval_toSingleOracleCode`: a query-free program computes the same
  function as the ordinary code it comes from, relative to every oracle.
* `TauCeti.Oracle.Single.Code.exists_code`: adequacy, `Nat.RecursiveIn {O} f ↔ ∃ c, eval O c = f`.
* `TauCeti.Oracle.Single.Code.turingReducible_iff_exists_code`: the same for Turing
  reducibility.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.1.
* M. Carneiro, *Formalizing computability theory via partial recursive functions*, ITP 2019. The
  numbering, the evaluation and the adequacy proof follow Mathlib's `Nat.Partrec.Code`,
  `Nat.Partrec.Code.eval` and `Nat.Partrec.Code.exists_code`, extended by the oracle instruction.
* The namespace and constructors follow the shape of the single-oracle code proposed by Edwin Park
  in Mathlib pull request 38973.
-/

public section

open Encodable Denumerable

namespace TauCeti

namespace Oracle.Single

/-- Programs of partial recursive functions with access to one oracle. They are Mathlib's codes
`Nat.Partrec.Code` together with the instruction `oracle`, which queries the oracle at its input.
See `TauCeti.Oracle.Single.Code.eval` for the interpretation of the constructors. -/
inductive Code : Type
  | zero : Code
  | succ : Code
  | left : Code
  | right : Code
  | oracle : Code
  | pair : Code → Code → Code
  | comp : Code → Code → Code
  | prec : Code → Code → Code
  | rfind' : Code → Code
  deriving DecidableEq

namespace Code

instance : Inhabited Code :=
  ⟨zero⟩

/-! ### Numbering programs -/

/-- The number of a program: the five basic instructions are `0, …, 4`, and a compound program is
`4 * k + i + 5`, where `k` codes its components and `i < 4` its constructor. -/
def encodeCode : Code → ℕ
  | zero => 0
  | succ => 1
  | left => 2
  | right => 3
  | oracle => 4
  | pair cf cg => 4 * Nat.pair (encodeCode cf) (encodeCode cg) + 5
  | comp cf cg => 4 * Nat.pair (encodeCode cf) (encodeCode cg) + 1 + 5
  | prec cf cg => 4 * Nat.pair (encodeCode cf) (encodeCode cg) + 2 + 5
  | rfind' cf => 4 * encodeCode cf + 3 + 5

/-- The program with a given number, the inverse of `TauCeti.Oracle.Single.Code.encodeCode`. -/
def ofNatCode : ℕ → Code
  | 0 => zero
  | 1 => succ
  | 2 => left
  | 3 => right
  | 4 => oracle
  | n + 5 =>
    have hm : n / 4 < n + 5 := by omega
    have _m1 : (n / 4).unpair.1 < n + 5 := (Nat.unpair_left_le _).trans_lt hm
    have _m2 : (n / 4).unpair.2 < n + 5 := (Nat.unpair_right_le _).trans_lt hm
    match n % 4 with
    | 0 => pair (ofNatCode (n / 4).unpair.1) (ofNatCode (n / 4).unpair.2)
    | 1 => comp (ofNatCode (n / 4).unpair.1) (ofNatCode (n / 4).unpair.2)
    | 2 => prec (ofNatCode (n / 4).unpair.1) (ofNatCode (n / 4).unpair.2)
    | _ => rfind' (ofNatCode (n / 4))

/-- Decoding a number and encoding the result gives the number back. -/
@[simp]
theorem encodeCode_ofNatCode : ∀ n, encodeCode (ofNatCode n) = n
  | 0 | 1 | 2 | 3 | 4 => by simp [ofNatCode, encodeCode]
  | n + 5 => by
    have hm : n / 4 < n + 5 := by omega
    have _m1 : (n / 4).unpair.1 < n + 5 := (Nat.unpair_left_le _).trans_lt hm
    have _m2 : (n / 4).unpair.2 < n + 5 := (Nat.unpair_right_le _).trans_lt hm
    have IH := encodeCode_ofNatCode (n / 4)
    have IH1 := encodeCode_ofNatCode (n / 4).unpair.1
    have IH2 := encodeCode_ofNatCode (n / 4).unpair.2
    rw [ofNatCode]
    -- split on the constructor tag `n % 4`
    have h4 := Nat.div_add_mod n 4
    have hlt := Nat.mod_lt n (show 4 > 0 by omega)
    rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h <;>
      simp only [h, encodeCode, IH, IH1, IH2, Nat.pair_unpair] <;> omega

/-- Encoding a program and decoding the result gives the program back. -/
@[simp]
theorem ofNatCode_encodeCode (c : Code) : ofNatCode (encodeCode c) = c := by
  induction c <;> simp [encodeCode, ofNatCode, Nat.mul_add_div, *]

instance : Denumerable Code :=
  mk'
    { toFun := encodeCode
      invFun := ofNatCode
      left_inv := ofNatCode_encodeCode
      right_inv := encodeCode_ofNatCode }

/-- The `Denumerable` encoding of programs is `TauCeti.Oracle.Single.Code.encodeCode`. -/
theorem encodeCode_eq : encode = encodeCode :=
  rfl

/-- The `Denumerable` decoding of programs is `TauCeti.Oracle.Single.Code.ofNatCode`. -/
theorem ofNatCode_eq : ofNat Code = ofNatCode :=
  rfl

/-- The components of a pairing have smaller numbers. -/
theorem encode_lt_pair (cf cg : Code) :
    encode cf < encode (pair cf cg) ∧ encode cg < encode (pair cf cg) := by
  have := Nat.left_le_pair (encodeCode cf) (encodeCode cg)
  have := Nat.right_le_pair (encodeCode cf) (encodeCode cg)
  simp only [encodeCode_eq, encodeCode]
  omega

/-- The components of a composition have smaller numbers. -/
theorem encode_lt_comp (cf cg : Code) :
    encode cf < encode (comp cf cg) ∧ encode cg < encode (comp cf cg) := by
  have := Nat.left_le_pair (encodeCode cf) (encodeCode cg)
  have := Nat.right_le_pair (encodeCode cf) (encodeCode cg)
  simp only [encodeCode_eq, encodeCode]
  omega

/-- The components of a primitive recursion have smaller numbers. -/
theorem encode_lt_prec (cf cg : Code) :
    encode cf < encode (prec cf cg) ∧ encode cg < encode (prec cf cg) := by
  have := Nat.left_le_pair (encodeCode cf) (encodeCode cg)
  have := Nat.right_le_pair (encodeCode cf) (encodeCode cg)
  simp only [encodeCode_eq, encodeCode]
  omega

/-- The component of a search has a smaller number. -/
theorem encode_lt_rfind' (cf : Code) : encode cf < encode (rfind' cf) := by
  simp only [encodeCode_eq, encodeCode]
  omega

/-! ### Primitive recursive constructors -/

section Primrec

open Primrec

/-- Four times the `Nat.pair` of the numbers of two programs, given by their numbers, is primitive
recursive. -/
private theorem primrec_four_mul_pair :
    Primrec fun p : ℕ × ℕ => 4 * Nat.pair (encode (ofNat Code p.1)) (encode (ofNat Code p.2)) :=
  nat_mul.comp (const 4) <| Primrec₂.natPair.comp
    (encode_iff.2 <| (Primrec.ofNat Code).comp fst) (encode_iff.2 <| (Primrec.ofNat Code).comp snd)

/-- Pairing programs is primitive recursive. -/
theorem primrec₂_pair : Primrec₂ pair :=
  Primrec₂.ofNat_iff.2 <| Primrec₂.encode_iff.1 <| nat_add.comp primrec_four_mul_pair (const 5)

/-- Composing programs is primitive recursive. -/
theorem primrec₂_comp : Primrec₂ comp :=
  Primrec₂.ofNat_iff.2 <| Primrec₂.encode_iff.1 <|
    nat_add.comp (nat_add.comp primrec_four_mul_pair (const 1)) (const 5)

/-- Forming the primitive recursion of two programs is primitive recursive. -/
theorem primrec₂_prec : Primrec₂ prec :=
  Primrec₂.ofNat_iff.2 <| Primrec₂.encode_iff.1 <|
    nat_add.comp (nat_add.comp primrec_four_mul_pair (const 2)) (const 5)

/-- Forming the search program of a program is primitive recursive. -/
theorem primrec_rfind' : Primrec rfind' :=
  ofNat_iff.2 <| encode_iff.1 <|
    nat_add.comp (nat_add.comp (nat_mul.comp (const 4) <| encode_iff.2 <| Primrec.ofNat Code)
      (const 3)) (const 5)

/-- **Case analysis on programs is primitive recursive**, uniformly in a parameter: the branch
taken is read off the number of the program, and the branches receive its components. -/
theorem primrec_casesOn {α σ : Type*} [Primcodable α] [Primcodable σ] {c : α → Code}
    (hc : Primrec c) {z s l r o : α → σ} (hz : Primrec z) (hs : Primrec s) (hl : Primrec l)
    (hr : Primrec r) (ho : Primrec o) {pr co pc : α → Code × Code → σ} (hpr : Primrec₂ pr)
    (hco : Primrec₂ co) (hpc : Primrec₂ pc) {rf : α → Code → σ} (hrf : Primrec₂ rf) :
    Primrec fun a => Code.casesOn (motive := fun _ => σ) (c a) (z a) (s a) (l a) (r a) (o a)
      (fun cf cg => pr a (cf, cg)) (fun cf cg => co a (cf, cg)) (fun cf cg => pc a (cf, cg))
      (rf a) := by
  -- the components of a compound program with number `4 * q + i + 5`, from `q`
  let comps : ℕ → Code × Code := fun q => (ofNat Code q.unpair.1, ofNat Code q.unpair.2)
  have hcomps : Primrec comps :=
    ((Primrec.ofNat Code).comp (fst.comp Primrec.unpair)).pair
      ((Primrec.ofNat Code).comp (snd.comp Primrec.unpair))
  -- branch on the number `m` of the program: a basic instruction, or `m - 5 = 4 * q + i`
  have hm : Primrec fun a => encode (c a) := encode_iff.2 hc
  have hi : Primrec fun a => (encode (c a) - 5) % 4 := nat_mod.comp (nat_sub.comp hm (const 5))
    (const 4)
  have hq : Primrec fun a => (encode (c a) - 5) / 4 := nat_div.comp (nat_sub.comp hm (const 5))
    (const 4)
  have h : Primrec fun a =>
      if encode (c a) = 0 then z a else if encode (c a) = 1 then s a
      else if encode (c a) = 2 then l a else if encode (c a) = 3 then r a
      else if encode (c a) = 4 then o a
      else if (encode (c a) - 5) % 4 = 0 then pr a (comps ((encode (c a) - 5) / 4))
      else if (encode (c a) - 5) % 4 = 1 then co a (comps ((encode (c a) - 5) / 4))
      else if (encode (c a) - 5) % 4 = 2 then pc a (comps ((encode (c a) - 5) / 4))
      else rf a (ofNat Code ((encode (c a) - 5) / 4)) :=
    .ite (Primrec.eq.comp hm (const 0)) hz <| .ite (Primrec.eq.comp hm (const 1)) hs <|
      .ite (Primrec.eq.comp hm (const 2)) hl <| .ite (Primrec.eq.comp hm (const 3)) hr <|
      .ite (Primrec.eq.comp hm (const 4)) ho <|
      .ite (Primrec.eq.comp hi (const 0)) (hpr.comp .id (hcomps.comp hq)) <|
      .ite (Primrec.eq.comp hi (const 1)) (hco.comp .id (hcomps.comp hq)) <|
      .ite (Primrec.eq.comp hi (const 2)) (hpc.comp .id (hcomps.comp hq)) <|
      hrf.comp .id ((Primrec.ofNat Code).comp hq)
  refine h.of_eq fun a => ?_
  cases c a <;> simp [encodeCode_eq, encodeCode, comps, ofNatCode_eq, Nat.add_mod, Nat.mul_add_div]

end Primrec

/-! ### Evaluation -/

/-- The partial function computed by a program relative to the oracle `O`.
* `zero`, `succ`, `left`, `right`: zero, successor, and the two components of `Nat.unpair`.
* `oracle`: the oracle `O` itself, queried at the input.
* `pair cf cg`: pairs the outputs of `cf` and `cg` with `Nat.pair`.
* `comp cf cg`: runs `cg`, then `cf` on its output.
* `prec cf cg`: primitive recursion. On input `Nat.pair a 0` it returns the output of `cf` on `a`,
  and on `Nat.pair a (k + 1)` the output of `cg` on `Nat.pair a (Nat.pair k i)`, where `i` is the
  output of `prec cf cg` on `Nat.pair a k`.
* `rfind' cf`: search from a start. On input `Nat.pair a m` it returns the least `n ≥ m` with
  output `0` from `cf` on `Nat.pair a n`, provided `cf` halts on `Nat.pair a k` for every `k` from
  `m` to `n`. -/
def eval (O : ℕ →. ℕ) : Code → ℕ →. ℕ
  | zero => pure 0
  | succ => Nat.succ
  | left => ↑fun n : ℕ => n.unpair.1
  | right => ↑fun n : ℕ => n.unpair.2
  | oracle => O
  | pair cf cg => fun n => Nat.pair <$> eval O cf n <*> eval O cg n
  | comp cf cg => fun n => eval O cg n >>= eval O cf
  | prec cf cg =>
    Nat.unpaired fun a n =>
      n.rec (eval O cf a) fun y IH => do
        let i ← IH
        eval O cg (Nat.pair a (Nat.pair y i))
  | rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun m => m = 0) <$> eval O cf (Nat.pair a (n + m))).map (· + m)

variable {O : ℕ →. ℕ}

/-- The `zero` instruction returns `0`. -/
@[simp]
theorem eval_zero (n : ℕ) : eval O zero n = Part.some 0 :=
  (rfl)

/-- The `succ` instruction returns the successor of its input. -/
@[simp]
theorem eval_succ (n : ℕ) : eval O succ n = Part.some (n + 1) :=
  (rfl)

/-- The `left` instruction returns the first component of its unpaired input. -/
@[simp]
theorem eval_left (n : ℕ) : eval O left n = Part.some n.unpair.1 :=
  (rfl)

/-- The `right` instruction returns the second component of its unpaired input. -/
@[simp]
theorem eval_right (n : ℕ) : eval O right n = Part.some n.unpair.2 :=
  (rfl)

/-- The `oracle` instruction computes the oracle. -/
@[simp]
theorem eval_oracle : eval O oracle = O :=
  (rfl)

/-- `pair cf cg` pairs the outputs of `cf` and `cg`. -/
@[simp]
theorem eval_pair (cf cg : Code) (n : ℕ) :
    eval O (pair cf cg) n = Nat.pair <$> eval O cf n <*> eval O cg n :=
  (rfl)

/-- The outputs of `pair cf cg` are the pairings of outputs of `cf` and `cg`. -/
theorem mem_eval_pair {cf cg : Code} {n y : ℕ} :
    y ∈ eval O (pair cf cg) n ↔ ∃ y₁ ∈ eval O cf n, ∃ y₂ ∈ eval O cg n, Nat.pair y₁ y₂ = y := by
  simp only [eval_pair, Seq.seq, Part.map_eq_map, Part.bind_map, Part.mem_bind_iff,
    Part.mem_map_iff]

/-- `comp cf cg` runs `cg`, then `cf` on its output. -/
@[simp]
theorem eval_comp (cf cg : Code) (n : ℕ) :
    eval O (comp cf cg) n = eval O cg n >>= eval O cf :=
  (rfl)

/-- Primitive recursion at zero. -/
@[simp]
theorem eval_prec_zero (cf cg : Code) (a : ℕ) :
    eval O (prec cf cg) (Nat.pair a 0) = eval O cf a := by
  rw [eval, Nat.unpaired, Nat.unpair_pair, Nat.rec_zero]

/-- Primitive recursion at a successor. -/
theorem eval_prec_succ (cf cg : Code) (a k : ℕ) :
    eval O (prec cf cg) (Nat.pair a (k + 1)) =
      eval O (prec cf cg) (Nat.pair a k) >>= fun i => eval O cg (Nat.pair a (Nat.pair k i)) := by
  rw [eval, Nat.unpaired, Nat.unpair_pair]
  simp [Nat.unpaired]

/-- `rfind' cf` on `Nat.pair a m` searches for the least `n ≥ m` with output `0` from `cf` on
`Nat.pair a n`. -/
@[simp]
theorem eval_rfind' (cf : Code) (a m : ℕ) :
    eval O (rfind' cf) (Nat.pair a m) =
      (Nat.rfind fun n => (fun m => m = 0) <$> eval O cf (Nat.pair a (n + m))).map (· + m) := by
  rw [eval, Nat.unpaired, Nat.unpair_pair]

/-- One step of the search of `rfind' cf` from `m`: the search returns `m` when `cf` outputs `0`
at `m`, and otherwise, when `cf` halts at `m` with a nonzero output, continues from `m + 1`. -/
theorem mem_eval_rfind' {cf : Code} {a m y : ℕ} :
    y ∈ eval O (rfind' cf) (Nat.pair a m) ↔ ∃ x ∈ eval O cf (Nat.pair a m),
      x = 0 ∧ y = m ∨ x ≠ 0 ∧ y ∈ eval O (rfind' cf) (Nat.pair a (m + 1)) := by
  have key {k j : ℕ} : j ∈ Nat.rfind (fun n => (fun m => decide (m = 0)) <$>
      eval O cf (Nat.pair a (n + k))) ↔ (∃ x ∈ eval O cf (Nat.pair a (j + k)), x = 0) ∧
        ∀ {i}, i < j → ∃ x ∈ eval O cf (Nat.pair a (i + k)), x ≠ 0 := by
    refine Nat.mem_rfind.trans ?_
    simp [Part.mem_map_iff]
  simp only [eval_rfind', Part.mem_map_iff, key]
  constructor
  · rintro ⟨j, ⟨⟨x, hx, hx0⟩, hlt⟩, rfl⟩
    cases j with
    | zero => exact ⟨x, by simpa using hx, Or.inl ⟨hx0, by simp⟩⟩
    | succ j =>
      obtain ⟨x', hx', hx'0⟩ := hlt (Nat.succ_pos j)
      refine ⟨x', by simpa using hx', Or.inr ⟨hx'0, j,
        ⟨⟨x, by simpa [Nat.add_right_comm, Nat.add_assoc] using hx, hx0⟩, fun {i} hi => ?_⟩,
        by omega⟩⟩
      obtain ⟨z, hz, hz0⟩ := hlt (Nat.succ_lt_succ hi)
      exact ⟨z, by simpa [Nat.add_right_comm, Nat.add_assoc] using hz, hz0⟩
  · rintro ⟨x, hx, ⟨rfl, rfl⟩ | ⟨hx0, j, ⟨⟨z, hz, hz0⟩, hlt⟩, rfl⟩⟩
    · exact ⟨0, ⟨⟨0, by simpa using hx, rfl⟩, fun h => absurd h (by omega)⟩, by simp⟩
    · refine ⟨j + 1,
        ⟨⟨z, by simpa [Nat.add_right_comm, Nat.add_assoc] using hz, hz0⟩, fun {i} hi => ?_⟩,
        by omega⟩
      cases i with
      | zero => exact ⟨x, by simpa using hx, hx0⟩
      | succ i =>
        obtain ⟨w, hw, hw0⟩ := hlt (Nat.lt_of_succ_lt_succ hi)
        exact ⟨w, by simpa [Nat.add_right_comm, Nat.add_assoc] using hw, hw0⟩

/-- The search of `rfind' cf` from `m` returns a number at least `m`. -/
theorem le_of_mem_eval_rfind' {cf : Code} {a m y : ℕ}
    (h : y ∈ eval O (rfind' cf) (Nat.pair a m)) : m ≤ y := by
  rw [eval_rfind', Part.mem_map_iff] at h
  obtain ⟨j, -, rfl⟩ := h
  exact Nat.le_add_left m j

/-! ### Adequacy -/

/-- Every program computes a function recursive in its oracle. -/
theorem recursiveIn_eval (O : ℕ →. ℕ) (c : Code) : Nat.RecursiveIn {O} (eval O c) := by
  -- each clause of `eval` is the function of the matching constructor of `Nat.RecursiveIn`
  induction c with
  | zero => exact .zero
  | succ => exact .succ
  | left => exact .left
  | right => exact .right
  | oracle => exact .oracle O rfl
  | pair cf cg ihf ihg => exact ihf.pair ihg
  | comp cf cg ihf ihg => exact ihf.comp ihg
  | prec cf cg ihf ihg => exact ihf.prec ihg
  | rfind' cf ihf => exact ihf.rfind'

/-- Every function recursive in `O` is computed by a program relative to `O`. -/
theorem exists_code_of_recursiveIn {f : ℕ →. ℕ} (hf : Nat.RecursiveIn {O} f) :
    ∃ c, eval O c = f := by
  -- each constructor of `Nat.RecursiveIn` is the function of the matching clause of `eval`
  induction hf with
  | zero => exact ⟨zero, rfl⟩
  | succ => exact ⟨succ, rfl⟩
  | left => exact ⟨left, rfl⟩
  | right => exact ⟨right, rfl⟩
  | oracle g hg =>
    rw [Set.mem_singleton_iff] at hg
    exact ⟨oracle, hg.symm⟩
  | pair _ _ ihf ihg =>
    obtain ⟨cf, rfl⟩ := ihf
    obtain ⟨cg, rfl⟩ := ihg
    exact ⟨pair cf cg, rfl⟩
  | comp _ _ ihf ihg =>
    obtain ⟨cf, rfl⟩ := ihf
    obtain ⟨cg, rfl⟩ := ihg
    exact ⟨comp cf cg, rfl⟩
  | prec _ _ ihf ihg =>
    obtain ⟨cf, rfl⟩ := ihf
    obtain ⟨cg, rfl⟩ := ihg
    exact ⟨prec cf cg, rfl⟩
  | rfind _ ihf =>
    obtain ⟨cf, rfl⟩ := ihf
    -- search from zero: run `rfind' cf` on `Nat.pair a 0`
    refine ⟨comp (rfind' cf) (pair (pair left right) zero), funext fun a => ?_⟩
    simp [eval, Seq.seq, pure, PFun.pure, Part.map_id']

/-- **Adequacy.** For every oracle `O`, a partial function is recursive in `O` exactly when some
program computes it relative to `O`. -/
theorem exists_code {f : ℕ →. ℕ} : Nat.RecursiveIn {O} f ↔ ∃ c, eval O c = f :=
  ⟨exists_code_of_recursiveIn, fun ⟨c, hc⟩ => hc ▸ recursiveIn_eval O c⟩

/-- **Adequacy for Turing reducibility.** `f` is Turing reducible to `g` exactly when some program
computes `f` relative to the oracle `g`. -/
theorem turingReducible_iff_exists_code {f g : ℕ →. ℕ} :
    TuringReducible f g ↔ ∃ c, eval g c = f := by
  rw [TuringReducible, RecursiveIn.iff_nat, exists_code]

end Code

end Oracle.Single

end TauCeti

/-! ### Query-free programs -/

namespace Nat.Partrec.Code

/-- The query-free program of an ordinary Mathlib code: the same code, never using `oracle`. -/
def toSingleOracleCode : Nat.Partrec.Code → TauCeti.Oracle.Single.Code
  | zero => .zero
  | succ => .succ
  | left => .left
  | right => .right
  | pair cf cg => .pair cf.toSingleOracleCode cg.toSingleOracleCode
  | comp cf cg => .comp cf.toSingleOracleCode cg.toSingleOracleCode
  | prec cf cg => .prec cf.toSingleOracleCode cg.toSingleOracleCode
  | rfind' cf => .rfind' cf.toSingleOracleCode

/-- `Nat.Partrec.Code.toSingleOracleCode` is injective: distinct ordinary codes give distinct
programs. -/
theorem toSingleOracleCode_injective : Function.Injective toSingleOracleCode := by
  intro c
  induction c <;> intro d h <;> cases d <;> grind [toSingleOracleCode]

/-- The translation of ordinary codes into query-free programs is primitive recursive. -/
theorem primrec_toSingleOracleCode : Primrec toSingleOracleCode := by
  -- the recursive calls are the last two components of the data passed to each step
  have h₂ {f : TauCeti.Oracle.Single.Code → TauCeti.Oracle.Single.Code →
      TauCeti.Oracle.Single.Code} (hf : Primrec₂ f) :
      Primrec fun a : Nat.Partrec.Code × Nat.Partrec.Code × Nat.Partrec.Code ×
          TauCeti.Oracle.Single.Code × TauCeti.Oracle.Single.Code =>
        f a.2.2.2.1 a.2.2.2.2 :=
    hf.comp (Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.snd)
      (Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.snd)
  refine (primrec_recOn (c := id) _root_.Primrec.id
    (_root_.Primrec.const TauCeti.Oracle.Single.Code.zero)
    (_root_.Primrec.const TauCeti.Oracle.Single.Code.succ)
    (_root_.Primrec.const TauCeti.Oracle.Single.Code.left)
    (_root_.Primrec.const TauCeti.Oracle.Single.Code.right)
    (pr := fun _ _ _ => .pair) (h₂ TauCeti.Oracle.Single.Code.primrec₂_pair)
    (co := fun _ _ _ => .comp) (h₂ TauCeti.Oracle.Single.Code.primrec₂_comp)
    (pc := fun _ _ _ => .prec) (h₂ TauCeti.Oracle.Single.Code.primrec₂_prec)
    (rf := fun _ _ => .rfind')
    (TauCeti.Oracle.Single.Code.primrec_rfind'.comp <| Primrec.snd.comp Primrec.snd)).of_eq
    fun c => ?_
  induction c <;> simp_all [toSingleOracleCode]

end Nat.Partrec.Code

namespace TauCeti.Oracle.Single.Code

/-- **Query-free programs.** Relative to every oracle, the program `c.toSingleOracleCode` computes
the same function as the ordinary code `c`. -/
@[simp]
theorem eval_toSingleOracleCode (O : ℕ →. ℕ) (c : Nat.Partrec.Code) :
    eval O c.toSingleOracleCode = c.eval := by
  induction c with
  | zero | succ | left | right => rfl
  | pair cf cg ihf ihg =>
    rw [Nat.Partrec.Code.toSingleOracleCode, eval, Nat.Partrec.Code.eval, ihf, ihg]
  | comp cf cg ihf ihg =>
    rw [Nat.Partrec.Code.toSingleOracleCode, eval, Nat.Partrec.Code.eval, ihf, ihg]
  | prec cf cg ihf ihg =>
    rw [Nat.Partrec.Code.toSingleOracleCode, eval, Nat.Partrec.Code.eval, ihf, ihg]
  | rfind' cf ihf => rw [Nat.Partrec.Code.toSingleOracleCode, eval, Nat.Partrec.Code.eval, ihf]

end TauCeti.Oracle.Single.Code
