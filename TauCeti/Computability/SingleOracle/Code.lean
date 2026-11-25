/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.TuringDegree
import TauCeti.Computability.RecursiveIn
import TauCeti.Data.PFun.Basic

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
* `TauCeti.Oracle.Single.Code.interList`, `TauCeti.Oracle.Single.Code.restrictId`: direct
  domain combinators valid relative to every partial oracle.
* `Nat.Partrec.Code.toSingleOracleCode`: the query-free program of an ordinary Mathlib code.
* `TauCeti.Oracle.Single.Code.toPartrecCode`: the ordinary Mathlib code obtained by replacing every
  `oracle` instruction by `zero`.
* `TauCeti.Oracle.Single.Code.curry`: the program that specializes the first input of a program
  to a parameter.
* `TauCeti.Oracle.Single.Code.fixInput`: the program that runs a program on a fixed input,
  ignoring its own input.
* `TauCeti.Oracle.Single.Code.haltingIndex`: the number of such a fixed-input program.

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
* `TauCeti.Oracle.Single.Code.eval_toPartrecCode`,
  `TauCeti.Oracle.Single.Code.eval_toPartrecCode_zero`,
  `TauCeti.Oracle.Single.Code.primrec_toPartrecCode`: specializing an oracle program to an
  always-zero oracle is primitive recursive and preserves evaluation.
* `TauCeti.Oracle.Single.Code.eval_curry`, `TauCeti.Oracle.Single.Code.eval_fixInput`:
  specialization and fixing an input preserve evaluation, relative to every oracle.
* `TauCeti.Oracle.Single.Code.curry_inj`, `TauCeti.Oracle.Single.Code.fixInput_inj`,
  `TauCeti.Oracle.Single.Code.haltingIndex_inj`: these compilers retain both the source program and
  the parameter or input.
* `TauCeti.Oracle.Single.Code.exists_forall_eval_eq_of_partrec`: every partial recursive function
  is computed by one program relative to every oracle.
* `TauCeti.Oracle.Single.Code.exists_code_of_computable`: in particular, every computable function
  is computed by one program relative to every oracle.
* `TauCeti.Oracle.Single.Code.exists_code`,
  `TauCeti.Oracle.Single.Code.recursiveIn_decode_restrict`: adequacy for `Nat.RecursiveIn {O}`
  and restricting partial decoding to a program's domain.
* `TauCeti.Oracle.Single.Code.turingReducible_iff_exists_code`: the same for Turing
  reducibility.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.1.
* M. Carneiro, *Formalizing computability theory via partial recursive functions*, ITP 2019. The
  numbering, the evaluation and the adequacy proof follow Mathlib's `Nat.Partrec.Code`,
  `Nat.Partrec.Code.eval` and `Nat.Partrec.Code.exists_code`, extended by the oracle instruction.
  Parameter specialization follows Mathlib's `Nat.Partrec.Code.curry`.
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

/-- If the left evaluation returns `a`, pair `a` with the result of the right evaluation. -/
theorem eval_pair_of_left_eq_some {cf cg : Code} {n a : ℕ}
    (h : eval O cf n = Part.some a) :
    eval O (pair cf cg) n = (eval O cg n).map (Nat.pair a) := by
  ext y
  simp only [mem_eval_pair, h, Part.mem_some_iff, exists_eq_left, Part.mem_map_iff]

/-- Pairing the two projections reconstructs the input. -/
@[simp high]
theorem eval_pair_left_right (n : ℕ) :
    eval O (pair left right) n = Part.some n := by
  rw [eval_pair_of_left_eq_some (eval_left n), eval_right, Part.map_some, Nat.pair_unpair]

/-- Pairing zero with the reconstructed input supplies an initial argument for recursion. -/
@[simp high]
theorem eval_pair_zero_left_right (n : ℕ) :
    eval O (pair zero (pair left right)) n = Part.some (Nat.pair 0 n) := by
  rw [eval_pair_of_left_eq_some (eval_zero n), eval_pair_left_right, Part.map_some]

/-- Pairing the reconstructed input with zero supplies a zero starting index for search. -/
@[simp high]
theorem eval_pair_left_right_zero (n : ℕ) :
    eval O (pair (pair left right) zero) n = Part.some (Nat.pair n 0) := by
  rw [eval_pair_of_left_eq_some (eval_pair_left_right n), eval_zero, Part.map_some]

/-- `comp cf cg` runs `cg`, then `cf` on its output. -/
@[simp]
theorem eval_comp (cf cg : Code) (n : ℕ) :
    eval O (comp cf cg) n = eval O cg n >>= eval O cf :=
  (rfl)

/-- Evaluation of a composed program is partial-function composition. -/
theorem eval_comp_eq (O : ℕ →. ℕ) (cf cg : Code) :
    eval O (comp cf cg) = (eval O cf).comp (eval O cg) :=
  funext fun x => (eval_comp cf cg x).trans (PFun.comp_apply (eval O cf) (eval O cg) x).symm

/-- The domain of a paired program is the intersection of the two domains, relative to every
partial oracle. -/
@[simp]
theorem dom_eval_pair (O : ℕ →. ℕ) (cf cg : Code) :
    (eval O (pair cf cg)).Dom = (eval O cf).Dom ∩ (eval O cg).Dom := by
  ext x
  simp [PFun.Dom, Seq.seq]

/-- The domain of a composed program is the partial preimage of the outer domain under the inner
program, relative to every partial oracle. -/
@[simp]
theorem dom_eval_comp (O : ℕ →. ℕ) (cf cg : Code) :
    (eval O (comp cf cg)).Dom = (eval O cg).preimage (eval O cf).Dom := by
  rw [eval_comp_eq, PFun.dom_comp]

/-- Uniform finite-intersection compiler for a list of oracle programs. -/
def interList (cs : List Code) : Code :=
  cs.foldr pair zero

/-- The empty intersection is the everywhere-defined program `zero`. -/
@[simp]
theorem interList_nil : interList [] = zero :=
  (rfl)

/-- Consing a program intersects its domain with the rest of the list. -/
@[simp]
theorem interList_cons (c : Code) (cs : List Code) :
    interList (c :: cs) = pair c (interList cs) :=
  (rfl)

/-- Finite intersection of program lists is primitive recursive. -/
theorem primrec_interList : Primrec interList :=
  (Primrec.list_foldr (h := fun (_ : List Code) (p : Code × Code) => pair p.1 p.2)
    Primrec.id (Primrec.const zero) <|
      Primrec₂.mk (primrec₂_pair.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).of_eq
    fun _ => rfl

/-- The domain of `interList cs` is the intersection of the domains of its entries, relative to
every partial oracle. -/
@[simp]
theorem dom_eval_interList (O : ℕ →. ℕ) (cs : List Code) :
    (eval O (interList cs)).Dom = ⋂ c ∈ cs, (eval O c).Dom := by
  induction cs with
  | nil =>
    ext x
    simp [PFun.Dom]
  | cons c cs ih =>
    simp [ih]

/-- Restrict the identity function on `ℕ` to the domain of `c`. -/
def restrictId (c : Code) : Code :=
  comp left (pair (pair left right) c)

/-- Unfolding equation for `restrictId`. -/
theorem restrictId_def (c : Code) :
    restrictId c = comp left (pair (pair left right) c) :=
  (rfl)

/-- Domain restriction of the identity is primitive recursive on programs. -/
theorem primrec_restrictId : Primrec restrictId :=
  primrec₂_comp.comp (Primrec.const left)
    (primrec₂_pair.comp (Primrec.const (pair left right)) Primrec.id)

/-- `restrictId c` outputs its input `x` whenever `c` halts on `x`, and diverges otherwise,
relative to every partial oracle. -/
@[simp]
theorem eval_restrictId (O : ℕ →. ℕ) (c : Code) (x : ℕ) :
    eval O (restrictId c) x = (eval O c x).map fun _ => x := by
  have hleft : eval O left = fun p => Part.some p.unpair.1 := funext eval_left
  rw [restrictId, eval_comp, eval_pair_of_left_eq_some (eval_pair_left_right x), hleft]
  simp [Part.bind_some_eq_map, Part.map_map, Function.comp_def]

/-- `restrictId c` has the same domain as `c`, relative to every partial oracle. -/
@[simp]
theorem dom_eval_restrictId (O : ℕ →. ℕ) (c : Code) :
    (eval O (restrictId c)).Dom = (eval O c).Dom := by
  ext x
  simp [PFun.Dom]

/-- The range of `restrictId c` is the domain of `c`, relative to every partial oracle. -/
@[simp]
theorem ran_eval_restrictId (O : ℕ →. ℕ) (c : Code) :
    (eval O (restrictId c)).ran = (eval O c).Dom := by
  have hrestrict : eval O (restrictId c) = fun x => (eval O c x).map fun _ => x :=
    funext (eval_restrictId O c)
  rw [hrestrict, PFun.ran_map_const]

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

/-- Primitive recursion at one unpacks a single recursion step from the base case. -/
@[simp]
theorem eval_prec_one (cf cg : Code) (a : ℕ) :
    eval O (prec cf cg) (Nat.pair a 1) =
      eval O cf a >>= fun y => eval O cg (Nat.pair a (Nat.pair 0 y)) := by
  simpa using eval_prec_succ cf cg a 0

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
    rw [eval_comp, eval_pair_left_right_zero, PFun.some_bind, eval_rfind']
    simp [Part.map_id']

/-- **Adequacy.** For every oracle `O`, a partial function is recursive in `O` exactly when some
program computes it relative to `O`. -/
theorem exists_code {f : ℕ →. ℕ} : Nat.RecursiveIn {O} f ↔ ∃ c, eval O c = f :=
  ⟨exists_code_of_recursiveIn, fun ⟨c, hc⟩ => hc ▸ recursiveIn_eval O c⟩

/-- **Adequacy for Turing reducibility.** `f` is Turing reducible to `g` exactly when some program
computes `f` relative to the oracle `g`. -/
theorem turingReducible_iff_exists_code {f g : ℕ →. ℕ} :
    TuringReducible f g ↔ ∃ c, eval g c = f := by
  rw [TuringReducible, RecursiveIn.iff_nat, exists_code]

/-- Restricting partial decoding `ℕ →. α` to the domain of an oracle program `c` on encoded
inputs is recursive in the oracle. -/
theorem recursiveIn_decode_restrict {α : Type*} [Primcodable α] (O : ℕ →. ℕ) (c : Code) :
    RecursiveIn {O} fun n =>
      (Part.ofOption (decode (α := α) n)).bind fun x =>
        (eval O c (encode x)).map fun _ => x := by
  have hdec : Nat.RecursiveIn {O} fun n => Part.ofOption ((decode (α := α) n).map encode) :=
    (Partrec.nat_iff.1 (Computable.ofOption
      (Computable.decode.option_map (Computable.encode.comp Computable.snd).to₂))).recursiveIn
  have heq : ∀ n : ℕ,
      ((Part.ofOption ((decode (α := α) n).map encode)).bind fun k =>
        eval O (restrictId c) k) =
      ((Part.ofOption (decode (α := α) n)).bind fun x =>
        (eval O c (encode x)).map fun _ => x).map encode := by
    intro n
    cases decode (α := α) n with
    | none => simp [Part.bind_none]
    | some x => simp [Part.bind_some, Part.map_map, Function.comp_def]
  exact RecursiveIn.iff_nat_map_encode.2
    (((recursiveIn_eval O (restrictId c)).comp hdec).of_eq heq)

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

/-- Translation to single-oracle code preserves each constructor of an ordinary program. -/
theorem toSingleOracleCode_def (c : Nat.Partrec.Code) :
    c.toSingleOracleCode = match c with
      | zero => .zero
      | succ => .succ
      | left => .left
      | right => .right
      | pair cf cg => .pair cf.toSingleOracleCode cg.toSingleOracleCode
      | comp cf cg => .comp cf.toSingleOracleCode cg.toSingleOracleCode
      | prec cf cg => .prec cf.toSingleOracleCode cg.toSingleOracleCode
      | rfind' cf => .rfind' cf.toSingleOracleCode := by
  cases c <;> rfl

/-- `toSingleOracleCode` maps `Nat.Partrec.Code.zero` to `zero`. -/
@[simp] theorem toSingleOracleCode_zero : toSingleOracleCode .zero = .zero := by
  rw [toSingleOracleCode]

/-- `toSingleOracleCode` maps `Nat.Partrec.Code.succ` to `succ`. -/
@[simp] theorem toSingleOracleCode_succ : toSingleOracleCode .succ = .succ := by
  rw [toSingleOracleCode]

/-- `toSingleOracleCode` maps `Nat.Partrec.Code.left` to `left`. -/
@[simp] theorem toSingleOracleCode_left : toSingleOracleCode .left = .left := by
  rw [toSingleOracleCode]

/-- `toSingleOracleCode` maps `Nat.Partrec.Code.right` to `right`. -/
@[simp] theorem toSingleOracleCode_right : toSingleOracleCode .right = .right := by
  rw [toSingleOracleCode]

/-- `toSingleOracleCode` distributes over `pair`. -/
@[simp] theorem toSingleOracleCode_pair (cf cg : Nat.Partrec.Code) :
    toSingleOracleCode (.pair cf cg) = .pair cf.toSingleOracleCode cg.toSingleOracleCode := by
  rw [toSingleOracleCode]

/-- `toSingleOracleCode` distributes over `comp`. -/
@[simp] theorem toSingleOracleCode_comp (cf cg : Nat.Partrec.Code) :
    toSingleOracleCode (.comp cf cg) = .comp cf.toSingleOracleCode cg.toSingleOracleCode := by
  rw [toSingleOracleCode]

/-- `toSingleOracleCode` distributes over `prec`. -/
@[simp] theorem toSingleOracleCode_prec (cf cg : Nat.Partrec.Code) :
    toSingleOracleCode (.prec cf cg) = .prec cf.toSingleOracleCode cg.toSingleOracleCode := by
  rw [toSingleOracleCode]

/-- `toSingleOracleCode` distributes over `rfind'`. -/
@[simp] theorem toSingleOracleCode_rfind' (cf : Nat.Partrec.Code) :
    toSingleOracleCode (.rfind' cf) = .rfind' cf.toSingleOracleCode := by
  rw [toSingleOracleCode]

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

/-- Specialize a program's first input to `a`, leaving the second input free. -/
def curry (c : Code) (a : ℕ) : Code :=
  comp c (pair (Nat.Partrec.Code.const a).toSingleOracleCode (pair left right))

/-- Specialization composes the program with the pairing of the ordinary constant program for
the parameter and the identity program. -/
theorem curry_def (c : Code) (a : ℕ) :
    c.curry a = comp c (pair (Nat.Partrec.Code.const a).toSingleOracleCode (pair left right)) :=
  (rfl)

/-- Parameter specialization preserves evaluation, uniformly for every partial oracle. -/
@[simp]
theorem eval_curry (O : ℕ →. ℕ) (c : Code) (a x : ℕ) :
    eval O (curry c a) x = eval O c (Nat.pair a x) := by
  simp [curry, Nat.Partrec.Code.eval_const, Seq.seq, PFun.some_bind]

/-- The parameter compiler is primitive recursive on programs and parameters. -/
theorem primrec₂_curry : Primrec₂ curry :=
  primrec₂_comp.comp Primrec.fst <| primrec₂_pair.comp
    (Nat.Partrec.Code.primrec_toSingleOracleCode.comp
      (Nat.Partrec.Code.primrec_const.comp Primrec.snd))
    (Primrec.const (pair left right))

/-- Specialization retains both the source program and the parameter in its syntax. -/
@[simp]
theorem curry_inj {c d : Code} {a b : ℕ} : c.curry a = d.curry b ↔ c = d ∧ a = b := by
  constructor
  · intro h
    simp only [curry, Code.comp.injEq, Code.pair.injEq] at h
    exact ⟨h.1, Nat.Partrec.Code.const_inj
      (Nat.Partrec.Code.toSingleOracleCode_injective h.2.1)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Run `c` on the fixed input `x`, ignoring the input of the compiled program. -/
def fixInput (c : Code) (x : ℕ) : Code :=
  comp c (Nat.Partrec.Code.const x).toSingleOracleCode

/-- Fixing an input composes the program with the ordinary constant program for that input. -/
theorem fixInput_def (c : Code) (x : ℕ) :
    c.fixInput x = comp c (Nat.Partrec.Code.const x).toSingleOracleCode :=
  (rfl)

/-- Fixing an input retains both the source program and the input in its syntax. -/
@[simp]
theorem fixInput_inj {c d : Code} {x y : ℕ} : c.fixInput x = d.fixInput y ↔ c = d ∧ x = y := by
  constructor
  · intro h
    rw [fixInput, fixInput, Code.comp.injEq] at h
    exact ⟨h.1, Nat.Partrec.Code.const_inj
      (Nat.Partrec.Code.toSingleOracleCode_injective h.2)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Fixing an input is primitive recursive in the program and the input. -/
theorem primrec₂_fixInput : Primrec₂ fixInput :=
  primrec₂_comp.comp Primrec.fst <|
    Nat.Partrec.Code.primrec_toSingleOracleCode.comp
      (Nat.Partrec.Code.primrec_const.comp Primrec.snd)

/-- The compiled program runs its source on the fixed input for every partial oracle. -/
@[simp]
theorem eval_fixInput (O : ℕ →. ℕ) (c : Code) (x y : ℕ) :
    eval O (c.fixInput x) y = eval O c x := by
  rw [fixInput, eval_comp, eval_toSingleOracleCode, Nat.Partrec.Code.eval_const]
  exact Part.bind_some x (fun n => eval O c n)

/-- The index of a program that runs `c` on the fixed input `x`, ignoring its own input. -/
def haltingIndex (c : Code) (x : ℕ) : ℕ :=
  encode (c.fixInput x)

/-- Decoding a halting index recovers the fixed-input program. -/
@[simp]
theorem ofNat_haltingIndex (c : Code) (x : ℕ) :
    ofNat Code (c.haltingIndex x) = c.fixInput x := by
  rw [haltingIndex, ofNat_encode]

/-- Computing the index of a fixed-input program is primitive recursive. -/
theorem primrec₂_haltingIndex : Primrec₂ haltingIndex :=
  Primrec.encode.comp primrec₂_fixInput

/-- The halting index retains both the program and its fixed input. -/
@[simp]
theorem haltingIndex_inj {c d : Code} {x y : ℕ} :
    haltingIndex c x = haltingIndex d y ↔ c = d ∧ x = y := by
  rw [haltingIndex, haltingIndex, encode_inj, fixInput_inj]

/-- Every partial recursive function is computed by one program relative to every oracle: the
query-free program of an ordinary code computing it. -/
theorem exists_forall_eval_eq_of_partrec {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    ∃ c : Code, ∀ O, eval O c = f := by
  obtain ⟨c, rfl⟩ := Nat.Partrec.Code.exists_code.1 hf
  exact ⟨c.toSingleOracleCode, fun O => eval_toSingleOracleCode O c⟩

/-- A computable function is computed by one program relative to every oracle. -/
theorem exists_code_of_computable {g : ℕ → ℕ} (hg : Computable g) :
    ∃ c : Code, ∀ O n, eval O c n = Part.some (g n) :=
  (exists_forall_eval_eq_of_partrec (Partrec.nat_iff.1 hg)).imp fun _ h O n => by simp [h O]

/-! ### Specializing oracle programs to the constant-zero oracle -/

/-- Replace every `oracle` instruction by `zero`, turning an oracle program into an ordinary
Mathlib code. Relative to the constant-zero oracle (in particular the empty set oracle), the
resulting ordinary code computes the same partial function. -/
def toPartrecCode : Code → Nat.Partrec.Code
  | zero => .zero
  | succ => .succ
  | left => .left
  | right => .right
  | oracle => .zero
  | pair cf cg => .pair cf.toPartrecCode cg.toPartrecCode
  | comp cf cg => .comp cf.toPartrecCode cg.toPartrecCode
  | prec cf cg => .prec cf.toPartrecCode cg.toPartrecCode
  | rfind' cf => .rfind' cf.toPartrecCode

/-- `toPartrecCode` maps `zero` to `Nat.Partrec.Code.zero`. -/
@[simp] theorem toPartrecCode_zero : toPartrecCode zero = .zero := by rw [toPartrecCode]

/-- `toPartrecCode` maps `succ` to `Nat.Partrec.Code.succ`. -/
@[simp] theorem toPartrecCode_succ : toPartrecCode succ = .succ := by rw [toPartrecCode]

/-- `toPartrecCode` maps `left` to `Nat.Partrec.Code.left`. -/
@[simp] theorem toPartrecCode_left : toPartrecCode left = .left := by rw [toPartrecCode]

/-- `toPartrecCode` maps `right` to `Nat.Partrec.Code.right`. -/
@[simp] theorem toPartrecCode_right : toPartrecCode right = .right := by rw [toPartrecCode]

/-- `toPartrecCode` replaces `oracle` by `Nat.Partrec.Code.zero`. -/
@[simp] theorem toPartrecCode_oracle : toPartrecCode oracle = .zero := by rw [toPartrecCode]

/-- `toPartrecCode` distributes over `pair`. -/
@[simp] theorem toPartrecCode_pair (cf cg : Code) :
    toPartrecCode (pair cf cg) = .pair cf.toPartrecCode cg.toPartrecCode := by rw [toPartrecCode]

/-- `toPartrecCode` distributes over `comp`. -/
@[simp] theorem toPartrecCode_comp (cf cg : Code) :
    toPartrecCode (comp cf cg) = .comp cf.toPartrecCode cg.toPartrecCode := by rw [toPartrecCode]

/-- `toPartrecCode` distributes over `prec`. -/
@[simp] theorem toPartrecCode_prec (cf cg : Code) :
    toPartrecCode (prec cf cg) = .prec cf.toPartrecCode cg.toPartrecCode := by rw [toPartrecCode]

/-- `toPartrecCode` distributes over `rfind'`. -/
@[simp] theorem toPartrecCode_rfind' (cf : Code) :
    toPartrecCode (rfind' cf) = .rfind' cf.toPartrecCode := by rw [toPartrecCode]

/-- Specializing a query-free program recovers the original ordinary code. -/
@[simp]
theorem toPartrecCode_toSingleOracleCode (c : Nat.Partrec.Code) :
    c.toSingleOracleCode.toPartrecCode = c := by
  induction c <;> simp [Nat.Partrec.Code.toSingleOracleCode, *]

/-- Relative to any oracle that always answers `0` (such as the empty set oracle), every oracle
program computes the same partial function as its ordinary specialization `toPartrecCode`. -/
theorem eval_toPartrecCode {O : ℕ →. ℕ} (hO : ∀ n, O n = Part.some 0) (c : Code) :
    eval O c = c.toPartrecCode.eval := by
  induction c with
  | zero | succ | left | right => rfl
  | oracle => exact funext hO
  | pair cf cg ihf ihg => rw [toPartrecCode, eval, Nat.Partrec.Code.eval, ihf, ihg]
  | comp cf cg ihf ihg => rw [toPartrecCode, eval, Nat.Partrec.Code.eval, ihf, ihg]
  | prec cf cg ihf ihg => rw [toPartrecCode, eval, Nat.Partrec.Code.eval, ihf, ihg]
  | rfind' cf ihf => rw [toPartrecCode, eval, Nat.Partrec.Code.eval, ihf]

/-- An ordinary specialization `c.toPartrecCode` computes the same partial function as `c`
relative to the constant-zero oracle. -/
@[simp]
theorem eval_toPartrecCode_zero (c : Code) :
    c.toPartrecCode.eval = eval (((fun _ : ℕ => 0) : ℕ → ℕ) : ℕ →. ℕ) c :=
  (eval_toPartrecCode (fun n => PFun.coe_val (fun _ : ℕ => 0) n) c).symm

/-- One strong-recursion step for `toPartrecCode`, building the ordinary code of
`ofNat Code L.length` from the table `L` of already-translated smaller codes. -/
private def toPartrecCodeStep (L : List Nat.Partrec.Code) : Nat.Partrec.Code :=
  let lup (c : Code) : Nat.Partrec.Code := (L[encode c]?).getD .zero
  Code.casesOn (motive := fun _ => Nat.Partrec.Code) (ofNat Code L.length)
    .zero .succ .left .right .zero
    (fun cf cg => .pair (lup cf) (lup cg))
    (fun cf cg => .comp (lup cf) (lup cg))
    (fun cf cg => .prec (lup cf) (lup cg))
    (fun cf => .rfind' (lup cf))

private theorem primrec_toPartrecCodeStep : Primrec toPartrecCodeStep := by
  open Primrec in
  let lup (L : List Nat.Partrec.Code) (c : Code) : Nat.Partrec.Code :=
    (L[encode c]?).getD .zero
  have hlup {β : Type} [Primcodable β] {L : β → List Nat.Partrec.Code} {c : β → Code}
      (hL : Primrec L) (hc : Primrec c) : Primrec fun b => lup (L b) (c b) :=
    option_getD.comp (list_getElem?.comp hL (encode_iff.2 hc)) (const Nat.Partrec.Code.zero)
  have hL : Primrec fun x : List Nat.Partrec.Code × Code × Code => x.1 := fst
  have hcf : Primrec fun x : List Nat.Partrec.Code × Code × Code => x.2.1 := fst.comp snd
  have hcg : Primrec fun x : List Nat.Partrec.Code × Code × Code => x.2.2 := snd.comp snd
  exact primrec_casesOn ((Primrec.ofNat Code).comp list_length)
    (const Nat.Partrec.Code.zero) (const Nat.Partrec.Code.succ) (const Nat.Partrec.Code.left)
    (const Nat.Partrec.Code.right) (const Nat.Partrec.Code.zero)
    (pr := fun L cs => .pair (lup L cs.1) (lup L cs.2))
    (Primrec₂.mk (Nat.Partrec.Code.primrec₂_pair.comp (hlup hL hcf) (hlup hL hcg)))
    (co := fun L cs => .comp (lup L cs.1) (lup L cs.2))
    (Primrec₂.mk (Nat.Partrec.Code.primrec₂_comp.comp (hlup hL hcf) (hlup hL hcg)))
    (pc := fun L cs => .prec (lup L cs.1) (lup L cs.2))
    (Primrec₂.mk (Nat.Partrec.Code.primrec₂_prec.comp (hlup hL hcf) (hlup hL hcg)))
    (rf := fun L cf => .rfind' (lup L cf))
    (Primrec₂.mk (Nat.Partrec.Code.primrec_rfind'.comp (hlup fst snd)))

/-- Specializing oracle programs to ordinary Mathlib codes is primitive recursive. -/
theorem primrec_toPartrecCode : Primrec toPartrecCode := by
  open Primrec in
  have hstep : Primrec₂ fun (_ : Unit) (L : List Nat.Partrec.Code) => some (toPartrecCodeStep L) :=
    option_some.comp (primrec_toPartrecCodeStep.comp snd)
  have hrec : Primrec₂ fun (_ : Unit) n => (ofNat Code n).toPartrecCode := by
    refine nat_strong_rec (fun (_ : Unit) n => (ofNat Code n).toPartrecCode) hstep fun _ n => ?_
    set c := ofNat Code n
    have hn : n = encode c := (encode_ofNat n).symm
    cases hc : c with
    | zero | succ | left | right | oracle => simp [toPartrecCodeStep, hn, hc, toPartrecCode]
    | pair cf cg => simp [toPartrecCodeStep, hn, hc, toPartrecCode, encode_lt_pair]
    | comp cf cg => simp [toPartrecCodeStep, hn, hc, toPartrecCode, encode_lt_comp]
    | prec cf cg => simp [toPartrecCodeStep, hn, hc, toPartrecCode, encode_lt_prec]
    | rfind' cf => simp [toPartrecCodeStep, hn, hc, toPartrecCode, encode_lt_rfind']
  exact (hrec.comp (Primrec.const ()) (Primrec.encode_iff.2 Primrec.id)).of_eq fun c => by simp

end TauCeti.Oracle.Single.Code
