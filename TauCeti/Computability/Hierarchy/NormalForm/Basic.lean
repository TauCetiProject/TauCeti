/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.NormalForm.Prefix
public import TauCeti.Computability.Hierarchy.Totality
public import TauCeti.Computability.SingleOracle.Combinators
import TauCeti.Computability.Primrec.List
import TauCeti.Data.PFun.Basic

/-!
# Displayed arithmetical normal-form codes

A displayed normal-form code (`NormalFormCode`) pairs an alternating number-quantifier prefix
(`QuantifierPrefix`), a free-variable tuple arity `k`, and a single-oracle program (`Code`) for its
Boolean matrix. Its semantics evaluates the alternating quantifiers over the list of bound and free
variables, where `1` represents truth and `0` represents falsity.

Unlike the semantic pointclass predicates `IsSigma` and `IsPi`, a `NormalFormCode` is concrete
primitive-codable data that effective code transformations can manipulate directly, without
extracting programs from semantic existence proofs.

Validity (`NormalFormCode.IsValid Z nf`) is the semantic promise that the matrix program halts
with a Boolean output (`0` or `1`) relative to `Z` on every variable list of the expected length
`nf.quantifiers.depth + nf.arity`. Valid normal-form codes characterize the arithmetical
pointclasses `IsSigma` and `IsPi` on tuples `Fin k → ℕ` and on arbitrary primitive-codable types.
Conversely, `NormalFormCode.IsValid Z` is itself Π⁰₂-complete relative to `Z` under ordinary
computable one-one reductions, so validity is neither Σ⁰₂, computably enumerable, nor decidable.

## Main definitions

* `TauCeti.ArithmeticalHierarchy.NormalFormCode`: a displayed normal-form code consisting of a
  quantifier prefix, a tuple arity, and a matrix program.
* `TauCeti.ArithmeticalHierarchy.NormalFormCode.IsValid`: semantic totality and Boolean-valuedness
  of the matrix on lists of length `quantifiers.depth + arity`.
* `TauCeti.ArithmeticalHierarchy.NormalFormCode.Holds`: the `k`-ary predicate defined by a
  normal-form code relative to an oracle `Z`.

## Main results

* `TauCeti.ArithmeticalHierarchy.NormalFormCode.IsValid.isClass_holds`: soundness of valid
  normal-form codes.
* `TauCeti.ArithmeticalHierarchy.isClass_iff_exists_normalFormCode`: completeness for predicates
  on `Fin k → ℕ`, together with `isSigma_iff_exists_normalFormCode`,
  `isPi_iff_exists_normalFormCode`, and `isClass_iff_exists_normalFormCode_unary`.
* `TauCeti.ArithmeticalHierarchy.isPi_two_isValid`,
  `TauCeti.ArithmeticalHierarchy.oneOneReducible_totality_isValid`,
  `TauCeti.ArithmeticalHierarchy.not_isSigma_two_isValid`,
  `TauCeti.ArithmeticalHierarchy.not_computablePred_isValid`: exact Π⁰₂-completeness and
  undecidability of `NormalFormCode.IsValid Z`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters IV.1 and IV.3.
-/

public section

open Encodable Denumerable TauCeti.Oracle.Single

namespace TauCeti.ArithmeticalHierarchy

/-! ### Displayed normal-form codes -/

/-- A displayed arithmetical normal-form code: an alternating number-quantifier prefix, a free
variable arity `arity`, and a single-oracle program `matrix` intended to compute a Boolean value
(`0` for `false`, `1` for `true`) on encoded variable lists `bs ++ xs` of length
`quantifiers.depth + arity`. -/
@[ext]
structure NormalFormCode : Type where
  /-- The alternating number-quantifier prefix. -/
  quantifiers : QuantifierPrefix
  /-- The number of free numerical variables. -/
  arity : ℕ
  /-- The single-oracle program computing the Boolean matrix on encoded lists of variables. -/
  matrix : Code
  deriving DecidableEq

namespace NormalFormCode

/-- Equivalence between `NormalFormCode` and `QuantifierPrefix × ℕ × Code`. -/
def equivProd : NormalFormCode ≃ QuantifierPrefix × ℕ × Code where
  toFun nf := (nf.quantifiers, nf.arity, nf.matrix)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Normal-form codes are primitive-codable as triples of prefix, arity, and matrix program. -/
instance : Primcodable NormalFormCode :=
  Primcodable.ofEquiv (QuantifierPrefix × ℕ × Code) equivProd

/-- `equivProd` on a normal-form code. -/
@[simp]
theorem equivProd_apply (nf : NormalFormCode) :
    equivProd nf = (nf.quantifiers, nf.arity, nf.matrix) := (rfl)

/-- `equivProd.symm` on a triple. -/
@[simp]
theorem equivProd_symm_apply (p : QuantifierPrefix × ℕ × Code) :
    equivProd.symm p = ⟨p.1, p.2.1, p.2.2⟩ := (rfl)

/-- Projecting the quantifier prefix is primitive recursive. -/
theorem primrec_quantifiers : Primrec quantifiers :=
  (Primrec.fst.comp (Primrec.of_equiv (e := equivProd))).of_eq fun _ => rfl

/-- Projecting the tuple arity is primitive recursive. -/
theorem primrec_arity : Primrec arity :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := equivProd)))).of_eq fun _ => rfl

/-- Projecting the matrix program is primitive recursive. -/
theorem primrec_matrix : Primrec matrix :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := equivProd)))).of_eq fun _ => rfl

/-- Constructing a normal-form code from its prefix, arity, and matrix program is primitive
recursive. -/
theorem primrec_mk : Primrec fun p : QuantifierPrefix × ℕ × Code =>
    NormalFormCode.mk p.1 p.2.1 p.2.2 :=
  (Primrec.of_equiv_symm (e := equivProd)).of_eq fun _ => rfl

/-- The matrix of `nf` accepts variable list `l` relative to `Z` when `nf.matrix` evaluates to
`1` (`encode true`) on `encode l`. -/
def MatrixHolds (Z : Set ℕ) (nf : NormalFormCode) (l : List ℕ) : Prop :=
  1 ∈ Code.eval Z.oracle nf.matrix (encode l)

/-- Evaluation of a normal-form code on an explicit list of free variables relative to `Z`. -/
def EvalList (Z : Set ℕ) (nf : NormalFormCode) (xs : List ℕ) : Prop :=
  nf.quantifiers.Eval (nf.MatrixHolds Z) xs

/-- The `nf.arity`-ary predicate on tuples `Fin nf.arity → ℕ` defined by `nf` relative to `Z`. -/
def Holds (Z : Set ℕ) (nf : NormalFormCode) (x : Fin nf.arity → ℕ) : Prop :=
  nf.EvalList Z (List.ofFn x)

/-- Semantic validity of a normal-form code relative to `Z`: on every variable list of length
`nf.quantifiers.depth + nf.arity`, the matrix program halts with a Boolean value (`0` or `1`). -/
def IsValid (Z : Set ℕ) (nf : NormalFormCode) : Prop :=
  ∀ l : List ℕ, l.length = nf.quantifiers.depth + nf.arity →
    ∃ b : Bool, encode b ∈ Code.eval Z.oracle nf.matrix (encode l)

/-- Definition of `MatrixHolds` unfolded. -/
theorem matrixHolds_iff {Z : Set ℕ} {nf : NormalFormCode} {l : List ℕ} :
    nf.MatrixHolds Z l ↔ 1 ∈ Code.eval Z.oracle nf.matrix (encode l) := (Iff.rfl)

/-- Definition of `EvalList` unfolded. -/
theorem evalList_iff {Z : Set ℕ} {nf : NormalFormCode} {xs : List ℕ} :
    nf.EvalList Z xs ↔ nf.quantifiers.Eval (nf.MatrixHolds Z) xs := (Iff.rfl)

/-- Definition of `Holds` in terms of `EvalList`. -/
theorem holds_iff {Z : Set ℕ} {nf : NormalFormCode} {x : Fin nf.arity → ℕ} :
    nf.Holds Z x ↔ nf.EvalList Z (List.ofFn x) := (Iff.rfl)

/-- Definition of `IsValid` unfolded. -/
theorem isValid_iff {Z : Set ℕ} {nf : NormalFormCode} :
    nf.IsValid Z ↔ ∀ l : List ℕ, l.length = nf.quantifiers.depth + nf.arity →
      ∃ b : Bool, encode b ∈ Code.eval Z.oracle nf.matrix (encode l) := (Iff.rfl)

/-- For a valid normal-form code and a list of the expected length, the matrix program halts with
output `0` exactly when `MatrixHolds` fails. -/
theorem IsValid.zero_mem_eval_iff {Z : Set ℕ} {nf : NormalFormCode} (h : nf.IsValid Z)
    {l : List ℕ} (hl : l.length = nf.quantifiers.depth + nf.arity) :
    0 ∈ Code.eval Z.oracle nf.matrix (encode l) ↔ ¬nf.MatrixHolds Z l := by
  obtain ⟨b, hb⟩ := h l hl
  cases b with
  | false =>
    simp only [encode_false] at hb
    refine ⟨fun _ h1 => ?_, fun _ => hb⟩
    exact Nat.zero_ne_one (Part.mem_unique hb h1)
  | true =>
    simp only [encode_true] at hb
    refine ⟨fun h0 _ => ?_, fun hn => (hn hb).elim⟩
    exact Nat.zero_ne_one (Part.mem_unique h0 hb)

/-- A valid constant-false normal-form code of any quantifier prefix and arity. -/
def falseCode (p : QuantifierPrefix) (k : ℕ) : NormalFormCode :=
  ⟨p, k, Code.zero⟩

/-- The quantifier prefix of `falseCode p k` is `p`. -/
@[simp]
theorem quantifiers_falseCode (p : QuantifierPrefix) (k : ℕ) :
    (falseCode p k).quantifiers = p := (rfl)

/-- The arity of `falseCode p k` is `k`. -/
@[simp]
theorem arity_falseCode (p : QuantifierPrefix) (k : ℕ) :
    (falseCode p k).arity = k := (rfl)

/-- The matrix program of `falseCode p k` is `Code.zero`. -/
@[simp]
theorem matrix_falseCode (p : QuantifierPrefix) (k : ℕ) :
    (falseCode p k).matrix = Code.zero := (rfl)

/-- The matrix of `falseCode` never holds. -/
@[simp]
theorem matrixHolds_falseCode (Z : Set ℕ) (p : QuantifierPrefix) (k : ℕ) (l : List ℕ) :
    ¬(falseCode p k).MatrixHolds Z l := by
  simp [MatrixHolds]

/-- `falseCode` is valid relative to every oracle. -/
theorem isValid_falseCode (Z : Set ℕ) (p : QuantifierPrefix) (k : ℕ) :
    (falseCode p k).IsValid Z := fun _ _ => ⟨false, by simp [falseCode]⟩

/-- `falseCode` defines the identically false predicate on lists. -/
@[simp]
theorem evalList_falseCode (Z : Set ℕ) (p : QuantifierPrefix) (k : ℕ) (xs : List ℕ) :
    ¬(falseCode p k).EvalList Z xs := by
  have h : (falseCode p k).EvalList Z xs ↔ p.Eval (fun _ => False) xs :=
    QuantifierPrefix.eval_congr fun l => by
      simp [MatrixHolds, falseCode]
  rw [h]
  simp

/-- `falseCode` defines the identically false tuple predicate. -/
@[simp]
theorem holds_falseCode (Z : Set ℕ) (p : QuantifierPrefix) (k : ℕ)
    (x : Fin (falseCode p k).arity → ℕ) :
    ¬(falseCode p k).Holds Z x :=
  evalList_falseCode Z p k (List.ofFn x)

end NormalFormCode

/-! ### Soundness and completeness with respect to arithmetical pointclasses -/

-- Soundness for a quantifier-free matrix on `Fin k → ℕ`.
private theorem isSigma_zero_matrix {Z : Set ℕ} {k : ℕ} {c : Code}
    (hc : ∀ l : List ℕ, l.length = k → ∃ b : Bool, encode b ∈ Code.eval Z.oracle c (encode l)) :
    IsSigma Z 0 (fun x : Fin k → ℕ => 1 ∈ Code.eval Z.oracle c (encode (List.ofFn x))) := by
  have htot : ∀ x : Fin k → ℕ, ∃ b : Bool, encode b ∈ Code.eval Z.oracle c (encode (List.ofFn x)) :=
    fun x => hc (List.ofFn x) List.length_ofFn
  let b : (Fin k → ℕ) → Bool := fun x => (htot x).choose
  have hb_mem : ∀ x, encode (b x) ∈ Code.eval Z.oracle c (encode (List.ofFn x)) :=
    fun x => (htot x).choose_spec
  have hcomp : ComputableIn {Z.oracle} b := by
    have harg : ComputableIn {Z.oracle} (fun x : Fin k → ℕ => encode (List.ofFn x)) :=
      (Primrec.encode.comp Primrec.list_ofFn').computableIn
    unfold ComputableIn RecursiveIn at harg ⊢
    refine ((Code.recursiveIn_eval Z.oracle c).comp harg).of_eq fun n => ?_
    cases @decode (Fin k → ℕ) Primcodable.toEncodable n with
    | none =>
      simp only [Part.coe_none, Part.bind_none]
      exact Part.bind_none fun m => Code.eval Z.oracle c m
    | some x =>
      simp only [Part.coe_some, Part.bind_some, Part.map_some, encode_nat, PFun.some_bind]
      exact Part.eq_some_iff.2 (hb_mem x)
  refine isSigma_zero_iff.2 ⟨b, hcomp, fun x => ?_⟩
  have hx := Part.eq_some_iff.2 (hb_mem x)
  rw [hx, Part.mem_some_iff]
  cases b x <;> simp

-- Soundness by structural induction on the quantifier prefix.
private theorem isClass_eval_of_valid {Z : Set ℕ} {p : QuantifierPrefix} {k : ℕ} {c : Code}
    (hc : ∀ l : List ℕ, l.length = p.depth + k →
      ∃ b : Bool, encode b ∈ Code.eval Z.oracle c (encode l)) :
    p.IsClass Z (fun x : Fin k → ℕ =>
      p.Eval (fun l => 1 ∈ Code.eval Z.oracle c (encode l)) (List.ofFn x)) := by
  induction p using QuantifierPrefix.eval_induction generalizing k with
  | zero =>
    rw [QuantifierPrefix.isClass_zero]
    have h0 := isSigma_zero_matrix (Z := Z) (k := k) (c := c) (fun l hl => hc l (by simp [hl]))
    exact h0.of_eq fun x => by simp
  | sigma_zero =>
    rw [QuantifierPrefix.isClass_sigma]
    have h0 := isSigma_zero_matrix (Z := Z) (k := k + 1) (c := c)
      (fun l hl => hc l (by simp [Nat.add_comm, hl]))
    refine isSigma_succ_iff.2 ⟨_, isPi_zero_iff.2
      (h0.preimage (Primrec.fin_cons.comp Primrec.snd Primrec.fst).computableIn), fun x => ?_⟩
    simp [List.ofFn_succ]
  | pi_zero =>
    rw [QuantifierPrefix.isClass_pi]
    have h0 := isSigma_zero_matrix (Z := Z) (k := k + 1) (c := c)
      (fun l hl => hc l (by simp [Nat.add_comm, hl]))
    refine isPi_succ_iff.2 ⟨_,
      h0.preimage (Primrec.fin_cons.comp Primrec.snd Primrec.fst).computableIn, fun x => ?_⟩
    simp [List.ofFn_succ]
  | sigma_succ n ih =>
    rw [QuantifierPrefix.isClass_sigma]
    have hprev : IsPi Z (n + 1) (fun v : Fin (k + 1) → ℕ =>
        QuantifierPrefix.Eval (.pi n) (fun l => 1 ∈ Code.eval Z.oracle c (encode l))
          (List.ofFn v)) := by
      rw [← QuantifierPrefix.isClass_pi]
      refine ih (k := k + 1) fun l hl => hc l ?_
      simp only [QuantifierPrefix.depth_sigma, QuantifierPrefix.depth_pi] at hl ⊢
      omega
    refine isSigma_succ_iff.2 ⟨_,
      hprev.preimage (Primrec.fin_cons.comp Primrec.snd Primrec.fst).computableIn, fun x => ?_⟩
    simp [List.ofFn_succ]
  | pi_succ n ih =>
    rw [QuantifierPrefix.isClass_pi]
    have hprev : IsSigma Z (n + 1) (fun v : Fin (k + 1) → ℕ =>
        QuantifierPrefix.Eval (.sigma n) (fun l => 1 ∈ Code.eval Z.oracle c (encode l))
          (List.ofFn v)) := by
      rw [← QuantifierPrefix.isClass_sigma]
      refine ih (k := k + 1) fun l hl => hc l ?_
      simp only [QuantifierPrefix.depth_sigma, QuantifierPrefix.depth_pi] at hl ⊢
      omega
    refine isPi_succ_iff.2 ⟨_,
      hprev.preimage (Primrec.fin_cons.comp Primrec.snd Primrec.fst).computableIn, fun x => ?_⟩
    simp [List.ofFn_succ]

/-- **Soundness of displayed normal-form codes.** A valid normal-form code relative to `Z` defines
a predicate in the arithmetical pointclass named by its quantifier prefix. -/
theorem NormalFormCode.IsValid.isClass_holds {Z : Set ℕ} {nf : NormalFormCode}
    (h : nf.IsValid Z) : nf.quantifiers.IsClass Z (nf.Holds Z) :=
  isClass_eval_of_valid h

-- Completeness at quantifier depth zero: extract a matrix program from a `Z`-computable Boolean.
private theorem exists_code_of_isSigma_zero {Z : Set ℕ} {k : ℕ}
    {P : (Fin k → ℕ) → Prop} (hP : IsSigma Z 0 P) :
    ∃ c : Code,
      (∀ l : List ℕ, l.length = k →
        ∃ b : Bool, encode b ∈ Code.eval Z.oracle c (encode l)) ∧
      ∀ x : Fin k → ℕ, (1 ∈ Code.eval Z.oracle c (encode (List.ofFn x))) ↔ P x := by
  obtain ⟨b, hb, heq⟩ := isSigma_zero_iff.1 hP
  have hbl : ComputableIn {Z.oracle} (fun l : List ℕ => b (fun i : Fin k => l.getD i 0)) :=
    hb.comp (Primrec.list_getD_fin.comp Primrec.id (Primrec.const 0)).computableIn
  unfold ComputableIn RecursiveIn at hbl
  obtain ⟨c, hc⟩ := Code.exists_code.1 hbl
  have hce : ∀ l : List ℕ,
      Code.eval Z.oracle c (encode l) = Part.some (encode (b (fun i : Fin k => l.getD i 0))) := by
    intro l
    rw [hc]
    simp
  refine ⟨c, fun l _ => ⟨b (fun i : Fin k => l.getD i 0), by rw [hce]; exact Part.mem_some _⟩,
    fun x => ?_⟩
  have hx : (fun i : Fin k => (List.ofFn x).getD i 0) = x := by
    funext i
    simp [List.getD_eq_getElem?_getD]
  rw [hce, hx, Part.mem_some_iff, ← heq x]
  cases b x <;> simp

-- Completeness by structural induction on the quantifier prefix.
private theorem exists_code_of_isClass {Z : Set ℕ} {p : QuantifierPrefix} {k : ℕ}
    {P : (Fin k → ℕ) → Prop} (hP : p.IsClass Z P) :
    ∃ c : Code,
      (∀ l : List ℕ, l.length = p.depth + k →
        ∃ b : Bool, encode b ∈ Code.eval Z.oracle c (encode l)) ∧
      ∀ x : Fin k → ℕ,
        p.Eval (fun l => 1 ∈ Code.eval Z.oracle c (encode l)) (List.ofFn x) ↔ P x := by
  induction p using QuantifierPrefix.eval_induction generalizing k with
  | zero =>
    obtain ⟨c, hval, hsem⟩ := exists_code_of_isSigma_zero (QuantifierPrefix.isClass_zero.1 hP)
    exact ⟨c, fun l hl => hval l (by simpa using hl), fun x => by simpa using hsem x⟩
  | sigma_zero =>
    obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 (QuantifierPrefix.isClass_sigma.1 hP)
    obtain ⟨c, hval, hsem⟩ := exists_code_of_isSigma_zero ((isPi_zero_iff.1 hq).preimage
      (Primrec.fin_tail.pair (Primrec.fin_app.comp Primrec.id (Primrec.const 0))).computableIn)
    refine ⟨c, fun l hl => hval l (by simp at hl ⊢; omega), fun x => ?_⟩
    simp only [QuantifierPrefix.eval_sigma_zero, heq]
    exact exists_congr fun y => by simpa [List.ofFn_succ] using hsem (Fin.cons y x)
  | pi_zero =>
    obtain ⟨q, hq, heq⟩ := isPi_succ_iff.1 (QuantifierPrefix.isClass_pi.1 hP)
    obtain ⟨c, hval, hsem⟩ := exists_code_of_isSigma_zero (hq.preimage
      (Primrec.fin_tail.pair (Primrec.fin_app.comp Primrec.id (Primrec.const 0))).computableIn)
    refine ⟨c, fun l hl => hval l (by simp at hl ⊢; omega), fun x => ?_⟩
    simp only [QuantifierPrefix.eval_pi_zero, heq]
    exact forall_congr' fun y => by simpa [List.ofFn_succ] using hsem (Fin.cons y x)
  | sigma_succ n ih =>
    obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 (QuantifierPrefix.isClass_sigma.1 hP)
    obtain ⟨c, hval, hsem⟩ := ih (QuantifierPrefix.isClass_pi.2 (hq.preimage
      (Primrec.fin_tail.pair (Primrec.fin_app.comp Primrec.id (Primrec.const 0))).computableIn))
    refine ⟨c, fun l hl => hval l (by simp at hl ⊢; omega), fun x => ?_⟩
    simp only [QuantifierPrefix.eval_sigma_succ, heq]
    exact exists_congr fun y => by simpa [List.ofFn_succ] using hsem (Fin.cons y x)
  | pi_succ n ih =>
    obtain ⟨q, hq, heq⟩ := isPi_succ_iff.1 (QuantifierPrefix.isClass_pi.1 hP)
    obtain ⟨c, hval, hsem⟩ := ih (QuantifierPrefix.isClass_sigma.2 (hq.preimage
      (Primrec.fin_tail.pair (Primrec.fin_app.comp Primrec.id (Primrec.const 0))).computableIn))
    refine ⟨c, fun l hl => hval l (by simp at hl ⊢; omega), fun x => ?_⟩
    simp only [QuantifierPrefix.eval_pi_succ, heq]
    exact forall_congr' fun y => by simpa [List.ofFn_succ] using hsem (Fin.cons y x)

/-- **Normal-form representation theorem for tuple predicates.** A predicate on `Fin k → ℕ` belongs
to the pointclass `p.IsClass Z` if and only if it is realized by a valid `NormalFormCode` with
prefix `p` and arity `k`. -/
theorem isClass_iff_exists_normalFormCode {Z : Set ℕ} {p : QuantifierPrefix} {k : ℕ}
    {P : (Fin k → ℕ) → Prop} :
    p.IsClass Z P ↔
      ∃ nf : NormalFormCode, nf.quantifiers = p ∧ nf.arity = k ∧ nf.IsValid Z ∧
        ∀ x : Fin k → ℕ, nf.EvalList Z (List.ofFn x) ↔ P x := by
  constructor
  · intro hP
    obtain ⟨c, hval, hsem⟩ := exists_code_of_isClass hP
    exact ⟨⟨p, k, c⟩, rfl, rfl, hval, hsem⟩
  · rintro ⟨nf, rfl, rfl, hval, hsem⟩
    exact hval.isClass_holds.of_eq hsem

/-- A `k`-ary predicate is Σ⁰ₙ relative to `Z` if and only if it is defined by a valid displayed
normal-form code with prefix `QuantifierPrefix.ofSigma n` and arity `k`. -/
theorem isSigma_iff_exists_normalFormCode {Z : Set ℕ} {n k : ℕ} {P : (Fin k → ℕ) → Prop} :
    IsSigma Z n P ↔
      ∃ nf : NormalFormCode, nf.quantifiers = QuantifierPrefix.ofSigma n ∧ nf.arity = k ∧
        nf.IsValid Z ∧ ∀ x : Fin k → ℕ, nf.EvalList Z (List.ofFn x) ↔ P x := by
  rw [← QuantifierPrefix.isClass_ofSigma]
  exact isClass_iff_exists_normalFormCode

/-- A `k`-ary predicate is Π⁰ₙ relative to `Z` if and only if it is defined by a valid displayed
normal-form code with prefix `QuantifierPrefix.ofPi n` and arity `k`. -/
theorem isPi_iff_exists_normalFormCode {Z : Set ℕ} {n k : ℕ} {P : (Fin k → ℕ) → Prop} :
    IsPi Z n P ↔
      ∃ nf : NormalFormCode, nf.quantifiers = QuantifierPrefix.ofPi n ∧ nf.arity = k ∧
        nf.IsValid Z ∧ ∀ x : Fin k → ℕ, nf.EvalList Z (List.ofFn x) ↔ P x := by
  rw [← QuantifierPrefix.isClass_ofPi]
  exact isClass_iff_exists_normalFormCode

/-- A predicate on any primitive-codable type `α` belongs to `p.IsClass Z` if and only if it is
defined on singleton encoded inputs `[encode x]` by a valid unary normal-form code of prefix `p`. -/
theorem isClass_iff_exists_normalFormCode_unary {Z : Set ℕ} {p : QuantifierPrefix}
    {α : Type*} [Primcodable α] {P : α → Prop} :
    p.IsClass Z P ↔
      ∃ nf : NormalFormCode, nf.quantifiers = p ∧ nf.arity = 1 ∧ nf.IsValid Z ∧
        ∀ x : α, nf.EvalList Z [encode x] ↔ P x := by
  constructor
  · intro hP
    rcases isEmpty_or_nonempty α with hempty | hne
    · refine ⟨NormalFormCode.falseCode p 1, rfl, rfl,
        NormalFormCode.isValid_falseCode Z p 1, fun x => (hempty.false x).elim⟩
    · obtain ⟨a₀⟩ := hne
      have hdec : Primrec fun v : Fin 1 → ℕ => (decode (α := α) (v 0)).getD a₀ := by
        refine (Primrec.option_casesOn
          (Primrec.decode.comp (Primrec.fin_app.comp Primrec.id (Primrec.const 0)))
          (Primrec.const a₀) Primrec.snd.to₂).of_eq fun v => ?_
        cases e : decode (α := α) (v 0) <;> simp [e]
      have hP' : p.IsClass Z (fun v : Fin 1 → ℕ => P ((decode (α := α) (v 0)).getD a₀)) :=
        hP.preimage hdec.computableIn
      obtain ⟨nf, hq, ha, hval, hsem⟩ := isClass_iff_exists_normalFormCode.1 hP'
      refine ⟨nf, hq, ha, hval, fun x => ?_⟩
      simpa [List.ofFn_succ, encodek] using hsem (fun _ => encode x)
  · rintro ⟨⟨q, a, m⟩, rfl, ha, hval, hsem⟩
    dsimp only at ha hval hsem ⊢
    subst ha
    have hfun : Primrec fun x : α => (fun _ : Fin 1 => encode x) :=
      Primrec.fin_curry.2 (Primrec.encode.comp Primrec.fst)
    have hclass := hval.isClass_holds.preimage hfun.computableIn
    refine hclass.of_eq fun x => ?_
    simpa [NormalFormCode.Holds, List.ofFn_succ] using hsem x

/-! ### Exact Π⁰₂-completeness and undecidability of `NormalFormCode.IsValid` -/

-- Halting with a Boolean output (`0` or `1`) on a coded input is Σ⁰₁ relative to `Z`.
private theorem isSigma_one_eval_bool {Z : Set ℕ} :
    IsSigma Z 1 (fun p : NormalFormCode × ℕ =>
      ∃ b : Bool, encode b ∈ Code.eval Z.oracle p.1.matrix p.2) := by
  obtain ⟨guard, hguard⟩ := Code.exists_boolGuardCode
  have harg : Primrec fun p : NormalFormCode × ℕ =>
      Nat.pair (encode (Code.comp guard p.1.matrix)) p.2 :=
    Primrec₂.natPair.comp
      (Primrec.encode.comp (Code.primrec₂_comp.comp (Primrec.const guard)
        (NormalFormCode.primrec_matrix.comp Primrec.fst)))
      Primrec.snd
  have hdom := (isSigma_one_dom_eval (Z := Z) Code.universal).preimage harg.computableIn
  refine hdom.of_eq fun p => ?_
  have hZ : Z.oracle = ((Z.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) := funext fun n => by simp
  rw [hZ, Code.eval_universal, ← hZ, ofNat_encode, Code.eval_comp]
  have hbind : ∀ y : ℕ,
      y ∈ (Code.eval Z.oracle p.1.matrix p.2 >>= Code.eval Z.oracle guard) ↔
        ∃ m ∈ Code.eval Z.oracle p.1.matrix p.2, m < 2 ∧ y = 0 := fun y => by
    refine Part.mem_bind_iff.trans ?_
    simp [hguard]
  simp only [Part.dom_iff_mem, hbind]
  constructor
  · rintro ⟨_, m, hm, hlt, _⟩
    match m, hlt with
    | 0, _ => exact ⟨false, hm⟩
    | 1, _ => exact ⟨true, hm⟩
  · rintro ⟨b, hb⟩
    exact ⟨0, encode b, hb, by cases b <;> decide, rfl⟩

/-- Validity of normal-form codes is Π⁰₂ relative to the oracle. -/
theorem isPi_two_isValid {Z : Set ℕ} : IsPi Z 2 (NormalFormCode.IsValid Z) := by
  have hlen : IsSigma Z 1 (fun p : NormalFormCode × ℕ =>
      (ofNat (List ℕ) p.2).length ≠ p.1.quantifiers.depth + p.1.arity) := by
    have hpred : PrimrecPred fun p : NormalFormCode × ℕ =>
        (ofNat (List ℕ) p.2).length ≠ p.1.quantifiers.depth + p.1.arity :=
      (Primrec.eq.comp
        (Primrec.list_length.comp ((Primrec.ofNat (List ℕ)).comp Primrec.snd))
        (Primrec.nat_add.comp (QuantifierPrefix.primrec_depth.comp
            (NormalFormCode.primrec_quantifiers.comp Primrec.fst))
          (NormalFormCode.primrec_arity.comp Primrec.fst))).not
    obtain ⟨_, hdec⟩ := hpred
    exact (isSigma_zero_iff.2 ⟨_, hdec.computableIn, fun _ => by simp⟩).one_of_zero
  refine isPi_succ_iff.2 ⟨_, hlen.or isSigma_one_eval_bool, fun nf => ?_⟩
  constructor
  · intro h n
    by_cases hl : (ofNat (List ℕ) n).length = nf.quantifiers.depth + nf.arity
    · exact Or.inr (by simpa only [encode_ofNat] using h (ofNat (List ℕ) n) hl)
    · exact Or.inl hl
  · intro h l hl
    rcases h (encode l) with hne | hb
    · simp only [ofNat_encode] at hne
      exact (hne hl).elim
    · exact hb

/-- Relative totality reduces one-one to normal-form validity by a primitive recursive map,
uniformly for every oracle `Z`. -/
theorem oneOneReducible_totality_isValid {Z : Set ℕ} :
    OneOneReducible (· ∈ totality Z) (NormalFormCode.IsValid Z) := by
  obtain ⟨headCode, hhead⟩ := Code.exists_listHeadCode
  let f : ℕ → NormalFormCode := fun e =>
    ⟨.zero, 1, Code.comp Code.zero (Code.comp (ofNat Code e) headCode)⟩
  have hf : Primrec f :=
    NormalFormCode.primrec_mk.comp
      ((Primrec.const .zero).pair ((Primrec.const 1).pair
        (Code.primrec₂_comp.comp (Primrec.const Code.zero)
          (Code.primrec₂_comp.comp (Primrec.ofNat Code) (Primrec.const headCode)))))
  refine ⟨f, hf.to_comp, fun e₁ e₂ h => ?_, fun e => ?_⟩
  · have hmat : Code.comp Code.zero (Code.comp (ofNat Code e₁) headCode) =
        Code.comp Code.zero (Code.comp (ofNat Code e₂) headCode) :=
      congrArg NormalFormCode.matrix h
    simp only [Code.comp.injEq] at hmat
    rw [← @encode_ofNat Code _ e₁, ← @encode_ofNat Code _ e₂, hmat.2.1]
  · simp only [mem_totality, NormalFormCode.IsValid, f, QuantifierPrefix.depth_zero, Nat.zero_add]
    have hmem : ∀ (x z : ℕ),
        z ∈ Code.eval Z.oracle (Code.comp Code.zero (Code.comp (ofNat Code e) headCode))
          (encode [x]) ↔ (Code.eval Z.oracle (ofNat Code e) x).Dom ∧ z = 0 := fun x z => by
      simp only [Code.eval_comp, hhead, ofNat_encode, List.headI_cons, PFun.some_bind]
      refine Part.mem_bind_iff.trans ?_
      simp [Part.dom_iff_mem]
    constructor
    · intro h l hl
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hl
      exact ⟨false, (hmem x 0).2 ⟨h x, rfl⟩⟩
    · intro h x
      obtain ⟨b, hb⟩ := h [x] rfl
      exact ((hmem x (encode b)).1 hb).1

/-- Every Π⁰₂ predicate relative to `Z` one-one reduces to `NormalFormCode.IsValid Z` by an
ordinary computable function. -/
theorem IsPi.oneOneReducible_isValid {Z : Set ℕ} {α : Type*} [Primcodable α] {p : α → Prop}
    (hp : IsPi Z 2 p) : OneOneReducible p (NormalFormCode.IsValid Z) :=
  hp.oneOneReducible_totality.trans oneOneReducible_totality_isValid

/-- A predicate is Π⁰₂ relative to `Z` if and only if it one-one reduces to normal-form validity
relative to `Z`. -/
theorem isPi_two_iff_oneOneReducible_isValid {Z : Set ℕ} {α : Type*} [Primcodable α]
    {p : α → Prop} : IsPi Z 2 p ↔ OneOneReducible p (NormalFormCode.IsValid Z) := by
  refine ⟨IsPi.oneOneReducible_isValid, fun ⟨f, hf, _, heq⟩ => ?_⟩
  exact (isPi_two_isValid.preimage hf.computableIn).of_eq fun x => (heq x).symm

/-- Normal-form validity is not Σ⁰₂ relative to its oracle. -/
theorem not_isSigma_two_isValid {Z : Set ℕ} : ¬IsSigma Z 2 (NormalFormCode.IsValid Z) := by
  intro h
  obtain ⟨f, hf, _, heq⟩ := oneOneReducible_totality_isValid (Z := Z)
  exact not_isSigma_two_totality ((h.preimage hf.computableIn).of_eq fun e => (heq e).symm)

/-- Normal-form validity relative to any oracle is not computably enumerable. -/
theorem not_rePred_isValid {Z : Set ℕ} : ¬REPred (NormalFormCode.IsValid Z) := by
  intro h
  obtain ⟨f, hf, _, heq⟩ := oneOneReducible_totality_isValid (Z := Z)
  have hre : REPred fun e => NormalFormCode.IsValid Z (f e) := h.comp hf
  have htot : (· ∈ totality Z) = fun e => NormalFormCode.IsValid Z (f e) :=
    funext fun e => propext (heq e)
  exact not_rePred_mem_totality (htot ▸ hre)

/-- Normal-form validity relative to any oracle is undecidable. -/
theorem not_computablePred_isValid {Z : Set ℕ} : ¬ComputablePred (NormalFormCode.IsValid Z) :=
  fun h => not_rePred_isValid h.to_re

end TauCeti.ArithmeticalHierarchy
