/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.NormalForm.Basic
import TauCeti.Data.PFun.Basic

/-!
# Effective Boolean transformations of arithmetical normal-form codes

This file implements primitive recursive, oracle-independent Boolean connectives on displayed
arithmetical normal forms (`NormalFormCode`):

* `NormalFormCode.neg`: complementation, dualizing the quantifier prefix and negating the matrix.
* `NormalFormCode.and` and `NormalFormCode.or`: finite conjunction and disjunction at a common
  quantifier prefix and arity, unpairing all bound variables simultaneously and returning `none`
  when the operands' quantifier prefixes or arities differ.

Every transformation is proved primitive recursive on `NormalFormCode` without depending on the
oracle. For valid operands — and, in the case of `and` and `or`, when the operation succeeds
(`= some nf`, meaning the operands have matching quantifier prefixes and arities) — each
transformation preserves semantic validity (`NormalFormCode.IsValid Z`) and satisfies its exact
semantic equation relative to every oracle `Z` (on tuples of the declared arity and on variable
lists of that length).

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV.1.
-/

public section

open Encodable Denumerable TauCeti.Oracle.Single

namespace TauCeti.ArithmeticalHierarchy

namespace NormalFormCode

/-! ### Complementation -/

/-- Effective complementation of a normal-form code, dualizing the quantifier prefix and negating
the Boolean matrix. -/
def neg (nf : NormalFormCode) : NormalFormCode :=
  ⟨nf.quantifiers.dual, nf.arity, Code.boolNot nf.matrix⟩

/-- Complementation dualizes the quantifier prefix. -/
@[simp]
theorem quantifiers_neg (nf : NormalFormCode) : nf.neg.quantifiers = nf.quantifiers.dual := (rfl)

/-- Complementation preserves the free-variable arity. -/
@[simp]
theorem arity_neg (nf : NormalFormCode) : nf.neg.arity = nf.arity := (rfl)

/-- Complementation negates the matrix program via `Code.boolNot`. -/
@[simp]
theorem matrix_neg (nf : NormalFormCode) : nf.neg.matrix = Code.boolNot nf.matrix := (rfl)

/-- Complementation is primitive recursive on normal-form codes. -/
theorem primrec_neg : Primrec neg :=
  primrec_mk.comp
    ((QuantifierPrefix.primrec_dual.comp primrec_quantifiers).pair
      (primrec_arity.pair (Code.primrec_boolNot.comp primrec_matrix)))

/-- Complementation preserves validity relative to every oracle. -/
theorem IsValid.neg {Z : Set ℕ} {nf : NormalFormCode} (h : nf.IsValid Z) : nf.neg.IsValid Z := by
  refine isValid_iff.2 fun l hl => ?_
  have hl' : l.length = nf.quantifiers.depth + nf.arity := by
    simpa [quantifiers_neg, arity_neg] using hl
  obtain ⟨b, hb⟩ := isValid_iff.1 h l hl'
  refine ⟨!b, ?_⟩
  rw [NormalFormCode.neg, Code.eval_boolNot Z.oracle nf.matrix (encode l) b hb]
  exact Part.mem_some _

/-- Matrix semantics for complementation on variable lists of the expected length. -/
theorem IsValid.matrixHolds_neg {Z : Set ℕ} {nf : NormalFormCode} (h : nf.IsValid Z)
    {l : List ℕ} (hl : l.length = nf.quantifiers.depth + nf.arity) :
    nf.neg.MatrixHolds Z l ↔ ¬nf.MatrixHolds Z l := by
  obtain ⟨b, hb⟩ := isValid_iff.1 h l hl
  have hnot := Code.eval_boolNot Z.oracle nf.matrix (encode l) b hb
  have hmat := Part.eq_some_iff.2 hb
  rw [matrixHolds_iff, matrixHolds_iff]
  simp only [matrix_neg, hnot, hmat, Part.mem_some_iff]
  cases b <;> simp

/-- Semantic equation for complementation on lists of the expected arity. -/
theorem evalList_neg {Z : Set ℕ} {nf : NormalFormCode} (h : nf.IsValid Z)
    {xs : List ℕ} (hxs : xs.length = nf.arity) :
    nf.neg.EvalList Z xs ↔ ¬nf.EvalList Z xs := by
  rw [evalList_iff, evalList_iff, QuantifierPrefix.not_eval_iff, quantifiers_neg]
  exact QuantifierPrefix.eval_congr_append fun bs hbs =>
    h.matrixHolds_neg (by simp [hbs, hxs])

/-- Semantic equation for complementation on tuples. -/
theorem holds_neg {Z : Set ℕ} {nf : NormalFormCode} (h : nf.IsValid Z)
    (x : Fin nf.neg.arity → ℕ) :
    nf.neg.Holds Z x ↔ ¬nf.Holds Z (x ∘ Fin.cast (arity_neg nf).symm) := by
  simp only [holds_iff, Function.comp_def, ← List.ofFn_congr (arity_neg nf) x]
  exact evalList_neg h (by simp)

/-! ### Conjunction and disjunction at a common prefix -/

private def unpairFst (d : ℕ) (l : List ℕ) : List ℕ :=
  (l.take d).map (fun y => y.unpair.1) ++ l.drop d

private def unpairSnd (d : ℕ) (l : List ℕ) : List ℕ :=
  (l.take d).map (fun y => y.unpair.2) ++ l.drop d

private theorem length_unpairFst (d : ℕ) (l : List ℕ) : (unpairFst d l).length = l.length := by
  simp [unpairFst]
  omega

private theorem length_unpairSnd (d : ℕ) (l : List ℕ) : (unpairSnd d l).length = l.length := by
  simp [unpairSnd]
  omega

private def unpairFstBase : Code :=
  Code.mapTakeCode Code.left

private def unpairSndBase : Code :=
  Code.mapTakeCode Code.right

private theorem eval_unpairFstBase (O : ℕ →. ℕ) (d : ℕ) (l : List ℕ) :
    Code.eval O unpairFstBase (Nat.pair d (encode l)) = Part.some (encode (unpairFst d l)) :=
  Code.eval_mapTakeCode (fun y => Code.eval_left y) d l

private theorem eval_unpairSndBase (O : ℕ →. ℕ) (d : ℕ) (l : List ℕ) :
    Code.eval O unpairSndBase (Nat.pair d (encode l)) = Part.some (encode (unpairSnd d l)) :=
  Code.eval_mapTakeCode (fun y => Code.eval_right y) d l

private def unpairFstCode (d : ℕ) : Code :=
  Code.paramCode unpairFstBase d

private def unpairSndCode (d : ℕ) : Code :=
  Code.paramCode unpairSndBase d

/-- Effective conjunction of two normal-form codes at a common quantifier prefix and arity,
unpairing the first `nf₁.quantifiers.depth` bound variables and returning `none` when the
quantifier prefixes or arities differ. -/
def and (nf₁ nf₂ : NormalFormCode) : Option NormalFormCode :=
  if nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity then
    some ⟨nf₁.quantifiers, nf₁.arity,
      Code.boolAnd
        (Code.comp nf₁.matrix (unpairFstCode nf₁.quantifiers.depth))
        (Code.comp nf₂.matrix (unpairSndCode nf₁.quantifiers.depth))⟩
  else
    none

/-- Effective disjunction of two normal-form codes at a common quantifier prefix and arity,
unpairing the first `nf₁.quantifiers.depth` bound variables and returning `none` when the
quantifier prefixes or arities differ. -/
def or (nf₁ nf₂ : NormalFormCode) : Option NormalFormCode :=
  if nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity then
    some ⟨nf₁.quantifiers, nf₁.arity,
      Code.boolOr
        (Code.comp nf₁.matrix (unpairFstCode nf₁.quantifiers.depth))
        (Code.comp nf₂.matrix (unpairSndCode nf₁.quantifiers.depth))⟩
  else
    none

/-- Conjunction returns `none` if and only if the quantifier prefixes or arities differ. -/
@[simp]
theorem and_eq_none_iff (nf₁ nf₂ : NormalFormCode) :
    nf₁.and nf₂ = none ↔ nf₁.quantifiers ≠ nf₂.quantifiers ∨ nf₁.arity ≠ nf₂.arity := by
  by_cases hq : nf₁.quantifiers = nf₂.quantifiers <;> by_cases ha : nf₁.arity = nf₂.arity <;>
    simp [and, hq, ha]

/-- Conjunction succeeds if and only if the quantifier prefixes and arities agree. -/
@[simp]
theorem isSome_and_iff (nf₁ nf₂ : NormalFormCode) :
    (nf₁.and nf₂).isSome ↔ nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity := by
  by_cases h : nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity <;> simp [and, h]

/-- Conjunction produces a normal-form code if and only if the quantifier prefixes and arities
agree. -/
theorem exists_and_iff (nf₁ nf₂ : NormalFormCode) :
    (∃ nf, nf₁.and nf₂ = some nf) ↔ nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity := by
  simpa [Option.isSome_iff_exists] using isSome_and_iff nf₁ nf₂

/-- Disjunction returns `none` if and only if the quantifier prefixes or arities differ. -/
@[simp]
theorem or_eq_none_iff (nf₁ nf₂ : NormalFormCode) :
    nf₁.or nf₂ = none ↔ nf₁.quantifiers ≠ nf₂.quantifiers ∨ nf₁.arity ≠ nf₂.arity := by
  by_cases hq : nf₁.quantifiers = nf₂.quantifiers <;> by_cases ha : nf₁.arity = nf₂.arity <;>
    simp [or, hq, ha]

/-- Disjunction succeeds if and only if the quantifier prefixes and arities agree. -/
@[simp]
theorem isSome_or_iff (nf₁ nf₂ : NormalFormCode) :
    (nf₁.or nf₂).isSome ↔ nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity := by
  by_cases h : nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity <;> simp [or, h]

/-- Disjunction produces a normal-form code if and only if the quantifier prefixes and arities
agree. -/
theorem exists_or_iff (nf₁ nf₂ : NormalFormCode) :
    (∃ nf, nf₁.or nf₂ = some nf) ↔ nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity := by
  simpa [Option.isSome_iff_exists] using isSome_or_iff nf₁ nf₂

/-- A successful conjunction witnesses that the operands have equal quantifier prefixes. -/
theorem quantifiers_eq_of_and_eq_some {nf₁ nf₂ nf : NormalFormCode}
    (h : nf₁.and nf₂ = some nf) : nf₁.quantifiers = nf₂.quantifiers :=
  ((exists_and_iff nf₁ nf₂).1 ⟨nf, h⟩).1

/-- A successful conjunction witnesses that the operands have equal arities. -/
theorem arity_eq_of_and_eq_some {nf₁ nf₂ nf : NormalFormCode}
    (h : nf₁.and nf₂ = some nf) : nf₁.arity = nf₂.arity :=
  ((exists_and_iff nf₁ nf₂).1 ⟨nf, h⟩).2

/-- A successful conjunction retains the operands' quantifier prefix. -/
theorem quantifiers_and {nf₁ nf₂ nf : NormalFormCode} (h : nf₁.and nf₂ = some nf) :
    nf.quantifiers = nf₁.quantifiers := by
  unfold and at h
  split_ifs at h
  cases h
  rfl

/-- A successful conjunction retains the operands' arity. -/
theorem arity_and {nf₁ nf₂ nf : NormalFormCode} (h : nf₁.and nf₂ = some nf) :
    nf.arity = nf₁.arity := by
  unfold and at h
  split_ifs at h
  cases h
  rfl

/-- A successful disjunction witnesses that the operands have equal quantifier prefixes. -/
theorem quantifiers_eq_of_or_eq_some {nf₁ nf₂ nf : NormalFormCode}
    (h : nf₁.or nf₂ = some nf) : nf₁.quantifiers = nf₂.quantifiers :=
  ((exists_or_iff nf₁ nf₂).1 ⟨nf, h⟩).1

/-- A successful disjunction witnesses that the operands have equal arities. -/
theorem arity_eq_of_or_eq_some {nf₁ nf₂ nf : NormalFormCode}
    (h : nf₁.or nf₂ = some nf) : nf₁.arity = nf₂.arity :=
  ((exists_or_iff nf₁ nf₂).1 ⟨nf, h⟩).2

/-- A successful disjunction retains the operands' quantifier prefix. -/
theorem quantifiers_or {nf₁ nf₂ nf : NormalFormCode} (h : nf₁.or nf₂ = some nf) :
    nf.quantifiers = nf₁.quantifiers := by
  unfold or at h
  split_ifs at h
  cases h
  rfl

/-- A successful disjunction retains the operands' arity. -/
theorem arity_or {nf₁ nf₂ nf : NormalFormCode} (h : nf₁.or nf₂ = some nf) :
    nf.arity = nf₁.arity := by
  unfold or at h
  split_ifs at h
  cases h
  rfl

/-- Conjunction is primitive recursive on normal-form codes. -/
theorem primrec₂_and : Primrec₂ and := by
  have hcond : PrimrecPred fun p : NormalFormCode × NormalFormCode =>
      p.1.quantifiers = p.2.quantifiers ∧ p.1.arity = p.2.arity :=
    (Primrec.eq.comp (primrec_quantifiers.comp Primrec.fst)
      (primrec_quantifiers.comp Primrec.snd)).and
      (Primrec.eq.comp (primrec_arity.comp Primrec.fst)
        (primrec_arity.comp Primrec.snd))
  have hval : Primrec fun p : NormalFormCode × NormalFormCode =>
      (some ⟨p.1.quantifiers, p.1.arity,
        Code.boolAnd
          (Code.comp p.1.matrix (unpairFstCode p.1.quantifiers.depth))
          (Code.comp p.2.matrix (unpairSndCode p.1.quantifiers.depth))⟩ :
        Option NormalFormCode) :=
    Primrec.option_some.comp
      (primrec_mk.comp
        ((primrec_quantifiers.comp Primrec.fst).pair
          ((primrec_arity.comp Primrec.fst).pair
            (Code.primrec₂_boolAnd.comp
              (Code.primrec₂_comp.comp (primrec_matrix.comp Primrec.fst)
                ((Code.primrec_paramCode unpairFstBase).comp
                  (QuantifierPrefix.primrec_depth.comp (primrec_quantifiers.comp Primrec.fst))))
              (Code.primrec₂_comp.comp (primrec_matrix.comp Primrec.snd)
                ((Code.primrec_paramCode unpairSndBase).comp
                  (QuantifierPrefix.primrec_depth.comp
                    (primrec_quantifiers.comp Primrec.fst))))))))
  exact (Primrec.ite hcond hval (Primrec.const none)).to₂

/-- Disjunction is primitive recursive on normal-form codes. -/
theorem primrec₂_or : Primrec₂ or := by
  have hcond : PrimrecPred fun p : NormalFormCode × NormalFormCode =>
      p.1.quantifiers = p.2.quantifiers ∧ p.1.arity = p.2.arity :=
    (Primrec.eq.comp (primrec_quantifiers.comp Primrec.fst)
      (primrec_quantifiers.comp Primrec.snd)).and
      (Primrec.eq.comp (primrec_arity.comp Primrec.fst)
        (primrec_arity.comp Primrec.snd))
  have hval : Primrec fun p : NormalFormCode × NormalFormCode =>
      (some ⟨p.1.quantifiers, p.1.arity,
        Code.boolOr
          (Code.comp p.1.matrix (unpairFstCode p.1.quantifiers.depth))
          (Code.comp p.2.matrix (unpairSndCode p.1.quantifiers.depth))⟩ :
        Option NormalFormCode) :=
    Primrec.option_some.comp
      (primrec_mk.comp
        ((primrec_quantifiers.comp Primrec.fst).pair
          ((primrec_arity.comp Primrec.fst).pair
            (Code.primrec₂_boolOr.comp
              (Code.primrec₂_comp.comp (primrec_matrix.comp Primrec.fst)
                ((Code.primrec_paramCode unpairFstBase).comp
                  (QuantifierPrefix.primrec_depth.comp (primrec_quantifiers.comp Primrec.fst))))
              (Code.primrec₂_comp.comp (primrec_matrix.comp Primrec.snd)
                ((Code.primrec_paramCode unpairSndBase).comp
                  (QuantifierPrefix.primrec_depth.comp
                    (primrec_quantifiers.comp Primrec.fst))))))))
  exact (Primrec.ite hcond hval (Primrec.const none)).to₂

-- Shared evaluation of the two unpaired matrix sub-programs on a list of the expected length.
private theorem eval_unpair_components {Z : Set ℕ} {nf₁ nf₂ : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z)
    (hq : nf₁.quantifiers = nf₂.quantifiers) (ha : nf₁.arity = nf₂.arity)
    {l : List ℕ} (hl : l.length = nf₁.quantifiers.depth + nf₁.arity) :
    ∃ b₁ b₂ : Bool,
      encode b₁ ∈ Code.eval Z.oracle nf₁.matrix (encode (unpairFst nf₁.quantifiers.depth l)) ∧
      encode b₂ ∈ Code.eval Z.oracle nf₂.matrix (encode (unpairSnd nf₁.quantifiers.depth l)) ∧
      encode b₁ ∈ Code.eval Z.oracle
        (Code.comp nf₁.matrix (unpairFstCode nf₁.quantifiers.depth)) (encode l) ∧
      encode b₂ ∈ Code.eval Z.oracle
        (Code.comp nf₂.matrix (unpairSndCode nf₁.quantifiers.depth)) (encode l) := by
  have hl₁ : (unpairFst nf₁.quantifiers.depth l).length = nf₁.quantifiers.depth + nf₁.arity := by
    rw [length_unpairFst, hl]
  have hl₂ : (unpairSnd nf₁.quantifiers.depth l).length = nf₂.quantifiers.depth + nf₂.arity := by
    rw [length_unpairSnd, hl, hq, ha]
  obtain ⟨b₁, hb₁⟩ := isValid_iff.1 h₁ _ hl₁
  obtain ⟨b₂, hb₂⟩ := isValid_iff.1 h₂ _ hl₂
  refine ⟨b₁, b₂, hb₁, hb₂, ?_, ?_⟩
  · rw [unpairFstCode, Code.eval_comp_paramCode, encode_nat, eval_unpairFstBase, PFun.some_bind]
    exact hb₁
  · rw [unpairSndCode, Code.eval_comp_paramCode, encode_nat, eval_unpairSndBase, PFun.some_bind]
    exact hb₂

/-- Conjunction preserves validity when it succeeds. -/
theorem IsValid.and {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : nf₁.and nf₂ = some nf) :
    nf.IsValid Z := by
  unfold NormalFormCode.and at h
  split_ifs at h with hshape
  cases h
  refine isValid_iff.2 fun l hl => ?_
  obtain ⟨b₁, b₂, _, _, hm₁, hm₂⟩ := eval_unpair_components h₁ h₂ hshape.1 hshape.2 hl
  refine ⟨b₁ && b₂, ?_⟩
  rw [isValid_mk] at *
  rw [Code.eval_boolAnd Z.oracle _ _ (encode l) b₁ b₂ hm₁ hm₂]
  exact Part.mem_some _

/-- Disjunction preserves validity when it succeeds. -/
theorem IsValid.or {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : nf₁.or nf₂ = some nf) :
    nf.IsValid Z := by
  unfold NormalFormCode.or at h
  split_ifs at h with hshape
  cases h
  refine isValid_iff.2 fun l hl => ?_
  obtain ⟨b₁, b₂, _, _, hm₁, hm₂⟩ := eval_unpair_components h₁ h₂ hshape.1 hshape.2 hl
  refine ⟨b₁ || b₂, ?_⟩
  rw [Code.eval_boolOr Z.oracle _ _ (encode l) b₁ b₂ hm₁ hm₂]
  exact Part.mem_some _

/-- Matrix semantics for a successful conjunction on variable lists of the expected length: the
bound prefix of length `nf₁.quantifiers.depth` is unpaired coordinatewise while the free variables
are kept. -/
theorem matrixHolds_and {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : nf₁.and nf₂ = some nf)
    {l : List ℕ} (hl : l.length = nf₁.quantifiers.depth + nf₁.arity) :
    nf.MatrixHolds Z l ↔
      nf₁.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.1) ++
        l.drop nf₁.quantifiers.depth) ∧
      nf₂.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.2) ++
        l.drop nf₁.quantifiers.depth) := by
  unfold and at h
  split_ifs at h with hshape
  cases h
  obtain ⟨b₁, b₂, hb₁, hb₂, hm₁, hm₂⟩ := eval_unpair_components h₁ h₂ hshape.1 hshape.2 hl
  dsimp only [unpairFst, unpairSnd] at hb₁ hb₂
  have hand := Code.eval_boolAnd Z.oracle _ _ (encode l) b₁ b₂ hm₁ hm₂
  simp only [matrixHolds_iff, hand, Part.eq_some_iff.2 hb₁, Part.eq_some_iff.2 hb₂,
    Part.mem_some_iff]
  cases b₁ <;> cases b₂ <;> simp

/-- Matrix semantics for a successful disjunction on variable lists of the expected length: the
bound prefix of length `nf₁.quantifiers.depth` is unpaired coordinatewise while the free variables
are kept. -/
theorem matrixHolds_or {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : nf₁.or nf₂ = some nf)
    {l : List ℕ} (hl : l.length = nf₁.quantifiers.depth + nf₁.arity) :
    nf.MatrixHolds Z l ↔
      nf₁.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.1) ++
        l.drop nf₁.quantifiers.depth) ∨
      nf₂.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.2) ++
        l.drop nf₁.quantifiers.depth) := by
  unfold or at h
  split_ifs at h with hshape
  cases h
  obtain ⟨b₁, b₂, hb₁, hb₂, hm₁, hm₂⟩ := eval_unpair_components h₁ h₂ hshape.1 hshape.2 hl
  dsimp only [unpairFst, unpairSnd] at hb₁ hb₂
  have hor := Code.eval_boolOr Z.oracle _ _ (encode l) b₁ b₂ hm₁ hm₂
  simp only [matrixHolds_iff, hor, Part.eq_some_iff.2 hb₁, Part.eq_some_iff.2 hb₂,
    Part.mem_some_iff]
  cases b₁ <;> cases b₂ <;> simp

/-- Semantic equation for a successful conjunction on lists of the expected arity. -/
theorem evalList_and {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : nf₁.and nf₂ = some nf)
    {xs : List ℕ} (hxs : xs.length = nf₁.arity) :
    nf.EvalList Z xs ↔ nf₁.EvalList Z xs ∧ nf₂.EvalList Z xs := by
  have hq := quantifiers_eq_of_and_eq_some h
  rw [evalList_iff, evalList_iff, evalList_iff, quantifiers_and h, ← hq]
  refine (QuantifierPrefix.eval_congr_append fun bs hbs => ?_).trans
    (QuantifierPrefix.eval_and_unpair_iff nf₁.quantifiers (nf₁.MatrixHolds Z)
      (nf₂.MatrixHolds Z) xs xs xs)
  simpa [List.take_left' hbs, List.drop_left' hbs] using
    matrixHolds_and h₁ h₂ h (l := bs ++ xs) (by simp [hbs, hxs])

/-- Semantic equation for a successful disjunction on lists of the expected arity. -/
theorem evalList_or {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : nf₁.or nf₂ = some nf)
    {xs : List ℕ} (hxs : xs.length = nf₁.arity) :
    nf.EvalList Z xs ↔ nf₁.EvalList Z xs ∨ nf₂.EvalList Z xs := by
  have hq := quantifiers_eq_of_or_eq_some h
  rw [evalList_iff, evalList_iff, evalList_iff, quantifiers_or h, ← hq]
  refine (QuantifierPrefix.eval_congr_append fun bs hbs => ?_).trans
    (QuantifierPrefix.eval_or_unpair_iff nf₁.quantifiers (nf₁.MatrixHolds Z)
      (nf₂.MatrixHolds Z) xs xs xs)
  simpa [List.take_left' hbs, List.drop_left' hbs] using
    matrixHolds_or h₁ h₂ h (l := bs ++ xs) (by simp [hbs, hxs])

/-- Semantic equation for a successful conjunction on tuples. -/
theorem holds_and {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : nf₁.and nf₂ = some nf)
    (x : Fin nf.arity → ℕ) :
    nf.Holds Z x ↔
      nf₁.Holds Z (x ∘ Fin.cast (arity_and h).symm) ∧
      nf₂.Holds Z (x ∘ Fin.cast ((arity_and h).trans (arity_eq_of_and_eq_some h)).symm) := by
  simp only [holds_iff, Function.comp_def, ← List.ofFn_congr (arity_and h) x,
    ← List.ofFn_congr ((arity_and h).trans (arity_eq_of_and_eq_some h)) x]
  exact evalList_and h₁ h₂ h (by simp [arity_and h])

/-- Semantic equation for a successful disjunction on tuples. -/
theorem holds_or {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : nf₁.or nf₂ = some nf)
    (x : Fin nf.arity → ℕ) :
    nf.Holds Z x ↔
      nf₁.Holds Z (x ∘ Fin.cast (arity_or h).symm) ∨
      nf₂.Holds Z (x ∘ Fin.cast ((arity_or h).trans (arity_eq_of_or_eq_some h)).symm) := by
  simp only [holds_iff, Function.comp_def, ← List.ofFn_congr (arity_or h) x,
    ← List.ofFn_congr ((arity_or h).trans (arity_eq_of_or_eq_some h)) x]
  exact evalList_or h₁ h₂ h (by simp [arity_or h])

end NormalFormCode

end TauCeti.ArithmeticalHierarchy
