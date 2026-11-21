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
  quantifier prefix and arity, unpairing all bound variables simultaneously.

Every transformation is proved primitive recursive on `NormalFormCode` without depending on the
oracle. For valid operands — and, in the case of `and` and `or`, when the operands have matching
quantifier prefixes and arities — each transformation preserves semantic validity
(`NormalFormCode.IsValid Z`) and satisfies its exact semantic equation relative to every oracle `Z`
(on tuples of the declared arity and on variable lists of that length).

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

private theorem primrec₂_unpairFst : Primrec₂ unpairFst :=
  (Primrec.list_append.comp
    (Primrec.list_map (Primrec.list_take.comp Primrec.fst Primrec.snd)
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to₂)
    (Primrec.list_drop.comp Primrec.fst Primrec.snd)).to₂

private theorem primrec₂_unpairSnd : Primrec₂ unpairSnd :=
  (Primrec.list_append.comp
    (Primrec.list_map (Primrec.list_take.comp Primrec.fst Primrec.snd)
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to₂)
    (Primrec.list_drop.comp Primrec.fst Primrec.snd)).to₂

private theorem length_unpairFst (d : ℕ) (l : List ℕ) : (unpairFst d l).length = l.length := by
  simp [unpairFst]
  omega

private theorem length_unpairSnd (d : ℕ) (l : List ℕ) : (unpairSnd d l).length = l.length := by
  simp [unpairSnd]
  omega

private noncomputable def unpairFstCode (d : ℕ) : Code :=
  Code.paramCode primrec₂_unpairFst.to_comp d

private noncomputable def unpairSndCode (d : ℕ) : Code :=
  Code.paramCode primrec₂_unpairSnd.to_comp d

/-- Effective conjunction of two normal-form codes with matching quantifier prefix and arity. -/
noncomputable def and (nf₁ nf₂ : NormalFormCode) : NormalFormCode :=
  ⟨nf₁.quantifiers, nf₁.arity,
    Code.boolAnd
      (Code.comp nf₁.matrix (unpairFstCode nf₁.quantifiers.depth))
      (Code.comp nf₂.matrix (unpairSndCode nf₁.quantifiers.depth))⟩

/-- Effective disjunction of two normal-form codes with matching quantifier prefix and arity. -/
noncomputable def or (nf₁ nf₂ : NormalFormCode) : NormalFormCode :=
  ⟨nf₁.quantifiers, nf₁.arity,
    Code.boolOr
      (Code.comp nf₁.matrix (unpairFstCode nf₁.quantifiers.depth))
      (Code.comp nf₂.matrix (unpairSndCode nf₁.quantifiers.depth))⟩

/-- Conjunction retains the first operand's quantifier prefix. -/
@[simp]
theorem quantifiers_and (nf₁ nf₂ : NormalFormCode) :
    (nf₁.and nf₂).quantifiers = nf₁.quantifiers := (rfl)

/-- Conjunction retains the first operand's arity. -/
@[simp]
theorem arity_and (nf₁ nf₂ : NormalFormCode) : (nf₁.and nf₂).arity = nf₁.arity := (rfl)

/-- Disjunction retains the first operand's quantifier prefix. -/
@[simp]
theorem quantifiers_or (nf₁ nf₂ : NormalFormCode) :
    (nf₁.or nf₂).quantifiers = nf₁.quantifiers := (rfl)

/-- Disjunction retains the first operand's arity. -/
@[simp]
theorem arity_or (nf₁ nf₂ : NormalFormCode) : (nf₁.or nf₂).arity = nf₁.arity := (rfl)

/-- Conjunction is primitive recursive on normal-form codes. -/
theorem primrec₂_and : Primrec₂ and :=
  (primrec_mk.comp
    ((primrec_quantifiers.comp Primrec.fst).pair
      ((primrec_arity.comp Primrec.fst).pair
        (Code.primrec₂_boolAnd.comp
          (Code.primrec₂_comp.comp (primrec_matrix.comp Primrec.fst)
            ((Code.primrec_paramCode primrec₂_unpairFst.to_comp).comp
              (QuantifierPrefix.primrec_depth.comp (primrec_quantifiers.comp Primrec.fst))))
          (Code.primrec₂_comp.comp (primrec_matrix.comp Primrec.snd)
            ((Code.primrec_paramCode primrec₂_unpairSnd.to_comp).comp
              (QuantifierPrefix.primrec_depth.comp
                (primrec_quantifiers.comp Primrec.fst)))))))).to₂

/-- Disjunction is primitive recursive on normal-form codes. -/
theorem primrec₂_or : Primrec₂ or :=
  (primrec_mk.comp
    ((primrec_quantifiers.comp Primrec.fst).pair
      ((primrec_arity.comp Primrec.fst).pair
        (Code.primrec₂_boolOr.comp
          (Code.primrec₂_comp.comp (primrec_matrix.comp Primrec.fst)
            ((Code.primrec_paramCode primrec₂_unpairFst.to_comp).comp
              (QuantifierPrefix.primrec_depth.comp (primrec_quantifiers.comp Primrec.fst))))
          (Code.primrec₂_comp.comp (primrec_matrix.comp Primrec.snd)
            ((Code.primrec_paramCode primrec₂_unpairSnd.to_comp).comp
              (QuantifierPrefix.primrec_depth.comp
                (primrec_quantifiers.comp Primrec.fst)))))))).to₂

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
  · rw [unpairFstCode, Code.eval_comp_paramCode]
    exact hb₁
  · rw [unpairSndCode, Code.eval_comp_paramCode]
    exact hb₂

/-- Conjunction preserves validity when both operands share prefix and arity. -/
theorem IsValid.and {Z : Set ℕ} {nf₁ nf₂ : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z)
    (hq : nf₁.quantifiers = nf₂.quantifiers) (ha : nf₁.arity = nf₂.arity) :
    (nf₁.and nf₂).IsValid Z := by
  refine isValid_iff.2 fun l hl => ?_
  obtain ⟨b₁, b₂, _, _, hm₁, hm₂⟩ := eval_unpair_components h₁ h₂ hq ha hl
  refine ⟨b₁ && b₂, ?_⟩
  rw [NormalFormCode.and, Code.eval_boolAnd Z.oracle _ _ (encode l) b₁ b₂ hm₁ hm₂]
  exact Part.mem_some _

/-- Disjunction preserves validity when both operands share prefix and arity. -/
theorem IsValid.or {Z : Set ℕ} {nf₁ nf₂ : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z)
    (hq : nf₁.quantifiers = nf₂.quantifiers) (ha : nf₁.arity = nf₂.arity) :
    (nf₁.or nf₂).IsValid Z := by
  refine isValid_iff.2 fun l hl => ?_
  obtain ⟨b₁, b₂, _, _, hm₁, hm₂⟩ := eval_unpair_components h₁ h₂ hq ha hl
  refine ⟨b₁ || b₂, ?_⟩
  rw [NormalFormCode.or, Code.eval_boolOr Z.oracle _ _ (encode l) b₁ b₂ hm₁ hm₂]
  exact Part.mem_some _

-- Shared matrix equivalence for conjunction and disjunction on paired bound variables.
private theorem matrixHolds_and_or {Z : Set ℕ} {nf₁ nf₂ : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z)
    (hq : nf₁.quantifiers = nf₂.quantifiers) (ha : nf₁.arity = nf₂.arity)
    {l : List ℕ} (hl : l.length = nf₁.quantifiers.depth + nf₁.arity) :
    ((nf₁.and nf₂).MatrixHolds Z l ↔
      nf₁.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.1) ++
        l.drop nf₁.quantifiers.depth) ∧
      nf₂.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.2) ++
        l.drop nf₁.quantifiers.depth)) ∧
    ((nf₁.or nf₂).MatrixHolds Z l ↔
      nf₁.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.1) ++
        l.drop nf₁.quantifiers.depth) ∨
      nf₂.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.2) ++
        l.drop nf₁.quantifiers.depth)) := by
  obtain ⟨b₁, b₂, hb₁, hb₂, hm₁, hm₂⟩ := eval_unpair_components h₁ h₂ hq ha hl
  dsimp only [unpairFst, unpairSnd] at hb₁ hb₂
  have hand := Code.eval_boolAnd Z.oracle _ _ (encode l) b₁ b₂ hm₁ hm₂
  have hor := Code.eval_boolOr Z.oracle _ _ (encode l) b₁ b₂ hm₁ hm₂
  simp only [matrixHolds_iff, and, or, hand, hor, Part.eq_some_iff.2 hb₁, Part.eq_some_iff.2 hb₂,
    Part.mem_some_iff]
  cases b₁ <;> cases b₂ <;> simp

/-- Matrix semantics for conjunction on variable lists of the expected length: the bound prefix of
length `nf₁.quantifiers.depth` is unpaired coordinatewise while the free variables are kept. -/
theorem matrixHolds_and {Z : Set ℕ} {nf₁ nf₂ : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z)
    (hq : nf₁.quantifiers = nf₂.quantifiers) (ha : nf₁.arity = nf₂.arity)
    {l : List ℕ} (hl : l.length = nf₁.quantifiers.depth + nf₁.arity) :
    (nf₁.and nf₂).MatrixHolds Z l ↔
      nf₁.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.1) ++
        l.drop nf₁.quantifiers.depth) ∧
      nf₂.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.2) ++
        l.drop nf₁.quantifiers.depth) :=
  (matrixHolds_and_or h₁ h₂ hq ha hl).1

/-- Matrix semantics for disjunction on variable lists of the expected length: the bound prefix of
length `nf₁.quantifiers.depth` is unpaired coordinatewise while the free variables are kept. -/
theorem matrixHolds_or {Z : Set ℕ} {nf₁ nf₂ : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z)
    (hq : nf₁.quantifiers = nf₂.quantifiers) (ha : nf₁.arity = nf₂.arity)
    {l : List ℕ} (hl : l.length = nf₁.quantifiers.depth + nf₁.arity) :
    (nf₁.or nf₂).MatrixHolds Z l ↔
      nf₁.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.1) ++
        l.drop nf₁.quantifiers.depth) ∨
      nf₂.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.2) ++
        l.drop nf₁.quantifiers.depth) :=
  (matrixHolds_and_or h₁ h₂ hq ha hl).2

/-- Semantic equation for conjunction on lists of the expected arity. -/
theorem evalList_and {Z : Set ℕ} {nf₁ nf₂ : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z)
    (hq : nf₁.quantifiers = nf₂.quantifiers) (ha : nf₁.arity = nf₂.arity)
    {xs : List ℕ} (hxs : xs.length = nf₁.arity) :
    (nf₁.and nf₂).EvalList Z xs ↔ nf₁.EvalList Z xs ∧ nf₂.EvalList Z xs := by
  rw [evalList_iff, evalList_iff, evalList_iff, quantifiers_and, ← hq]
  refine (QuantifierPrefix.eval_congr_append fun bs hbs => ?_).trans
    (QuantifierPrefix.eval_and_unpair_iff nf₁.quantifiers (nf₁.MatrixHolds Z)
      (nf₂.MatrixHolds Z) xs xs xs)
  simpa [List.take_left' hbs, List.drop_left' hbs] using
    matrixHolds_and h₁ h₂ hq ha (l := bs ++ xs) (by simp [hbs, hxs])

/-- Semantic equation for disjunction on lists of the expected arity. -/
theorem evalList_or {Z : Set ℕ} {nf₁ nf₂ : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z)
    (hq : nf₁.quantifiers = nf₂.quantifiers) (ha : nf₁.arity = nf₂.arity)
    {xs : List ℕ} (hxs : xs.length = nf₁.arity) :
    (nf₁.or nf₂).EvalList Z xs ↔ nf₁.EvalList Z xs ∨ nf₂.EvalList Z xs := by
  rw [evalList_iff, evalList_iff, evalList_iff, quantifiers_or, ← hq]
  refine (QuantifierPrefix.eval_congr_append fun bs hbs => ?_).trans
    (QuantifierPrefix.eval_or_unpair_iff nf₁.quantifiers (nf₁.MatrixHolds Z)
      (nf₂.MatrixHolds Z) xs xs xs)
  simpa [List.take_left' hbs, List.drop_left' hbs] using
    matrixHolds_or h₁ h₂ hq ha (l := bs ++ xs) (by simp [hbs, hxs])

/-- Semantic equation for conjunction on tuples. -/
theorem holds_and {Z : Set ℕ} {nf₁ nf₂ : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z)
    (hq : nf₁.quantifiers = nf₂.quantifiers) (ha : nf₁.arity = nf₂.arity)
    (x : Fin (nf₁.and nf₂).arity → ℕ) :
    (nf₁.and nf₂).Holds Z x ↔
      nf₁.Holds Z (x ∘ Fin.cast (arity_and nf₁ nf₂).symm) ∧
      nf₂.Holds Z (x ∘ Fin.cast ((arity_and nf₁ nf₂).trans ha).symm) := by
  simp only [holds_iff, Function.comp_def, ← List.ofFn_congr (arity_and nf₁ nf₂) x,
    ← List.ofFn_congr ((arity_and nf₁ nf₂).trans ha) x]
  exact evalList_and h₁ h₂ hq ha (by simp)

/-- Semantic equation for disjunction on tuples. -/
theorem holds_or {Z : Set ℕ} {nf₁ nf₂ : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z)
    (hq : nf₁.quantifiers = nf₂.quantifiers) (ha : nf₁.arity = nf₂.arity)
    (x : Fin (nf₁.or nf₂).arity → ℕ) :
    (nf₁.or nf₂).Holds Z x ↔
      nf₁.Holds Z (x ∘ Fin.cast (arity_or nf₁ nf₂).symm) ∨
      nf₂.Holds Z (x ∘ Fin.cast ((arity_or nf₁ nf₂).trans ha).symm) := by
  simp only [holds_iff, Function.comp_def, ← List.ofFn_congr (arity_or nf₁ nf₂) x,
    ← List.ofFn_congr ((arity_or nf₁ nf₂).trans ha) x]
  exact evalList_or h₁ h₂ hq ha (by simp)

end NormalFormCode

end TauCeti.ArithmeticalHierarchy
