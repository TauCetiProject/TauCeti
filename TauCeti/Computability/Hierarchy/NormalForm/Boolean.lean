/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.NormalForm.Basic
import TauCeti.Data.List.TakeDrop
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
  simp only [matrix_neg, Code.eval_boolNot Z.oracle nf.matrix (encode l) b hb, Part.mem_some_iff]

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

private theorem unpairFst_eq (d : ℕ) (l : List ℕ) :
    unpairFst d l = (l.take d).map (fun y => y.unpair.1) ++ l.drop d := (rfl)

private theorem unpairSnd_eq (d : ℕ) (l : List ℕ) :
    unpairSnd d l = (l.take d).map (fun y => y.unpair.2) ++ l.drop d := (rfl)

private theorem exists_unpairTakeCode {f : ℕ → ℕ} (hf : Primrec f) :
    ∃ c : Code, ∀ (O : ℕ →. ℕ) (d : ℕ) (l : List ℕ),
      Code.eval O c (Nat.pair d (encode l)) =
        Part.some (encode ((l.take d).map f ++ l.drop d)) := by
  have hprim : Primrec fun p : ℕ =>
      encode (((ofNat (List ℕ) p.unpair.2).take p.unpair.1).map f ++
        (ofNat (List ℕ) p.unpair.2).drop p.unpair.1) :=
    Primrec.encode.comp
      (Primrec.list_append.comp
        (Primrec.list_map
          (Primrec.list_take.comp (Primrec.fst.comp Primrec.unpair)
            ((Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp Primrec.unpair)))
          (hf.comp Primrec.snd).to₂)
        (Primrec.list_drop.comp (Primrec.fst.comp Primrec.unpair)
          ((Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp Primrec.unpair))))
  obtain ⟨c, hc⟩ := Code.exists_code_of_computable hprim.to_comp
  exact ⟨c, fun O d l => by
    simpa [Nat.unpair_pair, ofNat_encode] using hc O (Nat.pair d (encode l))⟩

private noncomputable def unpairFstBase : Code :=
  (exists_unpairTakeCode (Primrec.fst.comp Primrec.unpair)).choose

private noncomputable def unpairSndBase : Code :=
  (exists_unpairTakeCode (Primrec.snd.comp Primrec.unpair)).choose

private theorem eval_unpairFstBase (O : ℕ →. ℕ) (d : ℕ) (l : List ℕ) :
    Code.eval O unpairFstBase (Nat.pair d (encode l)) = Part.some (encode (unpairFst d l)) := by
  unfold unpairFstBase
  rw [unpairFst_eq]
  exact (exists_unpairTakeCode (Primrec.fst.comp Primrec.unpair)).choose_spec O d l

private theorem eval_unpairSndBase (O : ℕ →. ℕ) (d : ℕ) (l : List ℕ) :
    Code.eval O unpairSndBase (Nat.pair d (encode l)) = Part.some (encode (unpairSnd d l)) := by
  unfold unpairSndBase
  rw [unpairSnd_eq]
  exact (exists_unpairTakeCode (Primrec.snd.comp Primrec.unpair)).choose_spec O d l

private noncomputable def unpairFstCode (d : ℕ) : Code :=
  Code.curry unpairFstBase d

private noncomputable def unpairSndCode (d : ℕ) : Code :=
  Code.curry unpairSndBase d

private noncomputable def binop (op : Code → Code → Code)
    (nf₁ nf₂ : NormalFormCode) : Option NormalFormCode :=
  if nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity then
    some ⟨nf₁.quantifiers, nf₁.arity,
      op
        (Code.comp nf₁.matrix (unpairFstCode nf₁.quantifiers.depth))
        (Code.comp nf₂.matrix (unpairSndCode nf₁.quantifiers.depth))⟩
  else
    none

private theorem binop_eq_some_iff {op : Code → Code → Code}
    {nf₁ nf₂ nf : NormalFormCode} :
    binop op nf₁ nf₂ = some nf ↔
      nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity ∧
      nf = ⟨nf₁.quantifiers, nf₁.arity,
        op
          (Code.comp nf₁.matrix (unpairFstCode nf₁.quantifiers.depth))
          (Code.comp nf₂.matrix (unpairSndCode nf₁.quantifiers.depth))⟩ := by
  by_cases hq : nf₁.quantifiers = nf₂.quantifiers <;>
    by_cases ha : nf₁.arity = nf₂.arity <;>
    simp [binop, hq, ha, eq_comm]

private theorem exists_binop_iff (op : Code → Code → Code) (nf₁ nf₂ : NormalFormCode) :
    (∃ nf, binop op nf₁ nf₂ = some nf) ↔
      nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity := by
  simp [binop_eq_some_iff]

private theorem isSome_binop_iff (op : Code → Code → Code) (nf₁ nf₂ : NormalFormCode) :
    (binop op nf₁ nf₂).isSome ↔ nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity :=
  Option.isSome_iff_exists.trans (exists_binop_iff op nf₁ nf₂)

private theorem binop_eq_none_iff (op : Code → Code → Code) (nf₁ nf₂ : NormalFormCode) :
    binop op nf₁ nf₂ = none ↔ nf₁.quantifiers ≠ nf₂.quantifiers ∨ nf₁.arity ≠ nf₂.arity := by
  rw [← Option.not_isSome_iff_eq_none, isSome_binop_iff, not_and_or]

private theorem quantifiers_eq_of_binop_eq_some {op : Code → Code → Code}
    {nf₁ nf₂ nf : NormalFormCode} (h : binop op nf₁ nf₂ = some nf) :
    nf₁.quantifiers = nf₂.quantifiers :=
  (binop_eq_some_iff.1 h).1

private theorem arity_eq_of_binop_eq_some {op : Code → Code → Code}
    {nf₁ nf₂ nf : NormalFormCode} (h : binop op nf₁ nf₂ = some nf) :
    nf₁.arity = nf₂.arity :=
  (binop_eq_some_iff.1 h).2.1

private theorem quantifiers_binop {op : Code → Code → Code} {nf₁ nf₂ nf : NormalFormCode}
    (h : binop op nf₁ nf₂ = some nf) : nf.quantifiers = nf₁.quantifiers := by
  rw [(binop_eq_some_iff.1 h).2.2]

private theorem arity_binop {op : Code → Code → Code} {nf₁ nf₂ nf : NormalFormCode}
    (h : binop op nf₁ nf₂ = some nf) : nf.arity = nf₁.arity := by
  rw [(binop_eq_some_iff.1 h).2.2]

private theorem eval_unpairCodes (O : ℕ →. ℕ) (d : ℕ) (l : List ℕ) :
    Code.eval O (unpairFstCode d) (encode l) = Part.some (encode (unpairFst d l)) ∧
    Code.eval O (unpairSndCode d) (encode l) = Part.some (encode (unpairSnd d l)) := by
  simp only [unpairFstCode, unpairSndCode, Code.eval_curry]
  exact ⟨eval_unpairFstBase O d l, eval_unpairSndBase O d l⟩

private theorem exists_matrix_binop {op : Code → Code → Code} {nf₁ nf₂ nf : NormalFormCode}
    (h : binop op nf₁ nf₂ = some nf) :
    ∃ c₁ c₂ : Code,
      nf.matrix = op (Code.comp nf₁.matrix c₁) (Code.comp nf₂.matrix c₂) ∧
      (∀ (O : ℕ →. ℕ) (l : List ℕ),
        Code.eval O c₁ (encode l) = Part.some (encode (unpairFst nf₁.quantifiers.depth l)) ∧
        Code.eval O c₂ (encode l) = Part.some (encode (unpairSnd nf₁.quantifiers.depth l))) :=
  ⟨unpairFstCode nf₁.quantifiers.depth, unpairSndCode nf₁.quantifiers.depth,
    by rw [(binop_eq_some_iff.1 h).2.2], fun O l => eval_unpairCodes O _ l⟩

private theorem exists_binop_eq_some {op : Code → Code → Code} {nf₁ nf₂ : NormalFormCode}
    (hq : nf₁.quantifiers = nf₂.quantifiers) (ha : nf₁.arity = nf₂.arity) :
    ∃ c₁ c₂ : Code,
      binop op nf₁ nf₂ = some ⟨nf₁.quantifiers, nf₁.arity,
        op (Code.comp nf₁.matrix c₁) (Code.comp nf₂.matrix c₂)⟩ ∧
      (∀ (O : ℕ →. ℕ) (l : List ℕ),
        Code.eval O c₁ (encode l) = Part.some (encode (unpairFst nf₁.quantifiers.depth l)) ∧
        Code.eval O c₂ (encode l) = Part.some (encode (unpairSnd nf₁.quantifiers.depth l))) :=
  ⟨unpairFstCode nf₁.quantifiers.depth, unpairSndCode nf₁.quantifiers.depth,
    binop_eq_some_iff.2 ⟨hq, ha, rfl⟩, fun O l => eval_unpairCodes O _ l⟩

private theorem primrec₂_binop {op : Code → Code → Code} (hop : Primrec₂ op) :
    Primrec₂ (binop op) := by
  have hcond : PrimrecPred fun p : NormalFormCode × NormalFormCode =>
      p.1.quantifiers = p.2.quantifiers ∧ p.1.arity = p.2.arity :=
    (Primrec.eq.comp (primrec_quantifiers.comp Primrec.fst)
      (primrec_quantifiers.comp Primrec.snd)).and
      (Primrec.eq.comp (primrec_arity.comp Primrec.fst)
        (primrec_arity.comp Primrec.snd))
  have hval : Primrec fun p : NormalFormCode × NormalFormCode =>
      (some ⟨p.1.quantifiers, p.1.arity,
        op
          (Code.comp p.1.matrix (unpairFstCode p.1.quantifiers.depth))
          (Code.comp p.2.matrix (unpairSndCode p.1.quantifiers.depth))⟩ :
        Option NormalFormCode) :=
    Primrec.option_some.comp
      (primrec_mk.comp
        ((primrec_quantifiers.comp Primrec.fst).pair
          ((primrec_arity.comp Primrec.fst).pair
            (hop.comp
              (Code.primrec₂_comp.comp (primrec_matrix.comp Primrec.fst)
                ((Code.primrec₂_curry.comp (Primrec.const unpairFstBase) Primrec.id).comp
                  (QuantifierPrefix.primrec_depth.comp (primrec_quantifiers.comp Primrec.fst))))
              (Code.primrec₂_comp.comp (primrec_matrix.comp Primrec.snd)
                ((Code.primrec₂_curry.comp (Primrec.const unpairSndBase) Primrec.id).comp
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
    rw [unpairFst_eq, List.length_map_take_append_drop, hl]
  have hl₂ : (unpairSnd nf₁.quantifiers.depth l).length = nf₂.quantifiers.depth + nf₂.arity := by
    rw [unpairSnd_eq, List.length_map_take_append_drop, hl, hq, ha]
  obtain ⟨b₁, hb₁⟩ := isValid_iff.1 h₁ _ hl₁
  obtain ⟨b₂, hb₂⟩ := isValid_iff.1 h₂ _ hl₂
  refine ⟨b₁, b₂, hb₁, hb₂, ?_, ?_⟩
  · rw [Code.eval_comp, (eval_unpairCodes Z.oracle _ l).1, PFun.some_bind]
    exact hb₁
  · rw [Code.eval_comp, (eval_unpairCodes Z.oracle _ l).2, PFun.some_bind]
    exact hb₂

private theorem isValid_binop {op : Code → Code → Code} {fb : Bool → Bool → Bool}
    (hop : ∀ (O : ℕ →. ℕ) (c₁ c₂ : Code) (n : ℕ) (b₁ b₂ : Bool),
      encode b₁ ∈ Code.eval O c₁ n → encode b₂ ∈ Code.eval O c₂ n →
      Code.eval O (op c₁ c₂) n = Part.some (encode (fb b₁ b₂)))
    {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : binop op nf₁ nf₂ = some nf) :
    nf.IsValid Z := by
  obtain ⟨hq, ha, rfl⟩ := binop_eq_some_iff.1 h
  refine isValid_iff.2 fun l hl => ?_
  obtain ⟨b₁, b₂, _, _, hm₁, hm₂⟩ := eval_unpair_components h₁ h₂ hq ha hl
  refine ⟨fb b₁ b₂, ?_⟩
  rw [hop Z.oracle _ _ (encode l) b₁ b₂ hm₁ hm₂]
  exact Part.mem_some _

private theorem matrixHolds_binop {op : Code → Code → Code} {fb : Bool → Bool → Bool}
    {P : Prop → Prop → Prop}
    (hop : ∀ (O : ℕ →. ℕ) (c₁ c₂ : Code) (n : ℕ) (b₁ b₂ : Bool),
      encode b₁ ∈ Code.eval O c₁ n → encode b₂ ∈ Code.eval O c₂ n →
      Code.eval O (op c₁ c₂) n = Part.some (encode (fb b₁ b₂)))
    (hP : ∀ b₁ b₂ : Bool, (fb b₁ b₂ = true) ↔ P (b₁ = true) (b₂ = true))
    {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : binop op nf₁ nf₂ = some nf)
    {l : List ℕ} (hl : l.length = nf₁.quantifiers.depth + nf₁.arity) :
    nf.MatrixHolds Z l ↔
      P (nf₁.MatrixHolds Z (unpairFst nf₁.quantifiers.depth l))
        (nf₂.MatrixHolds Z (unpairSnd nf₁.quantifiers.depth l)) := by
  obtain ⟨hq, ha, rfl⟩ := binop_eq_some_iff.1 h
  obtain ⟨b₁, b₂, hb₁, hb₂, hm₁, hm₂⟩ := eval_unpair_components h₁ h₂ hq ha hl
  have heval := hop Z.oracle _ _ (encode l) b₁ b₂ hm₁ hm₂
  simp only [matrixHolds_iff, heval, Part.eq_some_iff.2 hb₁, Part.eq_some_iff.2 hb₂,
    Part.mem_some_iff]
  have hfb := hP b₁ b₂
  cases b₁ <;> cases b₂ <;> cases h' : fb _ _ <;> simp_all

private theorem evalList_binop {op : Code → Code → Code} {P : Prop → Prop → Prop}
    (hmat : ∀ {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode},
      nf₁.IsValid Z → nf₂.IsValid Z → binop op nf₁ nf₂ = some nf →
      ∀ {l : List ℕ}, l.length = nf₁.quantifiers.depth + nf₁.arity →
        (nf.MatrixHolds Z l ↔
          P (nf₁.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.1) ++
              l.drop nf₁.quantifiers.depth))
            (nf₂.MatrixHolds Z ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.2) ++
              l.drop nf₁.quantifiers.depth))))
    (hdist : ∀ (p : QuantifierPrefix) (R₁ R₂ : List ℕ → Prop) (xs₁ xs₂ xs : List ℕ),
      p.Eval (fun l => P (R₁ ((l.take p.depth).map (fun y => y.unpair.1) ++ xs₁))
        (R₂ ((l.take p.depth).map (fun y => y.unpair.2) ++ xs₂))) xs ↔
      P (p.Eval R₁ xs₁) (p.Eval R₂ xs₂))
    {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : binop op nf₁ nf₂ = some nf)
    {xs : List ℕ} (hxs : xs.length = nf₁.arity) :
    nf.EvalList Z xs ↔ P (nf₁.EvalList Z xs) (nf₂.EvalList Z xs) := by
  have hq := quantifiers_eq_of_binop_eq_some h
  rw [evalList_iff, evalList_iff, evalList_iff, quantifiers_binop h, ← hq]
  refine (QuantifierPrefix.eval_congr_append fun bs hbs => ?_).trans
    (hdist nf₁.quantifiers (nf₁.MatrixHolds Z) (nf₂.MatrixHolds Z) xs xs xs)
  simpa [List.take_left' hbs, List.drop_left' hbs] using
    hmat h₁ h₂ h (l := bs ++ xs) (by simp [hbs, hxs])

private theorem holds_binop {op : Code → Code → Code} {P : Prop → Prop → Prop}
    (heval : ∀ {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode},
      nf₁.IsValid Z → nf₂.IsValid Z → binop op nf₁ nf₂ = some nf →
      ∀ {xs : List ℕ}, xs.length = nf₁.arity →
        (nf.EvalList Z xs ↔ P (nf₁.EvalList Z xs) (nf₂.EvalList Z xs)))
    {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : binop op nf₁ nf₂ = some nf)
    (x : Fin nf.arity → ℕ) :
    nf.Holds Z x ↔
      P (nf₁.Holds Z (x ∘ Fin.cast (arity_binop h).symm))
        (nf₂.Holds Z
          (x ∘ Fin.cast ((arity_binop h).trans (arity_eq_of_binop_eq_some h)).symm)) := by
  simp only [holds_iff, Function.comp_def, ← List.ofFn_congr (arity_binop h) x,
    ← List.ofFn_congr ((arity_binop h).trans (arity_eq_of_binop_eq_some h)) x]
  exact heval h₁ h₂ h (by simp [arity_binop h])

/-- Effective conjunction of two normal-form codes at a common quantifier prefix and arity,
unpairing the first `nf₁.quantifiers.depth` bound variables and returning `none` when the
quantifier prefixes or arities differ. -/
noncomputable def and (nf₁ nf₂ : NormalFormCode) : Option NormalFormCode :=
  binop Code.boolAnd nf₁ nf₂

/-- Effective disjunction of two normal-form codes at a common quantifier prefix and arity,
unpairing the first `nf₁.quantifiers.depth` bound variables and returning `none` when the
quantifier prefixes or arities differ. -/
noncomputable def or (nf₁ nf₂ : NormalFormCode) : Option NormalFormCode :=
  binop Code.boolOr nf₁ nf₂

/-- Conjunction returns `none` if and only if the quantifier prefixes or arities differ. -/
@[simp]
theorem and_eq_none_iff (nf₁ nf₂ : NormalFormCode) :
    nf₁.and nf₂ = none ↔ nf₁.quantifiers ≠ nf₂.quantifiers ∨ nf₁.arity ≠ nf₂.arity :=
  binop_eq_none_iff Code.boolAnd nf₁ nf₂

/-- Conjunction succeeds if and only if the quantifier prefixes and arities agree. -/
@[simp]
theorem isSome_and_iff (nf₁ nf₂ : NormalFormCode) :
    (nf₁.and nf₂).isSome ↔ nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity :=
  isSome_binop_iff Code.boolAnd nf₁ nf₂

/-- Conjunction produces a normal-form code if and only if the quantifier prefixes and arities
agree. -/
theorem exists_and_iff (nf₁ nf₂ : NormalFormCode) :
    (∃ nf, nf₁.and nf₂ = some nf) ↔ nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity :=
  exists_binop_iff Code.boolAnd nf₁ nf₂

/-- Disjunction returns `none` if and only if the quantifier prefixes or arities differ. -/
@[simp]
theorem or_eq_none_iff (nf₁ nf₂ : NormalFormCode) :
    nf₁.or nf₂ = none ↔ nf₁.quantifiers ≠ nf₂.quantifiers ∨ nf₁.arity ≠ nf₂.arity :=
  binop_eq_none_iff Code.boolOr nf₁ nf₂

/-- Disjunction succeeds if and only if the quantifier prefixes and arities agree. -/
@[simp]
theorem isSome_or_iff (nf₁ nf₂ : NormalFormCode) :
    (nf₁.or nf₂).isSome ↔ nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity :=
  isSome_binop_iff Code.boolOr nf₁ nf₂

/-- Disjunction produces a normal-form code if and only if the quantifier prefixes and arities
agree. -/
theorem exists_or_iff (nf₁ nf₂ : NormalFormCode) :
    (∃ nf, nf₁.or nf₂ = some nf) ↔ nf₁.quantifiers = nf₂.quantifiers ∧ nf₁.arity = nf₂.arity :=
  exists_binop_iff Code.boolOr nf₁ nf₂

/-- When the quantifier prefixes and arities agree, `and` returns `some` of a normal-form code
whose matrix applies `Code.boolAnd` to `nf₁.matrix` and `nf₂.matrix` composed with
oracle-independent unpairing preprocessors on the first `nf₁.quantifiers.depth` bound
variables. -/
theorem exists_and_eq_some {nf₁ nf₂ : NormalFormCode}
    (hq : nf₁.quantifiers = nf₂.quantifiers) (ha : nf₁.arity = nf₂.arity) :
    ∃ c₁ c₂ : Code,
      nf₁.and nf₂ = some ⟨nf₁.quantifiers, nf₁.arity,
        Code.boolAnd (Code.comp nf₁.matrix c₁) (Code.comp nf₂.matrix c₂)⟩ ∧
      (∀ (O : ℕ →. ℕ) (l : List ℕ),
        Code.eval O c₁ (encode l) = Part.some (encode
          ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.1) ++
            l.drop nf₁.quantifiers.depth)) ∧
        Code.eval O c₂ (encode l) = Part.some (encode
          ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.2) ++
            l.drop nf₁.quantifiers.depth))) := by
  simp only [← unpairFst_eq, ← unpairSnd_eq]
  exact exists_binop_eq_some hq ha

/-- When the quantifier prefixes and arities agree, `or` returns `some` of a normal-form code
whose matrix applies `Code.boolOr` to `nf₁.matrix` and `nf₂.matrix` composed with oracle-independent
unpairing preprocessors on the first `nf₁.quantifiers.depth` bound variables. -/
theorem exists_or_eq_some {nf₁ nf₂ : NormalFormCode}
    (hq : nf₁.quantifiers = nf₂.quantifiers) (ha : nf₁.arity = nf₂.arity) :
    ∃ c₁ c₂ : Code,
      nf₁.or nf₂ = some ⟨nf₁.quantifiers, nf₁.arity,
        Code.boolOr (Code.comp nf₁.matrix c₁) (Code.comp nf₂.matrix c₂)⟩ ∧
      (∀ (O : ℕ →. ℕ) (l : List ℕ),
        Code.eval O c₁ (encode l) = Part.some (encode
          ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.1) ++
            l.drop nf₁.quantifiers.depth)) ∧
        Code.eval O c₂ (encode l) = Part.some (encode
          ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.2) ++
            l.drop nf₁.quantifiers.depth))) := by
  simp only [← unpairFst_eq, ← unpairSnd_eq]
  exact exists_binop_eq_some hq ha

/-- A successful conjunction witnesses that the operands have equal quantifier prefixes. -/
theorem quantifiers_eq_of_and_eq_some {nf₁ nf₂ nf : NormalFormCode}
    (h : nf₁.and nf₂ = some nf) : nf₁.quantifiers = nf₂.quantifiers :=
  quantifiers_eq_of_binop_eq_some h

/-- A successful conjunction witnesses that the operands have equal arities. -/
theorem arity_eq_of_and_eq_some {nf₁ nf₂ nf : NormalFormCode}
    (h : nf₁.and nf₂ = some nf) : nf₁.arity = nf₂.arity :=
  arity_eq_of_binop_eq_some h

/-- A successful conjunction retains the operands' quantifier prefix. -/
theorem quantifiers_and {nf₁ nf₂ nf : NormalFormCode} (h : nf₁.and nf₂ = some nf) :
    nf.quantifiers = nf₁.quantifiers :=
  quantifiers_binop h

/-- A successful conjunction retains the operands' arity. -/
theorem arity_and {nf₁ nf₂ nf : NormalFormCode} (h : nf₁.and nf₂ = some nf) :
    nf.arity = nf₁.arity :=
  arity_binop h

/-- A successful conjunction builds its matrix program from `Code.boolAnd` composed with two
oracle-independent unpairing preprocessors. -/
theorem exists_matrix_and {nf₁ nf₂ nf : NormalFormCode} (h : nf₁.and nf₂ = some nf) :
    ∃ c₁ c₂ : Code,
      nf.matrix = Code.boolAnd (Code.comp nf₁.matrix c₁) (Code.comp nf₂.matrix c₂) ∧
      (∀ (O : ℕ →. ℕ) (l : List ℕ),
        Code.eval O c₁ (encode l) = Part.some (encode
          ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.1) ++
            l.drop nf₁.quantifiers.depth)) ∧
        Code.eval O c₂ (encode l) = Part.some (encode
          ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.2) ++
            l.drop nf₁.quantifiers.depth))) := by
  simpa only [unpairFst_eq, unpairSnd_eq] using exists_matrix_binop h

/-- A successful disjunction witnesses that the operands have equal quantifier prefixes. -/
theorem quantifiers_eq_of_or_eq_some {nf₁ nf₂ nf : NormalFormCode}
    (h : nf₁.or nf₂ = some nf) : nf₁.quantifiers = nf₂.quantifiers :=
  quantifiers_eq_of_binop_eq_some h

/-- A successful disjunction witnesses that the operands have equal arities. -/
theorem arity_eq_of_or_eq_some {nf₁ nf₂ nf : NormalFormCode}
    (h : nf₁.or nf₂ = some nf) : nf₁.arity = nf₂.arity :=
  arity_eq_of_binop_eq_some h

/-- A successful disjunction retains the operands' quantifier prefix. -/
theorem quantifiers_or {nf₁ nf₂ nf : NormalFormCode} (h : nf₁.or nf₂ = some nf) :
    nf.quantifiers = nf₁.quantifiers :=
  quantifiers_binop h

/-- A successful disjunction retains the operands' arity. -/
theorem arity_or {nf₁ nf₂ nf : NormalFormCode} (h : nf₁.or nf₂ = some nf) :
    nf.arity = nf₁.arity :=
  arity_binop h

/-- A successful disjunction builds its matrix program from `Code.boolOr` composed with two
oracle-independent unpairing preprocessors. -/
theorem exists_matrix_or {nf₁ nf₂ nf : NormalFormCode} (h : nf₁.or nf₂ = some nf) :
    ∃ c₁ c₂ : Code,
      nf.matrix = Code.boolOr (Code.comp nf₁.matrix c₁) (Code.comp nf₂.matrix c₂) ∧
      (∀ (O : ℕ →. ℕ) (l : List ℕ),
        Code.eval O c₁ (encode l) = Part.some (encode
          ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.1) ++
            l.drop nf₁.quantifiers.depth)) ∧
        Code.eval O c₂ (encode l) = Part.some (encode
          ((l.take nf₁.quantifiers.depth).map (fun y => y.unpair.2) ++
            l.drop nf₁.quantifiers.depth))) := by
  simpa only [unpairFst_eq, unpairSnd_eq] using exists_matrix_binop h

/-- Conjunction is primitive recursive on normal-form codes. -/
theorem primrec₂_and : Primrec₂ and :=
  primrec₂_binop Code.primrec₂_boolAnd

/-- Disjunction is primitive recursive on normal-form codes. -/
theorem primrec₂_or : Primrec₂ or :=
  primrec₂_binop Code.primrec₂_boolOr

/-- Conjunction preserves validity when it succeeds. -/
theorem IsValid.and {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : nf₁.and nf₂ = some nf) :
    nf.IsValid Z :=
  isValid_binop Code.eval_boolAnd h₁ h₂ h

/-- Disjunction preserves validity when it succeeds. -/
theorem IsValid.or {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : nf₁.or nf₂ = some nf) :
    nf.IsValid Z :=
  isValid_binop Code.eval_boolOr h₁ h₂ h

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
  simpa only [unpairFst_eq, unpairSnd_eq] using
    matrixHolds_binop Code.eval_boolAnd (fun _ _ => Iff.of_eq (Bool.and_eq_true _ _)) h₁ h₂ h hl

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
  simpa only [unpairFst_eq, unpairSnd_eq] using
    matrixHolds_binop Code.eval_boolOr (fun _ _ => Iff.of_eq (Bool.or_eq_true _ _)) h₁ h₂ h hl

/-- Semantic equation for a successful conjunction on lists of the expected arity. -/
theorem evalList_and {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : nf₁.and nf₂ = some nf)
    {xs : List ℕ} (hxs : xs.length = nf₁.arity) :
    nf.EvalList Z xs ↔ nf₁.EvalList Z xs ∧ nf₂.EvalList Z xs :=
  evalList_binop matrixHolds_and QuantifierPrefix.eval_and_unpair_iff h₁ h₂ h hxs

/-- Semantic equation for a successful disjunction on lists of the expected arity. -/
theorem evalList_or {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : nf₁.or nf₂ = some nf)
    {xs : List ℕ} (hxs : xs.length = nf₁.arity) :
    nf.EvalList Z xs ↔ nf₁.EvalList Z xs ∨ nf₂.EvalList Z xs :=
  evalList_binop matrixHolds_or QuantifierPrefix.eval_or_unpair_iff h₁ h₂ h hxs

/-- Semantic equation for a successful conjunction on tuples. -/
theorem holds_and {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : nf₁.and nf₂ = some nf)
    (x : Fin nf.arity → ℕ) :
    nf.Holds Z x ↔
      nf₁.Holds Z (x ∘ Fin.cast (arity_and h).symm) ∧
      nf₂.Holds Z (x ∘ Fin.cast ((arity_and h).trans (arity_eq_of_and_eq_some h)).symm) :=
  holds_binop evalList_and h₁ h₂ h x

/-- Semantic equation for a successful disjunction on tuples. -/
theorem holds_or {Z : Set ℕ} {nf₁ nf₂ nf : NormalFormCode}
    (h₁ : nf₁.IsValid Z) (h₂ : nf₂.IsValid Z) (h : nf₁.or nf₂ = some nf)
    (x : Fin nf.arity → ℕ) :
    nf.Holds Z x ↔
      nf₁.Holds Z (x ∘ Fin.cast (arity_or h).symm) ∨
      nf₂.Holds Z (x ∘ Fin.cast ((arity_or h).trans (arity_eq_of_or_eq_some h)).symm) :=
  holds_binop evalList_or h₁ h₂ h x

end NormalFormCode

end TauCeti.ArithmeticalHierarchy
