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

private theorem length_unpairFst (d : ℕ) (l : List ℕ) : (unpairFst d l).length = l.length := by
  simp [unpairFst]
  omega

private theorem length_unpairSnd (d : ℕ) (l : List ℕ) : (unpairSnd d l).length = l.length := by
  simp [unpairSnd]
  omega

private def idCode : Code :=
  Code.pair Code.left Code.right

private theorem eval_idCode (O : ℕ →. ℕ) (n : ℕ) : Code.eval O idCode n = Part.some n := by
  simp [idCode, Seq.seq]

private def ifZeroCode (c₀ c₁ : Code) : Code :=
  Code.prec c₀ (Code.comp c₁ (Code.pair Code.left (Code.comp Code.left Code.right)))

private theorem eval_ifZeroCode_dom {O : ℕ →. ℕ} {c₀ c₁ : Code}
    (hc₀ : ∀ a, ∃ y, Code.eval O c₀ a = Part.some y)
    (hc₁ : ∀ a m, ∃ y, Code.eval O c₁ (Nat.pair a m) = Part.some y) (a k : ℕ) :
    ∃ y, Code.eval O (ifZeroCode c₀ c₁) (Nat.pair a k) = Part.some y := by
  induction k with
  | zero =>
    rw [ifZeroCode, Code.eval_prec_zero]
    exact hc₀ a
  | succ k ih =>
    obtain ⟨i, hi⟩ := ih
    dsimp only [ifZeroCode] at hi
    rw [ifZeroCode, Code.eval_prec_succ, hi]
    simp [Seq.seq, hc₁ a k]

private theorem eval_ifZeroCode_zero (O : ℕ →. ℕ) (c₀ c₁ : Code) (a : ℕ) :
    Code.eval O (ifZeroCode c₀ c₁) (Nat.pair a 0) = Code.eval O c₀ a := by
  rw [ifZeroCode, Code.eval_prec_zero]

private theorem eval_ifZeroCode_succ {O : ℕ →. ℕ} {c₀ c₁ : Code}
    (hc₀ : ∀ a, ∃ y, Code.eval O c₀ a = Part.some y)
    (hc₁ : ∀ a m, ∃ y, Code.eval O c₁ (Nat.pair a m) = Part.some y) (a m : ℕ) :
    Code.eval O (ifZeroCode c₀ c₁) (Nat.pair a (m + 1)) = Code.eval O c₁ (Nat.pair a m) := by
  obtain ⟨i, hi⟩ := eval_ifZeroCode_dom hc₀ hc₁ a m
  dsimp only [ifZeroCode] at hi
  rw [ifZeroCode, Code.eval_prec_succ, hi]
  simp [Seq.seq]

private def iterCode (init step : Code) : Code :=
  Code.prec init (Code.comp step (Code.comp Code.right Code.right))

private theorem eval_iterCode {O : ℕ →. ℕ} {init step : Code} {g₀ g : ℕ → ℕ}
    (hinit : ∀ a, Code.eval O init a = Part.some (g₀ a))
    (hstep : ∀ s, Code.eval O step s = Part.some (g s)) (a d : ℕ) :
    Code.eval O (iterCode init step) (Nat.pair a d) = Part.some (g^[d] (g₀ a)) := by
  induction d with
  | zero =>
    rw [iterCode, Code.eval_prec_zero, hinit]
    rfl
  | succ d ih =>
    dsimp only [iterCode] at ih
    rw [iterCode, Code.eval_prec_succ, ih]
    simpa [hstep] using
      (Function.iterate_succ_apply' g d (g₀ a)).symm.trans (Function.iterate_succ_apply g d (g₀ a))

private def stepSplit (proj : Code) : Code :=
  ifZeroCode (Code.pair idCode Code.zero)
    (Code.pair
      (Code.comp Code.succ (Code.pair (Code.comp proj (Code.comp Code.left Code.right)) Code.left))
      (Code.comp Code.right Code.right))

private def stepSplitFn (f : ℕ → ℕ) : List ℕ × List ℕ → List ℕ × List ℕ
  | (rl, []) => (rl, [])
  | (rl, a :: l) => (f a :: rl, l)

private theorem eval_stepSplit {O : ℕ →. ℕ} {proj : Code} {f : ℕ → ℕ}
    (hproj : ∀ y, Code.eval O proj y = Part.some (f y)) (s : ℕ) :
    Code.eval O (stepSplit proj) s =
      Part.some (Nat.pair
        (encode (stepSplitFn f (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).1)
        (encode (stepSplitFn f (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).2)) := by
  have hc₀ : ∀ a, ∃ y, Code.eval O (Code.pair idCode Code.zero) a = Part.some y := fun a =>
    ⟨Nat.pair a 0, by simp [eval_idCode, Seq.seq]⟩
  have hc₁ : ∀ a m, ∃ y, Code.eval O
      (Code.pair
        (Code.comp Code.succ
          (Code.pair (Code.comp proj (Code.comp Code.left Code.right)) Code.left))
        (Code.comp Code.right Code.right))
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
  Code.comp
    (ifZeroCode (Code.pair Code.zero idCode)
      (Code.pair (Code.comp Code.right Code.right)
        (Code.comp Code.succ (Code.pair (Code.comp Code.left Code.right) Code.left))))
    (Code.pair Code.right Code.left)

private def stepRevFn : List ℕ × List ℕ → List ℕ × List ℕ
  | ([], l) => ([], l)
  | (b :: rl, l) => (rl, b :: l)

private theorem eval_stepRev (O : ℕ →. ℕ) (s : ℕ) :
    Code.eval O stepRev s =
      Part.some (Nat.pair
        (encode (stepRevFn (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).1)
        (encode (stepRevFn (ofNat (List ℕ) s.unpair.1, ofNat (List ℕ) s.unpair.2)).2)) := by
  have hc₀ : ∀ a, ∃ y, Code.eval O (Code.pair Code.zero idCode) a = Part.some y := fun a =>
    ⟨Nat.pair 0 a, by simp [eval_idCode, Seq.seq]⟩
  have hc₁ : ∀ a m, ∃ y, Code.eval O
      (Code.pair (Code.comp Code.right Code.right)
        (Code.comp Code.succ (Code.pair (Code.comp Code.left Code.right) Code.left)))
      (Nat.pair a m) = Part.some y := fun a m => by
    simp [Seq.seq]
  set rl := ofNat (List ℕ) s.unpair.1
  set l := ofNat (List ℕ) s.unpair.2
  have hs1 : s.unpair.1 = encode rl := (encode_ofNat s.unpair.1).symm
  have hs2 : s.unpair.2 = encode l := (encode_ofNat s.unpair.2).symm
  rw [stepRev, Code.eval_comp]
  have hswap : Code.eval O (Code.pair Code.right Code.left) s =
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

private def mapTakeCode (proj : Code) : Code :=
  let phase1 := Code.comp (iterCode (Code.pair Code.zero idCode) (stepSplit proj))
    (Code.pair Code.right Code.left)
  let phase2 := Code.comp (iterCode idCode stepRev) (Code.pair phase1 Code.left)
  Code.comp Code.right phase2

private theorem eval_mapTakeCode {O : ℕ →. ℕ} {proj : Code} {f : ℕ → ℕ}
    (hproj : ∀ y, Code.eval O proj y = Part.some (f y)) (d : ℕ) (l : List ℕ) :
    Code.eval O (mapTakeCode proj) (Nat.pair d (encode l)) =
      Part.some (encode ((l.take d).map f ++ l.drop d)) := by
  have hinit1 : ∀ a, Code.eval O (Code.pair Code.zero idCode) a =
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
  have hinit2 : ∀ a, Code.eval O idCode a = Part.some a := eval_idCode O
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
      Code.eval O (Code.comp (iterCode (Code.pair Code.zero idCode) (stepSplit proj))
          (Code.pair Code.right Code.left)) (Nat.pair d (encode l)) =
        Part.some (Nat.pair
          (encode (((l.take d).map f).reverseAux [])) (encode (l.drop d))) := by
    rw [Code.eval_comp]
    have hswap : Code.eval O (Code.pair Code.right Code.left) (Nat.pair d (encode l)) =
        Part.some (Nat.pair (encode l) d) := by
      simp [Seq.seq]
    rw [hswap, PFun.some_bind, hiter1, ofNat_encode, hstep1, stepSplitFn_iterate]
  have hlen : (((l.take d).map f).reverseAux []).length ≤ d := by
    simp
  rw [mapTakeCode, Code.eval_comp, Code.eval_comp]
  have hpair2 :
      Code.eval O (Code.pair
          (Code.comp (iterCode (Code.pair Code.zero idCode) (stepSplit proj))
            (Code.pair Code.right Code.left))
          Code.left) (Nat.pair d (encode l)) =
        Part.some (Nat.pair
          (Nat.pair (encode (((l.take d).map f).reverseAux [])) (encode (l.drop d))) d) := by
    simp [Code.eval_pair, hphase1, Seq.seq]
  rw [hpair2, PFun.some_bind, hiter2, PFun.some_bind, id_eq, hstep2, stepRevFn_iterate _ _ _ hlen]
  simp

private def unpairFstBase : Code :=
  mapTakeCode Code.left

private def unpairSndBase : Code :=
  mapTakeCode Code.right

private theorem eval_unpairFstBase (O : ℕ →. ℕ) (d : ℕ) (l : List ℕ) :
    Code.eval O unpairFstBase (Nat.pair d (encode l)) = Part.some (encode (unpairFst d l)) :=
  eval_mapTakeCode (fun y => Code.eval_left y) d l

private theorem eval_unpairSndBase (O : ℕ →. ℕ) (d : ℕ) (l : List ℕ) :
    Code.eval O unpairSndBase (Nat.pair d (encode l)) = Part.some (encode (unpairSnd d l)) :=
  eval_mapTakeCode (fun y => Code.eval_right y) d l

private def unpairFstCode (d : ℕ) : Code :=
  Code.paramCode unpairFstBase d

private def unpairSndCode (d : ℕ) : Code :=
  Code.paramCode unpairSndBase d

/-- Effective conjunction of two normal-form codes with matching quantifier prefix and arity. -/
def and (nf₁ nf₂ : NormalFormCode) : NormalFormCode :=
  ⟨nf₁.quantifiers, nf₁.arity,
    Code.boolAnd
      (Code.comp nf₁.matrix (unpairFstCode nf₁.quantifiers.depth))
      (Code.comp nf₂.matrix (unpairSndCode nf₁.quantifiers.depth))⟩

/-- Effective disjunction of two normal-form codes with matching quantifier prefix and arity. -/
def or (nf₁ nf₂ : NormalFormCode) : NormalFormCode :=
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
            ((Code.primrec_paramCode unpairFstBase).comp
              (QuantifierPrefix.primrec_depth.comp (primrec_quantifiers.comp Primrec.fst))))
          (Code.primrec₂_comp.comp (primrec_matrix.comp Primrec.snd)
            ((Code.primrec_paramCode unpairSndBase).comp
              (QuantifierPrefix.primrec_depth.comp
                (primrec_quantifiers.comp Primrec.fst)))))))).to₂

/-- Disjunction is primitive recursive on normal-form codes. -/
theorem primrec₂_or : Primrec₂ or :=
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
  · rw [unpairFstCode, Code.eval_comp_paramCode, encode_nat, eval_unpairFstBase, PFun.some_bind]
    exact hb₁
  · rw [unpairSndCode, Code.eval_comp_paramCode, encode_nat, eval_unpairSndBase, PFun.some_bind]
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
