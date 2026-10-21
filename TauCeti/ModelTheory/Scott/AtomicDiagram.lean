/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.AtomicType
public import TauCeti.ModelTheory.Infinitary.CodedConnectives

/-!
# Atomic diagrams of finite tuples

`atomicDiagram a` is the countable conjunction of the atomic tests true of `a` and the
negations of the tests false of `a`. For a relational language, a tuple in any other structure
realizes this formula exactly when it has the same atomic type. The tuple occupies bound-variable
slots, with no free variables. Nullary relations are retained even when the tuple is empty.

This is the initial approximation in the construction of characteristic formulas for tuples.
For a finite relation language, `firstOrderAtomicDiagram a` is the same conjunction as a
first-order formula.
The construction follows the atomic-diagram construction in Cameron Freer's
`cameronfreer/infinitary-logic`, `InfinitaryLogic/Scott/AtomicDiagram.lean` at checkpoint
`9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`; here tuples occupy bound positions rather than
free variables. See also Dana Scott, *Logic with denumerably long formulas and finite strings
of quantifiers* (1965).
-/

public section

universe u v w w'

namespace TauCeti

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {n : ℕ}
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- The finitary atomic formula testing equality or a relation on bound-variable positions. -/
def AtomicIdx.toFormula : AtomicIdx L n → L.BoundedFormula Empty n
  | .eq i j => .equal (.var (.inr i)) (.var (.inr j))
  | .rel r f => .rel r (fun i => .var (.inr (f i)))

@[simp]
theorem AtomicIdx.toFormula_eq (i j : Fin n) :
    (AtomicIdx.eq (L := L) i j).toFormula =
      .equal (.var (.inr i)) (.var (.inr j)) := (rfl)

@[simp]
theorem AtomicIdx.toFormula_rel {k : ℕ} (r : L.Relations k) (f : Fin k → Fin n) :
    (AtomicIdx.rel r f).toFormula = .rel r (fun i => .var (.inr (f i))) := (rfl)

/-- The formula for an atomic test realizes precisely that test. -/
@[simp]
theorem AtomicIdx.realize_toFormula (i : AtomicIdx L n) (a : Fin n → M) :
    i.toFormula.Realize Empty.elim a ↔ i.Holds a := by
  cases i <;> simp [BoundedFormula.Realize, Function.comp_def]

section FirstOrder

variable [Finite (Σ k, L.Relations k)]

/-- For a finite relation language, the finite conjunction of the atomic tests true of a tuple
and the negations of the tests false of it. Unlike `atomicDiagram`, this is a first-order
formula. -/
noncomputable def firstOrderAtomicDiagram (a : Fin n → M) : L.BoundedFormula Empty n := by
  classical
  exact BoundedFormula.iInf fun i : AtomicIdx L n =>
    if i.Holds a then i.toFormula else i.toFormula.not

open Classical in
/-- The first-order atomic diagram is the finite conjunction of signed atomic formulas. -/
theorem firstOrderAtomicDiagram_def (a : Fin n → M) :
    firstOrderAtomicDiagram (L := L) a =
      BoundedFormula.iInf fun i : AtomicIdx L n =>
        if i.Holds a then i.toFormula else i.toFormula.not := by
  classical
  rfl

/-- Over a finite relational language, the first-order atomic diagram characterizes
atomic-type agreement in every structure. -/
@[simp]
theorem realize_firstOrderAtomicDiagram_iff_sameAtomicType [L.IsRelational]
    (a : Fin n → M) (v : Empty → N) (b : Fin n → N) :
    (firstOrderAtomicDiagram (L := L) a).Realize v b ↔ SameAtomicType (L := L) a b := by
  classical
  rw [Subsingleton.elim v Empty.elim]
  simp only [firstOrderAtomicDiagram_def, BoundedFormula.realize_iInf, sameAtomicType_def]
  apply forall_congr'
  intro i
  by_cases h : i.Holds a <;> simp [h]

end FirstOrder

variable [Countable (Σ k, L.Relations k)]

/-- The signed conjunction of all equality and relation tests on a tuple's positions.
For a relational language this is its complete atomic diagram. -/
noncomputable def atomicDiagram (a : Fin n → M) : L.BoundedFormulaω Empty n := by
  classical
  exact .iInfAlong (IndexCoding.ofEncodableWith (Encodable.ofCountable (AtomicIdx L n)))
    (fun i => if i.Holds a then i.toFormula.toOmega else i.toFormula.toOmega.not)

open Classical in
/-- The atomic diagram is a coded conjunction of signed atomic formulas. -/
theorem atomicDiagram_def (a : Fin n → M) :
    atomicDiagram (L := L) a =
      .iInfAlong (IndexCoding.ofEncodableWith (Encodable.ofCountable (AtomicIdx L n)))
        (fun i => if i.Holds a then i.toFormula.toOmega else i.toFormula.toOmega.not) := by
  classical
  rfl

/-- Over a relational language, the atomic diagram characterizes atomic-type agreement in
every structure, without a countability assumption on the realizing structure. -/
@[simp]
theorem realize_atomicDiagram_iff_sameAtomicType [L.IsRelational]
    (a : Fin n → M) (b : Fin n → N) :
    (atomicDiagram (L := L) a).Realize Empty.elim b ↔ SameAtomicType (L := L) a b := by
  classical
  simp only [atomicDiagram_def, BoundedFormulaInf.realize_iInfAlong, sameAtomicType_def]
  apply forall_congr'
  intro i
  by_cases h : i.Holds a <;> simp [h]

end TauCeti
