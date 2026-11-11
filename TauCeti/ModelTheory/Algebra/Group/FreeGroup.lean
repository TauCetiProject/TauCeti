/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Algebra.Group.Basic
public import TauCeti.ModelTheory.Semantics
public import Mathlib.ModelTheory.Complexity
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Truth values of existential and universal sentences in free groups

The existential theory of a group `G` with coefficients is the set of existential sentences of
the group language with named coefficients that hold in `G`, and dually for the universal theory.
This file decides membership for three sentences in the free group `F(A)`, with the basis letters
as coefficients.

* `FirstOrder.Language.group.nontrivialCentralizerSentence a` is the existential sentence
  `∃ x, x * a * x⁻¹ * a⁻¹ = 1 ∧ x ≠ 1`. It holds whenever the coefficient `a` is interpreted by a
  nontrivial element, in particular in `F(A)` for a basis letter `a`.
* `FirstOrder.Language.group.commutativitySentence A` is the universal sentence
  `∀ x y, x * y * x⁻¹ * y⁻¹ = 1`. It holds exactly in the commutative groups, so it holds in
  `F(A)` exactly when `A` has at most one element: the truth value depends on the rank.
* The existential sentence `∃ x, x = x` holds in every nonempty structure, in particular in the
  trivial group.

The existential and universal theories of a group in the language with coefficients are those of
Kharlampovich and Myasnikov, *Implicit function theorem over free groups*, §2.3 and §3.2, and
*Algebraic geometry over free groups: lifting solutions into generic points*, Definition 9.
-/

public section

namespace FirstOrder.Language.group

open FirstOrder TauCeti TauCeti.Group

variable {A G : Type*}

/-! ### The sentences -/

/-- The existential sentence `∃ x, x * a * x⁻¹ * a⁻¹ = 1 ∧ x ≠ 1` of the group language with
coefficient names `A`: some nontrivial element commutes with the coefficient named `a`. -/
def nontrivialCentralizerSentence (a : A) : Language.group[[A]].Sentence :=
  ∃' ((((&0 : Language.group[[A]].Term (Empty ⊕ Fin 1)) * (Language.group.con a).term * (&0)⁻¹ *
      ((Language.group.con a).term)⁻¹) =' 1) ⊓
    ∼((&0 : Language.group[[A]].Term (Empty ⊕ Fin 1)) =' 1))

/-- The sentence `nontrivialCentralizerSentence a` is existential. -/
theorem isExistential_nontrivialCentralizerSentence (a : A) :
    (nontrivialCentralizerSentence a).IsExistential :=
  ((BoundedFormula.IsAtomic.equal _ _).isQF.inf
    (BoundedFormula.IsAtomic.equal _ _).isQF.not).isExistential.ex

/-- The universal sentence `∀ x y, x * y * x⁻¹ * y⁻¹ = 1` of the group language with coefficient
names `A`: any two elements commute. -/
def commutativitySentence (A : Type*) : Language.group[[A]].Sentence :=
  ∀' ∀' (((&0 : Language.group[[A]].Term (Empty ⊕ Fin 2)) * &1 * (&0)⁻¹ * (&1)⁻¹) =' 1)

/-- The sentence `commutativitySentence A` is universal. -/
theorem isUniversal_commutativitySentence (A : Type*) : (commutativitySentence A).IsUniversal :=
  (BoundedFormula.IsAtomic.equal _ _).isQF.isUniversal.all.all

/-! ### Truth values in groups and in free groups -/

section Realize

attribute [local instance] structureOfGroup

/-- A group, with the coefficient names read through `c`, satisfies
`nontrivialCentralizerSentence a` exactly when some nontrivial element commutes with `c a`. -/
@[simp]
theorem realize_nontrivialCentralizerSentence_iff [Group G] (c : A → G) (a : A) :
    letI := Language.constantsOn.structure c
    G ⊨ nontrivialCentralizerSentence a ↔ ∃ x : G, Commute x (c a) ∧ x ≠ 1 := by
  let := Language.constantsOn.structure c
  -- The coefficient name `a` is interpreted by `c a`, by definition of `constantsOn.structure`.
  have hc : ((Language.group.con a : Language.group[[A]].Constants) : G) = c a := rfl
  simp [nontrivialCentralizerSentence, Sentence.Realize, Formula.Realize, Fin.snoc, hc,
    ← commutatorElement_def, commutatorElement_eq_one_iff_commute]

/-- A nontrivial coefficient commutes with itself, so `nontrivialCentralizerSentence a` holds
whenever `a` names a nontrivial element. -/
theorem realize_nontrivialCentralizerSentence_of_ne_one [Group G] {c : A → G} {a : A}
    (ha : c a ≠ 1) :
    letI := Language.constantsOn.structure c
    G ⊨ nontrivialCentralizerSentence a :=
  (realize_nontrivialCentralizerSentence_iff c a).2 ⟨c a, Commute.refl _, ha⟩

/-- In the free group on `A`, with the basis letters as coefficients, some nontrivial element
commutes with each basis letter `a`, namely `a` itself. -/
theorem realize_nontrivialCentralizerSentence_freeGroup (a : A) :
    letI := Language.constantsOn.structure (FreeGroup.of : A → FreeGroup A)
    FreeGroup A ⊨ nontrivialCentralizerSentence a :=
  realize_nontrivialCentralizerSentence_of_ne_one (FreeGroup.of_ne_one a)

/-- A group satisfies `commutativitySentence A` exactly when it is commutative, whatever the
interpretation `c` of the coefficient names. -/
@[simp]
theorem realize_commutativitySentence_iff [Group G] (c : A → G) :
    letI := Language.constantsOn.structure c
    G ⊨ commutativitySentence A ↔ IsMulCommutative G := by
  let := Language.constantsOn.structure c
  simp [commutativitySentence, Sentence.Realize, Formula.Realize, Fin.snoc,
    ← commutatorElement_def, commutatorElement_eq_one_iff_commute, isMulCommutative_iff,
    commute_iff_eq]

/-- The free group on `A`, with the basis letters as coefficients, satisfies
`commutativitySentence A` exactly when `A` has at most one element. So the sentence fails in
`F(a, b)` and holds in the free groups of rank one and rank zero. -/
theorem realize_commutativitySentence_freeGroup_iff :
    letI := Language.constantsOn.structure (FreeGroup.of : A → FreeGroup A)
    FreeGroup A ⊨ commutativitySentence A ↔ Subsingleton A :=
  (realize_commutativitySentence_iff FreeGroup.of).trans FreeGroup.isMulCommutative_iff_subsingleton

/-- The commutativity sentence fails in the free group on two letters. -/
example :
    letI := Language.constantsOn.structure (FreeGroup.of : Fin 2 → FreeGroup (Fin 2))
    ¬FreeGroup (Fin 2) ⊨ commutativitySentence (Fin 2) :=
  mt realize_commutativitySentence_freeGroup_iff.1 (not_subsingleton (Fin 2))

/-- The commutativity sentence holds in the free group on one letter. -/
example :
    letI := Language.constantsOn.structure (FreeGroup.of : Unit → FreeGroup Unit)
    FreeGroup Unit ⊨ commutativitySentence Unit :=
  realize_commutativitySentence_freeGroup_iff.2 inferInstance

/-- The commutativity sentence holds in the free group of rank zero. -/
example :
    letI := Language.constantsOn.structure (FreeGroup.of : Empty → FreeGroup Empty)
    FreeGroup Empty ⊨ commutativitySentence Empty :=
  realize_commutativitySentence_freeGroup_iff.2 inferInstance

/-- The existential sentence `∃ x, x = x` holds in the trivial group, the free group of rank
zero. -/
example :
    letI := Language.constantsOn.structure (FreeGroup.of : Empty → FreeGroup Empty)
    FreeGroup Empty ⊨
      (∃' ((&0 : Language.group[[Empty]].Term (Empty ⊕ Fin 1)) =' &0) :
        Language.group[[Empty]].Sentence) := by
  let := Language.constantsOn.structure (FreeGroup.of : Empty → FreeGroup Empty)
  exact Sentence.realize_ex_bdEqual_self_iff.2 inferInstance

end Realize

end FirstOrder.Language.group
