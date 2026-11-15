/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Algebra.Group.Sentences
import TauCeti.ModelTheory.Semantics
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Truth values of existential and universal sentences in free groups

The existential theory of a group `G` with coefficients is the set of existential sentences of
the group language with named coefficients that hold in `G`, and dually for the universal theory.
This file computes the truth values of three such sentences in the free group `F(A)`, with the
basis letters as coefficients.

* The existential sentence `FirstOrder.Language.group.nontrivialCentralizerSentence a`, saying
  that some nontrivial element commutes with `a`, holds in `F(A)` for every basis letter `a`.
* The universal sentence `FirstOrder.Language.group.commutativitySentence A`, saying that any two
  elements commute, holds in `F(A)` exactly when `A` has at most one element: the truth value
  depends on the rank.
* The sentence `∃ x, x = x` holds in every nonempty structure
  (`FirstOrder.Language.Sentence.realize_ex_bdEqual_self_iff`); an example records it in the
  trivial group `F(∅)`.

The existential and universal theories of a group in the language with coefficients are studied by
Kharlampovich and Myasnikov, *Implicit function theorem over free groups*, §2.3 and §3.2, and
*Algebraic geometry over free groups: lifting solutions into generic points*, Definition 9, where
the existential theory is the set of true sentences `∃ x₁ … xₙ, ⋀ uᵢ = 1 ∧ ⋀ vⱼ ≠ 1`.
-/

public section

namespace FirstOrder.Language.group

open FirstOrder TauCeti TauCeti.Group

variable {A : Type*}

attribute [local instance] structureOfGroup

/-- In the free group on `A`, with the basis letters as coefficients, some nontrivial element
commutes with each basis letter `a`, namely `a` itself. -/
theorem realize_nontrivialCentralizerSentence_freeGroup (a : A) :
    letI := Language.constantsOn.structure (FreeGroup.of : A → FreeGroup A)
    FreeGroup A ⊨ nontrivialCentralizerSentence a :=
  realize_nontrivialCentralizerSentence_of_ne_one (FreeGroup.of_ne_one a)

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
  exact (Sentence.realize_ex_bdEqual_self_iff _).2 inferInstance

end FirstOrder.Language.group
