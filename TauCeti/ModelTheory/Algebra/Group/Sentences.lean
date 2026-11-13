/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Algebra.Group.Basic
public import TauCeti.ModelTheory.Algebra.Group.ExistentialUniversal
public import TauCeti.GroupTheory.MalcevEquation
public import Mathlib.ModelTheory.Complexity
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.GroupTheory.Commutator.Basic
import TauCeti.ModelTheory.Term.Constants

/-!
# The nontrivial-centralizer, commutativity and Vaught sentences

This file defines three sentences of the group language, classifies them as existential or
universal, and computes their truth values in an arbitrary group. The first two use named
coefficients; the Vaught sentence has none.

* `FirstOrder.Language.group.nontrivialCentralizerSentence a` is the existential sentence
  `∃ x, x * a * x⁻¹ * a⁻¹ = 1 ∧ x ≠ 1`. A group satisfies it exactly when some nontrivial element
  commutes with the element named `a`, so it holds whenever `a` names a nontrivial element.
* `FirstOrder.Language.group.commutativitySentence A` is the universal sentence
  `∀ x y, x * y * x⁻¹ * y⁻¹ = 1`. A group satisfies it exactly when it is commutative, whatever
  the interpretation of the coefficient names.
* `FirstOrder.Language.group.vaughtSentence` is the universal sentence
  `∀ x y z, x ^ 2 * y ^ 2 * z ^ 2 = 1 → x * y * x⁻¹ * y⁻¹ = 1` without coefficients. A group
  satisfies it exactly when it satisfies Vaught's condition `Group.IsVaught`, so it fails in the
  dihedral group of order `8`.

The existential and universal theories of a group in the language with coefficients are studied by
Kharlampovich and Myasnikov, *Implicit function theorem over free groups*, §2.3 and §3.2, and
*Algebraic geometry over free groups: lifting solutions into generic points*, Definition 9, where
the existential theory is the set of true sentences `∃ x₁ … xₙ, ⋀ uᵢ = 1 ∧ ⋀ vⱼ ≠ 1`;
the nontrivial-centralizer sentence has this form, with one equation and one inequation.
Vaught's condition is the universal sentence (V) of *Implicit function theorem over free groups*,
§3.1, Definition 7; the Vaught sentence is the quasi-identity which, as noted there, is equivalent
to (V) modulo the group axioms.
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

/-! ### Truth values in groups -/

section Realize

attribute [local instance] structureOfGroup

/-- A group, with the coefficient names read through `c`, satisfies
`nontrivialCentralizerSentence a` exactly when some nontrivial element commutes with `c a`. -/
@[simp]
theorem realize_nontrivialCentralizerSentence_iff [Group G] (c : A → G) (a : A) :
    letI := Language.constantsOn.structure c
    G ⊨ nontrivialCentralizerSentence a ↔ ∃ x : G, Commute x (c a) ∧ x ≠ 1 := by
  let := Language.constantsOn.structure c
  simp [nontrivialCentralizerSentence, Sentence.Realize, Formula.Realize, Fin.snoc,
    ← commutatorElement_def, commutatorElement_eq_one_iff_commute]

/-- A nontrivial coefficient commutes with itself, so `nontrivialCentralizerSentence a` holds
whenever `a` names a nontrivial element. -/
theorem realize_nontrivialCentralizerSentence_of_ne_one [Group G] {c : A → G} {a : A}
    (ha : c a ≠ 1) :
    letI := Language.constantsOn.structure c
    G ⊨ nontrivialCentralizerSentence a :=
  (realize_nontrivialCentralizerSentence_iff c a).2 ⟨c a, Commute.refl _, ha⟩

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

end Realize

/-! ### The Vaught sentence -/

open scoped commutatorElement

/-- The *Vaught sentence* `∀ x y z, x ^ 2 * y ^ 2 * z ^ 2 = 1 → x * y * x⁻¹ * y⁻¹ = 1` of the
group language without coefficients, written as the universal sentence saying that no triple
satisfies `x ^ 2 * y ^ 2 * z ^ 2 = 1` and `x * y * x⁻¹ * y⁻¹ ≠ 1`. It is the quasi-identity form
of Vaught's condition: a group satisfies it exactly when it satisfies `Group.IsVaught`. -/
noncomputable def vaughtSentence : Language.group.Sentence :=
  noSolutionSentence (n := 3) {FreeGroup.of 0 ^ 2 * FreeGroup.of 1 ^ 2 * FreeGroup.of 2 ^ 2}
    {⁅FreeGroup.of (0 : Fin 3), FreeGroup.of 1⁆}

/-- The Vaught sentence is the sentence saying that the system `x ^ 2 * y ^ 2 * z ^ 2 = 1`,
`x * y * x⁻¹ * y⁻¹ ≠ 1` has no solution. -/
theorem vaughtSentence_def : vaughtSentence = noSolutionSentence (n := 3)
    {FreeGroup.of 0 ^ 2 * FreeGroup.of 1 ^ 2 * FreeGroup.of 2 ^ 2}
    {⁅FreeGroup.of (0 : Fin 3), FreeGroup.of 1⁆} := (rfl)

/-- The Vaught sentence is universal. -/
theorem isUniversal_vaughtSentence : vaughtSentence.IsUniversal :=
  vaughtSentence_def ▸ isUniversal_noSolutionSentence _ _

section Realize

attribute [local instance] structureOfGroup

/-- A group satisfies the Vaught sentence exactly when it satisfies Vaught's condition. -/
@[simp]
theorem realize_vaughtSentence_iff [Group G] : G ⊨ vaughtSentence ↔ Group.IsVaught G := by
  rw [vaughtSentence_def, realize_noSolutionSentence_singleton, Group.isVaught_iff_commute]
  -- Quantify separately over the three entries of a triple `Fin 3 → G`.
  rw [← FinVec.forall_iff]
  simp [FinVec.Forall, commutatorElement_eq_one_iff_commute]

/-- The Vaught sentence fails in the dihedral group of order `8`. -/
example : ¬DihedralGroup 4 ⊨ vaughtSentence :=
  mt realize_vaughtSentence_iff.1 Group.not_isVaught_dihedralGroup_four

end Realize

end FirstOrder.Language.group
