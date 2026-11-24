/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Complexity
public import Mathlib.Topology.GDelta.Basic
public import TauCeti.ModelTheory.RelationalConfiguration.Theory
public import TauCeti.ModelTheory.RelationalConfiguration.Topology

/-!
# Topological complexity of first-order model classes

In a relational language every term is a variable, so an atomic formula at a fixed valuation either
does not depend on the configuration (an equation between elements of the carrier) or reads a
single coordinate (a relation symbol applied to elements). Atomic conditions are therefore clopen in
the product topology of `RelationalConfiguration L V`, and the syntactic complexity of a first-order
formula bounds the topological complexity of the configurations realizing it:

* a quantifier-free formula defines a clopen set at every valuation;
* a universal formula defines a closed set, an intersection over the carrier of the sets of its
  matrix;
* an existential formula defines an open set;
* on a countable carrier, the universal closure `ψ.alls` of an existential formula `ψ` (a `∀∃`
  formula) defines a Gδ set: an intersection over the countably many tuples of the carrier of open
  sets.

For sentences this describes the model classes `modelsOf φ.toInf` of first-order sentences embedded
in the infinitary logic. In particular the model class of a `∀∃` sentence on a countable carrier is
a Gδ subset of configuration space, and so, by `IsGδ.polishSpace`, a Polish space in its subspace
topology when the language has countably many relation symbols of each arity. The Gδ property of
model classes is closed under binary and countable conjunction, and the model class of a theory all
of whose sentences are universal is closed.

The syntactic hypotheses matter: not every model class is Gδ. In the language of one unary
predicate, the configurations on `ℕ` with finitely many elements in the predicate form a model
class of an `L_{ω₁ω}` sentence that is countable and dense with dense complement, so by the Baire
category theorem it is not Gδ.

## Main results

* `FirstOrder.Language.BoundedFormula.IsQF.isClopen_setOf_realize`,
  `FirstOrder.Language.BoundedFormula.IsUniversal.isClosed_setOf_realize`,
  `FirstOrder.Language.BoundedFormula.IsExistential.isOpen_setOf_realize` and
  `FirstOrder.Language.BoundedFormula.IsExistential.isGδ_setOf_realize_alls`: realization sets of
  quantifier-free, universal, existential and `∀∃` formulas at a fixed valuation.
* `FirstOrder.Language.BoundedFormula.IsQF.isClopen_modelsOf_toInf`,
  `FirstOrder.Language.BoundedFormula.IsUniversal.isClosed_modelsOf_toInf`,
  `FirstOrder.Language.BoundedFormula.IsExistential.isOpen_modelsOf_toInf` and
  `FirstOrder.Language.BoundedFormula.IsExistential.isGδ_modelsOf_toInf_alls`: the corresponding
  model classes of sentences.
* `TauCeti.RelationalConfiguration.isGδ_modelsOf_inf` and
  `TauCeti.RelationalConfiguration.isGδ_modelsOf_iInf`: Gδ model classes are closed under binary
  and countable conjunction.
* `TauCeti.RelationalConfiguration.isClosed_modelsOfTheory`: universal theories have closed model
  classes.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156, Springer,
  1995, §16 (the space of countable structures of a relational language and the logic action).
-/

public section

universe u v w uι u'

open FirstOrder FirstOrder.Language TauCeti TauCeti.RelationalConfiguration

namespace FirstOrder.Language.BoundedFormula

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {α : Type u'} {n : ℕ}

/-- In a relational language, the configurations realizing a quantifier-free formula at a fixed
valuation form a clopen set, on every carrier. -/
theorem IsQF.isClopen_setOf_realize {φ : L.BoundedFormula α n} (hφ : φ.IsQF) (v : α → V)
    (xs : Fin n → V) :
    IsClopen {c : RelationalConfiguration L V | @φ.Realize L V c.toStructure α n v xs} := by
  induction hφ with
  | falsum => simpa only [Realize, Set.ofPred_false] using isClopen_empty
  | of_isAtomic hA =>
    induction hA with
    | equal t₁ t₂ =>
      -- Both terms are variables, so the equation does not depend on the configuration.
      obtain ⟨a, rfl⟩ := t₁.exists_eq_var_of_isRelational
      obtain ⟨b, rfl⟩ := t₂.exists_eq_var_of_isRelational
      by_cases h : Sum.elim v xs a = Sum.elim v xs b <;>
        simp [Term.bdEqual, Realize, h, isClopen_empty, isClopen_univ]
    | rel R ts =>
      -- The arguments are variables, so the relation is read off a single atom.
      choose a ha using fun i => (ts i).exists_eq_var_of_isRelational
      simp only [Relations.boundedFormula, Realize, ha, Term.realize_var, toStructure_relMap]
      exact isClopen_setOf_eval _ true
  | imp _ _ ih₁ ih₂ =>
    simp only [realize_imp, imp_iff_not_or, Set.ofPred_or, ← Set.compl_ofPred]
    exact ih₁.compl.union ih₂

/-- In a relational language, the configurations realizing a universal formula at a fixed valuation
form a closed set, on every carrier. -/
theorem IsUniversal.isClosed_setOf_realize {φ : L.BoundedFormula α n} (hφ : φ.IsUniversal)
    (v : α → V) (xs : Fin n → V) :
    IsClosed {c : RelationalConfiguration L V | @φ.Realize L V c.toStructure α n v xs} := by
  induction hφ with
  | of_isQF h => exact (h.isClopen_setOf_realize v xs).isClosed
  | all _ ih =>
    simp only [realize_all, Set.ofPred_forall]
    exact isClosed_iInter fun x => ih _

/-- In a relational language, the configurations realizing an existential formula at a fixed
valuation form an open set, on every carrier. -/
theorem IsExistential.isOpen_setOf_realize {φ : L.BoundedFormula α n} (hφ : φ.IsExistential)
    (v : α → V) (xs : Fin n → V) :
    IsOpen {c : RelationalConfiguration L V | @φ.Realize L V c.toStructure α n v xs} := by
  induction hφ with
  | of_isQF h => exact (h.isClopen_setOf_realize v xs).isOpen
  | ex _ ih =>
    simp only [realize_ex, Set.ofPred_exists]
    exact isOpen_iUnion fun x => ih _

/-- In a relational language, on a countable carrier, the configurations realizing the universal
closure `ψ.alls` of an existential formula `ψ` (a `∀∃` formula) at a fixed valuation form a Gδ
set. -/
theorem IsExistential.isGδ_setOf_realize_alls [Countable V] {ψ : L.BoundedFormula α n}
    (hψ : ψ.IsExistential) (v : α → V) :
    IsGδ {c : RelationalConfiguration L V | @ψ.alls.Realize L V c.toStructure α v} := by
  simp only [realize_alls, Set.ofPred_forall]
  exact .iInter_of_isOpen fun xs => hψ.isOpen_setOf_realize v xs

/-- In a relational language, the model class of a quantifier-free first-order sentence is clopen,
on every carrier. -/
theorem IsQF.isClopen_modelsOf_toInf {ι : Type uι} {φ : L.Sentence} (hφ : φ.IsQF) :
    IsClopen (modelsOf (V := V) (φ.toInf (ι := ι))) := by
  convert hφ.isClopen_setOf_realize default default using 1
  exact Set.ext fun _ => mem_modelsOf_toInf

/-- In a relational language, the model class of a universal first-order sentence is closed, on
every carrier. -/
theorem IsUniversal.isClosed_modelsOf_toInf {ι : Type uι} {φ : L.Sentence} (hφ : φ.IsUniversal) :
    IsClosed (modelsOf (V := V) (φ.toInf (ι := ι))) := by
  convert hφ.isClosed_setOf_realize default default using 1
  exact Set.ext fun _ => mem_modelsOf_toInf

/-- In a relational language, the model class of an existential first-order sentence is open, on
every carrier. -/
theorem IsExistential.isOpen_modelsOf_toInf {ι : Type uι} {φ : L.Sentence}
    (hφ : φ.IsExistential) : IsOpen (modelsOf (V := V) (φ.toInf (ι := ι))) := by
  convert hφ.isOpen_setOf_realize default default using 1
  exact Set.ext fun _ => mem_modelsOf_toInf

/-- In a relational language, on a countable carrier, the model class of a `∀∃` sentence, the
universal closure `ψ.alls` of an existential formula `ψ`, is a Gδ set of configurations. -/
theorem IsExistential.isGδ_modelsOf_toInf_alls [Countable V] {ι : Type uι}
    {ψ : L.BoundedFormula Empty n} (hψ : ψ.IsExistential) :
    IsGδ (modelsOf (V := V) (ψ.alls.toInf (ι := ι))) := by
  convert hψ.isGδ_setOf_realize_alls (V := V) default using 1
  exact Set.ext fun _ => mem_modelsOf_toInf

end FirstOrder.Language.BoundedFormula

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {ι : Type uι}

/-- The model class of a conjunction of two sentences with Gδ model classes is Gδ. -/
theorem isGδ_modelsOf_inf {φ ψ : L.SentenceInf ι} (hφ : IsGδ (modelsOf (V := V) φ))
    (hψ : IsGδ (modelsOf (V := V) ψ)) : IsGδ (modelsOf (V := V) (φ ⊓ ψ)) := by
  rw [modelsOf_inf]
  exact hφ.inter hψ

/-- The model class of a countable conjunction of sentences with Gδ model classes is Gδ. -/
theorem isGδ_modelsOf_iInf [Countable ι] {φs : ι → L.SentenceInf ι}
    (h : ∀ i, IsGδ (modelsOf (V := V) (φs i))) :
    IsGδ (modelsOf (V := V) (BoundedFormulaInf.iInf φs)) := by
  rw [modelsOf_iInf]
  exact .iInter h

/-- In a relational language, the model class of a first-order theory all of whose sentences are
universal is closed, on every carrier. -/
theorem isClosed_modelsOfTheory {T : L.Theory} (hT : ∀ φ ∈ T, φ.IsUniversal) :
    IsClosed (modelsOfTheory (V := V) T) := by
  rw [modelsOfTheory_eq_biInter]
  exact isClosed_biInter fun φ hφ => (hT φ hφ).isClosed_modelsOf_toInf

end TauCeti.RelationalConfiguration
