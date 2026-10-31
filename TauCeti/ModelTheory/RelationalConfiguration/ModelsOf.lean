/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Structure
public import TauCeti.ModelTheory.RelationalConfiguration.Topology
import TauCeti.ModelTheory.Syntax

/-!
# Model classes of infinitary sentences

For a relational language `L`, a carrier `V` and an infinitary sentence `φ`, the **model class**
`TauCeti.RelationalConfiguration.modelsOf φ` is the set of configurations on `V` whose decoded
structures satisfy `φ`. Model classes are the basic objects of the descriptive set theory of
countable models: counting the countable models of `φ` is counting the isomorphism classes met by
its model classes on `ℕ` and on each `Fin n`.

On a countable carrier, every infinitary formula with countable branching defines a Borel set of
configurations at each valuation of its variables. In a relational language every term is a
variable, so atomic formulas are cylinders or constant conditions; implication, countable
conjunction and disjunction, and quantification over the countable carrier preserve Borelness.
In particular model classes of `L_{ω₁ω}` sentences are Borel, hence standard Borel subspaces when
the language has countably many relation symbols. Model classes are closed under isomorphism of
the decoded structures, across carriers, and by `Equiv.realize_encodeVia` a structure transported
to any bijective carrier lies in the model class of each sentence it satisfies.

This is the easy direction of the López–Escobar theorem, which conversely presents every
isomorphism-invariant Borel set of configurations on `ℕ` as a model class; see Gao, *Invariant
Descriptive Set Theory*, and Kechris, *Classical Descriptive Set Theory*.

## Main definitions

* `TauCeti.RelationalConfiguration.modelsOf`: the configurations on `V` decoding to models of a
  sentence.

## Main results

* `TauCeti.RelationalConfiguration.modelsOf_inf`, `modelsOf_sup`, `modelsOf_iInf`,
  `modelsOf_iSup`, `modelsOf_not`, `modelsOf_imp`, `modelsOf_top` and `modelsOf_bot`: model
  classes turn the connectives into the Boolean set operations.
* `TauCeti.RelationalConfiguration.measurableSet_setOf_realize`: on a countable carrier, the
  configurations realizing an infinitary formula with countable branching at a fixed valuation
  form a measurable set.
* `TauCeti.RelationalConfiguration.measurableSet_modelsOf`: model classes of such sentences are
  measurable, and `TauCeti.RelationalConfiguration.standardBorelSpace_modelsOf` makes them
  standard Borel.
* `FirstOrder.Language.Equiv.mem_modelsOf_iff`: model classes are invariant under isomorphism of
  the decoded structures.
-/

public section

universe u v w w' uι

open FirstOrder FirstOrder.Language

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {ι : Type uι}

/-- The **model class** of an infinitary sentence: the configurations on `V` whose decoded
structures satisfy it. -/
def modelsOf (φ : L.SentenceInf ι) : Set (RelationalConfiguration L V) :=
  {c | @SentenceInf.Realize L ι φ V c.toStructure}

/-- A configuration lies in the model class of `φ` exactly when its decoded structure satisfies
`φ`. -/
@[simp]
theorem mem_modelsOf {φ : L.SentenceInf ι} {c : RelationalConfiguration L V} :
    c ∈ modelsOf φ ↔ @SentenceInf.Realize L ι φ V c.toStructure :=
  Iff.rfl

/-- The false sentence has no models. -/
@[simp]
theorem modelsOf_bot : modelsOf (V := V) (⊥ : L.SentenceInf ι) = ∅ := by
  ext c
  simp

/-- The true sentence holds in every structure. -/
@[simp]
theorem modelsOf_top : modelsOf (V := V) (⊤ : L.SentenceInf ι) = Set.univ := by
  ext c
  simp

/-- The model class of an implication is the complement of the model class of its hypothesis,
joined with the model class of its conclusion. -/
@[simp]
theorem modelsOf_imp (φ ψ : L.SentenceInf ι) :
    modelsOf (V := V) (φ.imp ψ) = (modelsOf φ)ᶜ ∪ modelsOf ψ := by
  ext c
  simp [imp_iff_not_or]

/-- The model class of a negation is the complement of the model class. -/
@[simp]
theorem modelsOf_not (φ : L.SentenceInf ι) : modelsOf (V := V) φ.not = (modelsOf φ)ᶜ := by
  ext c
  simp

/-- The model class of a conjunction is the intersection of the model classes. -/
@[simp]
theorem modelsOf_inf (φ ψ : L.SentenceInf ι) :
    modelsOf (V := V) (φ ⊓ ψ) = modelsOf φ ∩ modelsOf ψ := by
  ext c
  simp

/-- The model class of a disjunction is the union of the model classes. -/
@[simp]
theorem modelsOf_sup (φ ψ : L.SentenceInf ι) :
    modelsOf (V := V) (φ ⊔ ψ) = modelsOf φ ∪ modelsOf ψ := by
  ext c
  simp

/-- The model class of an infinitary conjunction is the intersection of the model classes. -/
@[simp]
theorem modelsOf_iInf (φs : ι → L.SentenceInf ι) :
    modelsOf (V := V) (BoundedFormulaInf.iInf φs) = ⋂ i, modelsOf (φs i) := by
  ext c
  simp

/-- The model class of an infinitary disjunction is the union of the model classes. -/
@[simp]
theorem modelsOf_iSup (φs : ι → L.SentenceInf ι) :
    modelsOf (V := V) (BoundedFormulaInf.iSup φs) = ⋃ i, modelsOf (φs i) := by
  ext c
  simp

/-- On a countable carrier, the configurations realizing an infinitary formula with countable
branching, at fixed valuations of its free and bound variables, form a measurable set. Neither the
language nor its relation symbols need be countable. -/
theorem measurableSet_setOf_realize [Countable ι] [Countable V] {α : Type*} {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) (v : α → V) (xs : Fin n → V) :
    MeasurableSet {c : RelationalConfiguration L V |
      @BoundedFormulaInf.Realize L ι α V c.toStructure n φ v xs} := by
  induction φ with
  | falsum => simpa only [BoundedFormulaInf.realize_falsum] using MeasurableSet.const False
  | equal t₁ t₂ =>
    -- Both terms are variables, so the equation does not depend on the configuration.
    obtain ⟨a, rfl⟩ := t₁.exists_eq_var_of_isRelational
    obtain ⟨b, rfl⟩ := t₂.exists_eq_var_of_isRelational
    simp only [BoundedFormulaInf.realize_equal, Term.realize_var]
    exact MeasurableSet.const _
  | rel R ts =>
    -- The arguments are variables, so the relation is read off a single atom.
    choose a ha using fun i => (ts i).exists_eq_var_of_isRelational
    simp only [BoundedFormulaInf.realize_rel, ha, Term.realize_var, toStructure_relMap]
    exact measurableSet_setOf_eval _ true
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaInf.realize_imp]
    exact (ihφ xs).imp (ihψ xs)
  | all φ ih =>
    simp only [BoundedFormulaInf.realize_all, Set.ofPred_forall]
    exact .iInter fun y => ih _
  | iSup φs ih =>
    simp only [BoundedFormulaInf.realize_iSup, Set.ofPred_exists]
    exact .iUnion fun i => ih i xs
  | iInf φs ih =>
    simp only [BoundedFormulaInf.realize_iInf, Set.ofPred_forall]
    exact .iInter fun i => ih i xs

/-- On a countable carrier, the model class of an infinitary sentence with countable branching,
in particular of every `L_{ω₁ω}` sentence, is measurable. -/
theorem measurableSet_modelsOf [Countable ι] [Countable V] (φ : L.SentenceInf ι) :
    MeasurableSet (modelsOf (V := V) φ) := by
  simpa only [modelsOf, SentenceInf.realize_def, FormulaInf.realize_def] using
    measurableSet_setOf_realize (V := V) φ Empty.elim default

/-- In a language with countably many relation symbols of each arity, a model class on a countable
carrier is a standard Borel space. -/
instance standardBorelSpace_modelsOf [∀ n, Countable (L.Relations n)] [Countable ι] [Countable V]
    (φ : L.SentenceInf ι) : StandardBorelSpace (modelsOf (V := V) φ) :=
  (measurableSet_modelsOf φ).standardBorel

end TauCeti.RelationalConfiguration

namespace FirstOrder.Language.Equiv

open TauCeti RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {W : Type w'} {ι : Type uι}

/-- Model classes are invariant under isomorphism: configurations on possibly different carriers
with isomorphic decoded structures lie in the same model classes. -/
theorem mem_modelsOf_iff {c : RelationalConfiguration L V} {d : RelationalConfiguration L W}
    (e : @Language.Equiv L V W c.toStructure d.toStructure) (φ : L.SentenceInf ι) :
    c ∈ modelsOf φ ↔ d ∈ modelsOf φ :=
  @StrongHomClass.realize_sentenceInf L ι V W c.toStructure d.toStructure _ _ _ e φ

end FirstOrder.Language.Equiv
