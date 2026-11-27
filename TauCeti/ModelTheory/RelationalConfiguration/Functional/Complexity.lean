/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Functional.Coding
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
public import TauCeti.ModelTheory.Infinitary.GraphTranslation.Relationalize
public import TauCeti.Topology.Discrete
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.ModelTheory.Complexity

/-!
# First-order formulas on the functional coding space

On the functional coding space of a language `L` over a discrete carrier `V`, the value of a term
at a fixed valuation is a continuous, so locally constant, function of the configuration: it looks
up finitely many entries of the function table. Hence an atomic formula, and every quantifier-free
formula, defines a clopen set. Over a countable discrete carrier every `L_{ω₁ω}` formula, and so
every first-order formula, defines a set in the Borel σ-algebra of the coding space: the preimage,
under the continuous graph code, of the measurable realization set of the relational translation
of the formula. The realization set of a sentence is invariant under isomorphism, so the models of
a countable theory form an isomorphism-invariant Borel class.

Borel sets are stated with Mathlib's `borel` σ-algebra of the coding space.

## Main results

* `TauCeti.FunctionalConfiguration.continuous_realize_term`: term realization is continuous.
* `FirstOrder.Language.BoundedFormula.IsQF.isClopen_setOf_realize_functionalConfiguration`:
  quantifier-free formulas define clopen sets.
* `TauCeti.FunctionalConfiguration.measurableSet_setOf_realize`: every `L_{ω₁ω}` formula defines
  a Borel set on a countable discrete carrier.
* `TauCeti.FunctionalConfiguration.measurableSet_setOf_realize_boundedFormula`: in particular,
  every first-order formula does.
* `TauCeti.FunctionalConfiguration.realize_sentence_iff_of_isoSetoid`: isomorphic configurations
  satisfy the same sentences.
* `TauCeti.FunctionalConfiguration.measurableSet_setOf_model`: the models of a countable theory
  form a Borel set.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Springer, 1995, §16.C (Borel classes of
  models in the space of countable structures).
-/

public section

universe u v w u'

open FirstOrder FirstOrder.Language MeasureTheory

namespace TauCeti.FunctionalConfiguration

variable {L : Language.{u, v}} {V : Type w}

/-! ### Invariance -/

/-- **Isomorphic configurations satisfy the same sentences.** -/
theorem realize_sentence_iff_of_isoSetoid {F G : FunctionalConfiguration L V}
    (h : isoSetoid L V F G) (φ : L.Sentence) :
    @Sentence.Realize L V F.toStructure φ ↔ @Sentence.Realize L V G.toStructure φ := by
  obtain ⟨e⟩ := isoSetoid_apply.1 h
  exact @StrongHomClass.realize_sentence L V V F.toStructure G.toStructure
    (@Language.Equiv L V V F.toStructure G.toStructure) _ _ e φ

/-- Relabelling by a permutation preserves the sentences satisfied. -/
@[simp]
theorem realize_sentence_perm_smul (σ : Equiv.Perm V) (F : FunctionalConfiguration L V)
    (φ : L.Sentence) :
    @Sentence.Realize L V (σ • F).toStructure φ ↔ @Sentence.Realize L V F.toStructure φ :=
  (realize_sentence_iff_of_isoSetoid
    (isoSetoid_iff_exists_perm_smul_eq.2 ⟨σ, rfl⟩) φ).symm

/-! ### Terms and quantifier-free formulas -/

variable [TopologicalSpace V] [DiscreteTopology V]

/-- **Term realization is continuous.** On a discrete carrier, the value of a term at a fixed
valuation is a continuous, hence locally constant, function of the functional configuration. -/
theorem continuous_realize_term {β : Type u'} (t : L.Term β) (v : β → V) :
    Continuous fun F : FunctionalConfiguration L V => @Term.realize L V F.toStructure β v t := by
  induction t with
  | var => exact continuous_const
  | func f ts ih =>
    simp only [Term.realize_func, toStructure_funMap]
    exact continuous_uncurry_comp_of_discreteTopology
      (fun w => (continuous_apply (arg f w)).comp continuous_table) (continuous_pi ih)

end TauCeti.FunctionalConfiguration

namespace FirstOrder.Language.BoundedFormula

open TauCeti TauCeti.FunctionalConfiguration

variable {L : Language.{u, v}} {V : Type w} [TopologicalSpace V] [DiscreteTopology V]

/-- **Quantifier-free formulas define clopen sets.** On a discrete carrier, the functional
configurations realizing a quantifier-free formula at a fixed valuation form a clopen set. -/
theorem IsQF.isClopen_setOf_realize_functionalConfiguration {α : Type u'} {n : ℕ}
    {φ : L.BoundedFormula α n} (hφ : φ.IsQF) (v : α → V) (xs : Fin n → V) :
    IsClopen {F : FunctionalConfiguration L V | @φ.Realize L V F.toStructure α n v xs} := by
  induction hφ with
  | falsum => simpa only [BoundedFormula.Realize, Set.ofPred_false] using isClopen_empty
  | of_isAtomic hA =>
    induction hA with
    | equal t₁ t₂ =>
      have h : Continuous fun F : FunctionalConfiguration L V =>
          (@Term.realize L V F.toStructure _ (Sum.elim v xs) t₁,
            @Term.realize L V F.toStructure _ (Sum.elim v xs) t₂) :=
        (continuous_realize_term t₁ _).prodMk (continuous_realize_term t₂ _)
      simp only [BoundedFormula.realize_bdEqual]
      exact (isClopen_discrete {p : V × V | p.1 = p.2}).preimage h
    | rel R ts =>
      have h : Continuous fun F : FunctionalConfiguration L V =>
          F.rel.eval (RelationalConfiguration.atom R
            fun i => @Term.realize L V F.toStructure _ (Sum.elim v xs) (ts i)) :=
        continuous_uncurry_comp_of_discreteTopology
          (fun w => (RelationalConfiguration.continuous_eval
            (RelationalConfiguration.atom R w)).comp continuous_rel)
          (continuous_pi fun i => continuous_realize_term (ts i) _)
      simp only [Relations.boundedFormula, BoundedFormula.Realize, toStructure_relMap]
      exact (isClopen_discrete {true}).preimage h
  | imp _ _ ih₁ ih₂ =>
    simp only [BoundedFormula.realize_imp, imp_iff_not_or, Set.ofPred_or, ← Set.compl_ofPred]
    exact ih₁.compl.union ih₂

end FirstOrder.Language.BoundedFormula

/-! ### Borel sets -/

namespace TauCeti.FunctionalConfiguration

variable {L : Language.{u, v}} {V : Type w} [TopologicalSpace V] [DiscreteTopology V]
  [Countable V]

/-- **`L_{ω₁ω}` formulas define Borel sets.** On a countable discrete carrier, the functional
configurations realizing an infinitary formula with countable branching at a fixed valuation form
a Borel set. -/
theorem measurableSet_setOf_realize {α : Type u'} {n : ℕ} (φ : L.BoundedFormulaω α n)
    (v : α → V) (xs : Fin n → V) :
    MeasurableSet[borel (FunctionalConfiguration L V)]
      {F : FunctionalConfiguration L V | @φ.Realize L ℕ α V F.toStructure n v xs} := by
  let : MeasurableSpace (FunctionalConfiguration L V) := borel _
  have : BorelSpace (FunctionalConfiguration L V) := ⟨rfl⟩
  have hg : Measurable (graphCode (L := L) (V := V)) :=
    RelationalConfiguration.measurable_iff.2 fun a =>
      ((RelationalConfiguration.continuous_eval a).comp continuous_graphCode).measurable
  convert hg (RelationalConfiguration.measurableSet_setOf_realize φ.relationalize v xs) using 1
  ext F
  rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq, graphCode_def,
    RelationalConfiguration.toStructure_ofStructure]
  let := F.toStructure
  exact (BoundedFormulaInf.realize_relationalize φ v xs).symm

/-- **First-order formulas define Borel sets.** On a countable discrete carrier, the functional
configurations realizing a first-order formula at a fixed valuation form a Borel set. -/
theorem measurableSet_setOf_realize_boundedFormula {α : Type u'} {n : ℕ}
    (φ : L.BoundedFormula α n) (v : α → V) (xs : Fin n → V) :
    MeasurableSet[borel (FunctionalConfiguration L V)]
      {F : FunctionalConfiguration L V | @φ.Realize L V F.toStructure α n v xs} := by
  convert measurableSet_setOf_realize (BoundedFormula.toInf (ι := ℕ) φ) v xs using 1
  ext F
  let := F.toStructure
  exact (BoundedFormula.realize_toInf φ v xs).symm

/-- The functional configurations satisfying a sentence form a Borel set. -/
theorem measurableSet_setOf_realize_sentence (φ : L.Sentence) :
    MeasurableSet[borel (FunctionalConfiguration L V)]
      {F : FunctionalConfiguration L V | @Sentence.Realize L V F.toStructure φ} :=
  measurableSet_setOf_realize_boundedFormula (φ : L.BoundedFormula Empty 0) default default

/-- **The models of a countable theory form a Borel set** of the functional coding space on a
countable discrete carrier. It is isomorphism invariant by
`TauCeti.FunctionalConfiguration.realize_sentence_iff_of_isoSetoid`. -/
theorem measurableSet_setOf_model {T : L.Theory} (hT : T.Countable) :
    MeasurableSet[borel (FunctionalConfiguration L V)]
      {F : FunctionalConfiguration L V | @Theory.Model L V F.toStructure T} := by
  let : MeasurableSpace (FunctionalConfiguration L V) := borel _
  have : {F : FunctionalConfiguration L V | @Theory.Model L V F.toStructure T} =
      ⋂ φ ∈ T, {F | @Sentence.Realize L V F.toStructure φ} := by
    ext F
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact @Theory.model_iff L V F.toStructure T
  rw [this]
  exact MeasurableSet.biInter hT fun φ _ => measurableSet_setOf_realize_sentence φ

end TauCeti.FunctionalConfiguration
