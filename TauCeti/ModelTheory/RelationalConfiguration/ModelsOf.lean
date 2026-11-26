/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.CodedConnectives
public import TauCeti.ModelTheory.Infinitary.FreeVarSupport
public import TauCeti.ModelTheory.Infinitary.Infinite
public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
import TauCeti.MeasureTheory.MeasurableSpace.Invariants
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
the language has countably many relation symbols. The satisfaction set of a formula depends only on
the free-variable support of the formula and transforms equivariantly under carrier relabelling and
the logic action. Model classes are fixed blocks of the logic action, measurable for the invariant
σ-algebra on countable carriers, and closed under isomorphism across carriers.

This is the easy direction of the López–Escobar theorem, which conversely presents every
isomorphism-invariant Borel set of configurations on `ℕ` as a model class; see Gao, *Invariant
Descriptive Set Theory*, and Kechris, *Classical Descriptive Set Theory*.

## Main definitions

* `TauCeti.RelationalConfiguration.modelsOf`: the configurations on `V` decoding to models of a
  sentence.

## Main results

* `TauCeti.RelationalConfiguration.mem_modelsOf_toInf`: the model class of a first-order sentence
  consists of the configurations satisfying it.
* `TauCeti.RelationalConfiguration.modelsOf_inf`, `modelsOf_sup`, `modelsOf_iInf`,
  `modelsOf_iSup`, `modelsOf_iInfAlong`, `modelsOf_iSupAlong`, `modelsOf_not`, `modelsOf_imp`,
  `modelsOf_top` and `modelsOf_bot`: model classes turn the connectives into the Boolean set
  operations.
* `TauCeti.RelationalConfiguration.setOf_realize_eq_of_eqOn_freeVarSupport`: realization sets
  depend only on the valuation on the free-variable support.
* `TauCeti.RelationalConfiguration.image_relabel_setOf_realize` and
  `TauCeti.RelationalConfiguration.smul_setOf_realize`: realization sets transform equivariantly
  under carrier relabelling and the logic action.
* `TauCeti.RelationalConfiguration.measurableSet_setOf_realize`: on a countable carrier, the
  configurations realizing an infinitary formula with countable branching at a fixed valuation
  form a measurable set.
* `TauCeti.RelationalConfiguration.measurableSet_modelsOf`: model classes of such sentences are
  measurable, `TauCeti.RelationalConfiguration.measurableSet_iInf_invariants_modelsOf` places them
  in the invariant σ-algebra, and
  `TauCeti.RelationalConfiguration.standardBorelSpace_modelsOf` makes them standard Borel.
* `FirstOrder.Language.Equiv.mem_modelsOf_iff`,
  `TauCeti.RelationalConfiguration.smul_modelsOf`,
  `TauCeti.RelationalConfiguration.isFixedBlock_modelsOf`, and
  `TauCeti.RelationalConfiguration.isomorphismInvariant_modelsOf`: model classes are fixed by the
  logic action and invariant under isomorphism of the decoded structures.
-/

public section

universe u v w w' uι uκ

open FirstOrder FirstOrder.Language MeasureTheory
open scoped Pointwise

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

/-- A configuration lies in the model class of a first-order sentence, embedded in the infinitary
logic, exactly when its decoded structure satisfies the sentence. Not a simp lemma: `simp` already
reaches the right side through `mem_modelsOf` and `Sentence.realize_toInf`. -/
theorem mem_modelsOf_toInf {φ : L.Sentence} {c : RelationalConfiguration L V} :
    c ∈ modelsOf (φ.toInf (ι := ι)) ↔ @Sentence.Realize L V c.toStructure φ :=
  @Sentence.realize_toInf L ι φ V c.toStructure

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

/-- On an infinite carrier every configuration satisfies the infinitude sentence. -/
@[simp]
theorem modelsOf_infiniteSentence_of_infinite [Infinite V] :
    modelsOf (V := V) L.infiniteSentence = Set.univ := by
  ext c
  simp only [mem_modelsOf, realize_infiniteSentence_iff, Set.mem_univ, iff_true]
  infer_instance

/-- On a finite carrier no configuration satisfies the infinitude sentence, including on the
empty carrier. -/
@[simp]
theorem modelsOf_infiniteSentence_of_finite [Finite V] :
    modelsOf (V := V) L.infiniteSentence = ∅ := by
  ext c
  simp only [mem_modelsOf, realize_infiniteSentence_iff, Set.mem_empty_iff_false, iff_false]
  exact not_infinite_iff_finite.2 inferInstance

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

/-- The model class of a coded conjunction is the intersection of the model classes of its
conjuncts. -/
@[simp]
theorem modelsOf_iInfAlong {κ : Type uκ} (c : IndexCoding κ ι) (φs : κ → L.SentenceInf ι) :
    modelsOf (V := V) (BoundedFormulaInf.iInfAlong c φs) = ⋂ i, modelsOf (φs i) := by
  ext x
  simp

/-- The model class of a coded disjunction is the union of the model classes of its
disjuncts. -/
@[simp]
theorem modelsOf_iSupAlong {κ : Type uκ} (c : IndexCoding κ ι) (φs : κ → L.SentenceInf ι) :
    modelsOf (V := V) (BoundedFormulaInf.iSupAlong c φs) = ⋃ i, modelsOf (φs i) := by
  ext x
  simp

/-! ### Locality and action equivariance -/

/-- **Locality of satisfaction.** The configurations realizing an infinitary formula depend only on
the values of the free-variable valuation on its free-variable support. -/
theorem setOf_realize_eq_of_eqOn_freeVarSupport {α : Type*} {n : ℕ}
    {φ : L.BoundedFormulaInf ι α n} {v v' : α → V}
    (h : Set.EqOn v v' φ.freeVarSupport) (xs : Fin n → V) :
    {c : RelationalConfiguration L V |
        @BoundedFormulaInf.Realize L ι α V c.toStructure n φ v xs} =
      {c : RelationalConfiguration L V |
        @BoundedFormulaInf.Realize L ι α V c.toStructure n φ v' xs} := by
  ext c
  let := c.toStructure
  exact φ.realize_congr_freeVarSupport h xs

/-- Relabelling along a bijection of carriers transports the realization set of an infinitary
formula by composing both valuations with the bijection. -/
theorem image_relabel_setOf_realize {W : Type w'} (e : V ≃ W) {α : Type*} {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) (v : α → V) (xs : Fin n → V) :
    relabel e ''
        {c : RelationalConfiguration L V |
          @BoundedFormulaInf.Realize L ι α V c.toStructure n φ v xs} =
      {c : RelationalConfiguration L W |
        @BoundedFormulaInf.Realize L ι α W c.toStructure n φ (e ∘ v) (e ∘ xs)} := by
  ext c
  refine ⟨?_, fun hc => ⟨relabel e.symm c, ?_, relabel_relabel_symm e c⟩⟩
  · rintro ⟨d, hd, rfl⟩
    exact (realize_relabel e d φ v xs).2 hd
  · rw [Set.mem_ofPred_eq, ← realize_relabel e (relabel e.symm c) φ v xs, relabel_relabel_symm]
    exact hc

/-- **Equivariance of satisfaction.** The logic action of a permutation `σ` transforms the
realization set of an infinitary formula by composing the free and bound valuations with `σ`. -/
@[simp]
theorem smul_setOf_realize (σ : Equiv.Perm V) {α : Type*} {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) (v : α → V) (xs : Fin n → V) :
    σ • {c : RelationalConfiguration L V |
        @BoundedFormulaInf.Realize L ι α V c.toStructure n φ v xs} =
      {c : RelationalConfiguration L V |
        @BoundedFormulaInf.Realize L ι α V c.toStructure n φ (σ ∘ v) (σ ∘ xs)} := by
  rw [← Set.image_smul]
  simpa only [← relabel_perm] using image_relabel_setOf_realize σ φ v xs

/-- Relabelling along a bijection of carriers maps the model class of an infinitary sentence on `V`
onto its model class on `W`. -/
@[simp]
theorem image_relabel_modelsOf {W : Type w'} (e : V ≃ W) (φ : L.SentenceInf ι) :
    relabel e '' modelsOf (V := V) φ = modelsOf (V := W) φ := by
  ext c
  refine ⟨?_, fun hc => ⟨relabel e.symm c, ?_, relabel_relabel_symm e c⟩⟩
  · rintro ⟨d, hd, rfl⟩
    exact mem_modelsOf.2 ((realize_sentenceInf_relabel e d φ).2 hd)
  · rw [mem_modelsOf, ← realize_sentenceInf_relabel e (relabel e.symm c) φ, relabel_relabel_symm]
    exact hc

/-- Every permutation of the carrier fixes the model class of every infinitary sentence. -/
@[simp]
theorem smul_modelsOf (σ : Equiv.Perm V) (φ : L.SentenceInf ι) :
    σ • modelsOf (V := V) φ = modelsOf (V := V) φ := by
  rw [← Set.image_smul]
  simpa only [← relabel_perm] using image_relabel_modelsOf σ φ

/-- Model classes of infinitary sentences are fixed blocks of the logic action, on any carrier and
for any branching index. -/
theorem isFixedBlock_modelsOf (φ : L.SentenceInf ι) :
    MulAction.IsFixedBlock (Equiv.Perm V) (modelsOf (V := V) φ) :=
  fun σ => smul_modelsOf σ φ

/-! ### Borelness and invariance -/

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

/-- On a countable carrier, the model class of an infinitary sentence with countable branching is
measurable for the invariant σ-algebra of the logic action. -/
theorem measurableSet_iInf_invariants_modelsOf [Countable ι] [Countable V] (φ : L.SentenceInf ι) :
    MeasurableSet[⨅ σ : Equiv.Perm V,
        MeasurableSpace.invariants (fun c : RelationalConfiguration L V => σ • c)]
      (modelsOf (V := V) φ) :=
  TauCeti.measurableSet_iInf_invariants_iff.2 ⟨measurableSet_modelsOf φ, isFixedBlock_modelsOf φ⟩

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

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {ι : Type uι}

/-- Model classes of infinitary sentences are isomorphism invariant, on any carrier and for any
branching index. -/
theorem isomorphismInvariant_modelsOf (φ : L.SentenceInf ι) :
    IsomorphismInvariant (modelsOf (V := V) φ) :=
  isomorphismInvariant_iff.2 fun _ _ h hc => by
    obtain ⟨e⟩ := isoSetoid_apply.1 h
    exact (e.mem_modelsOf_iff φ).1 hc

end TauCeti.RelationalConfiguration
