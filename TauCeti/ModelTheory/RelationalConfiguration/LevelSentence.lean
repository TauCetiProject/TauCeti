/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Setoid.Basic
public import TauCeti.ModelTheory.RelationalConfiguration.BackAndForth
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
public import TauCeti.ModelTheory.Scott.Formula
import TauCeti.ModelTheory.BackAndForth.Karp

/-!
# Back-and-forth levels are model classes

For a configuration `c` on a countable carrier `V`, in a relational language with countably many
relation symbols, and a countable ordinal `α`, the sentence `c.scottSentenceAtLevel α` is the
canonical Scott formula `scottFormula` of the empty tuple of the structure decoded from `c`, read
as a sentence. A structure satisfies it exactly when its empty tuple is back-and-forth equivalent
to that of `c` at depth `α`. Hence the `α`-class `{d | bfEquivSetoid L V α c d}` of `c` is the
model class of `c.scottSentenceAtLevel α`, and the model class depends only on that class.

So below `ω₁` every back-and-forth class of configurations is cut out by a single sentence of
`L_{ω₁ω}`. Sentence cuts of a model class therefore include its cuts by level classes, which is
what lets counting arguments split a class of countable models along a back-and-forth level using
only sentences, as in the analysis of minimal counterexamples to Vaught's conjecture.

Conversely, for each sentence with countable branching, back-and-forth equivalence at every level
from its quantifier rank on preserves satisfaction of it, and that rank is countable. So the model
class of such a sentence is a union of level classes from some countable level on. This needs no
countability of the carrier or of the vocabulary.

## Main definitions

* `TauCeti.RelationalConfiguration.scottSentenceAtLevel c α`: the Scott formula at level `α` of
  the empty tuple of the structure decoded from `c`, as a sentence.

## Main results

* `TauCeti.RelationalConfiguration.realize_scottSentenceAtLevel`: below `ω₁`, a structure of any
  cardinality, in any universe, satisfies `c.scottSentenceAtLevel α` exactly when its empty tuple
  is back-and-forth equivalent at depth `α` to that of `c`.
* `TauCeti.RelationalConfiguration.modelsOf_scottSentenceAtLevel`: below `ω₁`, the model class of
  `c.scottSentenceAtLevel α` on the carrier of `c` is the `bfEquivSetoid L V α`-class of `c`.
* `TauCeti.RelationalConfiguration.modelsOf_scottSentenceAtLevel_eq_iff`: two configurations have
  the same level-`α` model class exactly when they are `α`-equivalent.
* `TauCeti.RelationalConfiguration.exists_bfLevel_saturated_modelsOf`: for each sentence with
  countable branching, back-and-forth equivalence from some countable level on preserves
  satisfaction of it.

## References

* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Lemma XII.5
  (level classes are defined by sentences), here in the one-element back-and-forth convention of
  `TauCeti.BFEquiv`.
* The statement follows `modelsOf_scottSentenceAt` in Cameron Freer's
  `cameronfreer/infinitary-logic` at checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  `InfinitaryLogic/Descriptive/MinimallyUncountable.lean` (Apache-2.0).
-/

public section

universe u v w w' o uι

open FirstOrder FirstOrder.Language
open scoped Ordinal

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ k, L.Relations k)]
variable {V : Type w} [Countable V]

/-- The **Scott sentence at level `α`** of a configuration `c`: the canonical Scott formula at
level `α` of the empty tuple of the structure decoded from `c`, read as a sentence. Below `ω₁` its
models are the structures back-and-forth equivalent to `c` at depth `α`. -/
noncomputable def scottSentenceAtLevel (c : RelationalConfiguration L V) (α : Ordinal.{o}) :
    L.Sentenceω :=
  @scottFormula L _ V c.toStructure _ 0 Fin.elim0 α

/-- The Scott sentence at level `α` of `c` is the Scott formula of the empty tuple of the decoded
structure. -/
theorem scottSentenceAtLevel_def (c : RelationalConfiguration L V) (α : Ordinal.{o}) :
    c.scottSentenceAtLevel α = @scottFormula L _ V c.toStructure _ 0 Fin.elim0 α :=
  (rfl)

/-- Below `ω₁`, a structure of any cardinality, in any universe, satisfies the Scott sentence at
level `α` of `c` exactly when its empty tuple is back-and-forth equivalent at depth `α` to that of
the structure decoded from `c`. -/
@[simp]
theorem realize_scottSentenceAtLevel (c : RelationalConfiguration L V) {α : Ordinal.{o}}
    (hα : α < ω₁) (N : Type w') [L.Structure N] :
    SentenceInf.Realize (c.scottSentenceAtLevel α) N ↔
      @BFEquiv L _ V N c.toStructure _ α 0 Fin.elim0 Fin.elim0 := by
  rw [scottSentenceAtLevel_def, SentenceInf.realize_def, FormulaInf.realize_def,
    Subsingleton.elim (default : Fin 0 → N) Fin.elim0]
  let := c.toStructure
  exact realize_scottFormula_iff_bfEquiv (Fin.elim0 : Fin 0 → V) (Fin.elim0 : Fin 0 → N) hα

/-- Below `ω₁`, a configuration on any carrier lies in the model class of the Scott sentence at
level `α` of `c` exactly when the empty tuples of the two decoded structures are back-and-forth
equivalent at depth `α`. -/
theorem mem_modelsOf_scottSentenceAtLevel (c : RelationalConfiguration L V) {α : Ordinal.{o}}
    (hα : α < ω₁) {W : Type w'} {d : RelationalConfiguration L W} :
    d ∈ modelsOf (c.scottSentenceAtLevel α) ↔
      @BFEquiv L _ V W c.toStructure d.toStructure α 0 Fin.elim0 Fin.elim0 :=
  mem_modelsOf.trans (@realize_scottSentenceAtLevel L _ _ V _ c α hα W d.toStructure)

/-- **Level classes are model classes.** Below `ω₁`, the configurations on `V` satisfying the
Scott sentence at level `α` of `c` are exactly those `α`-equivalent to `c`. -/
theorem modelsOf_scottSentenceAtLevel (c : RelationalConfiguration L V) {α : Ordinal.{o}}
    (hα : α < ω₁) :
    modelsOf (c.scottSentenceAtLevel α) = {d | bfEquivSetoid L V α c d} := by
  ext d
  exact (mem_modelsOf_scottSentenceAtLevel c hα).trans bfEquivSetoid_apply.symm

/-- Below `ω₁`, a configuration satisfies its own Scott sentence at level `α`. -/
theorem self_mem_modelsOf_scottSentenceAtLevel (c : RelationalConfiguration L V)
    {α : Ordinal.{o}} (hα : α < ω₁) : c ∈ modelsOf (c.scottSentenceAtLevel α) := by
  rw [modelsOf_scottSentenceAtLevel c hα]
  exact (bfEquivSetoid L V α).refl c

/-- Below `ω₁`, two configurations on `V` have the same level-`α` model class exactly when they
are `α`-equivalent, so the model class of `c.scottSentenceAtLevel α` depends exactly on the
`α`-class of `c`. -/
theorem modelsOf_scottSentenceAtLevel_eq_iff {c d : RelationalConfiguration L V}
    {α : Ordinal.{o}} (hα : α < ω₁) :
    modelsOf (V := V) (c.scottSentenceAtLevel α) = modelsOf (d.scottSentenceAtLevel α) ↔
      bfEquivSetoid L V α c d := by
  have hclass (x : RelationalConfiguration L V) :
      {e | bfEquivSetoid L V α x e} = {e | bfEquivSetoid L V α e x} :=
    Set.ext fun _ => Setoid.comm' _
  rw [modelsOf_scottSentenceAtLevel c hα, modelsOf_scottSentenceAtLevel d hα, hclass, hclass]
  exact Setoid.ofPred_rel_eq_iff

end TauCeti.RelationalConfiguration

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational]

/-- **Saturation of a sentence.** For each sentence `θ` with countable branching there is a
countable level `α` such that configurations on `V` that are back-and-forth equivalent at any level
`β ≥ α` agree on `θ`. The level is the quantifier rank of `θ`, which is countable; no countability
of the carrier or of the vocabulary is needed. -/
theorem exists_bfLevel_saturated_modelsOf {V : Type w} {ι : Type uι} [Countable ι]
    (θ : L.SentenceInf ι) :
    ∃ α : Ordinal.{o}, α < ω₁ ∧ ∀ β ≥ α, ∀ c d : RelationalConfiguration L V,
      bfEquivSetoid L V β c d → (c ∈ modelsOf θ ↔ d ∈ modelsOf θ) := by
  -- the quantifier rank of `θ` is countable, so it is the lift of a countable level `α`
  have hθ : Ordinal.lift.{o} θ.qrank ≤ Ordinal.lift.{uι} (ω₁ : Ordinal.{o}) := by
    simpa only [Ordinal.lift_omega, Ordinal.lift_one] using
      Ordinal.lift_le.{o}.2 (BoundedFormulaInf.qrank_lt_omega_one θ).le
  obtain ⟨α, hα⟩ := Ordinal.mem_range_lift_of_le hθ
  refine ⟨α, ?_, fun β hβ c d hcd => ?_⟩
  · rw [← Ordinal.lift_lt.{uι}, hα]
    simpa only [Ordinal.lift_omega, Ordinal.lift_one] using
      Ordinal.lift_lt.{o}.2 (BoundedFormulaInf.qrank_lt_omega_one θ)
  · have h := @BFEquiv.realize_iff_of_qrank_le L V V c.toStructure d.toStructure _ ι 0 θ β
      Fin.elim0 Fin.elim0 (bfEquivSetoid_apply.1 hcd) (hα ▸ Ordinal.lift_le.2 hβ)
      Empty.elim Empty.elim
    simpa only [mem_modelsOf, SentenceInf.realize_def, FormulaInf.realize_def,
      Subsingleton.elim default (Fin.elim0 : Fin 0 → V),
      Subsingleton.elim default (Empty.elim : Empty → V)] using h

end TauCeti.RelationalConfiguration
