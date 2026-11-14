/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
import TauCeti.MeasureTheory.Measure.BooleanPartition

/-!
# Truth sequences of countable lists of sentences

For a relational language `L`, a carrier `V` and a countable list `θ : ℕ → L.SentenceInf ι` of
infinitary sentences, the **truth sequence** `TauCeti.RelationalConfiguration.sentenceTheory θ c`
of a configuration `c` on `V` records, at each `n`, whether the decoded structure of `c` satisfies
`θ n`. Its `n`-th coordinate is `true` exactly when `c` lies in the model class `modelsOf (θ n)`.

On a countable carrier, for sentences with countable branching, the truth sequence is a measurable
map into Cantor space, since each coordinate reads off a Borel model class. It is invariant under
isomorphism of the decoded structures, across carriers, because model classes are. Truth
sequences are the observables through which countably many sentences see a set of
configurations.

## Main definitions

* `TauCeti.RelationalConfiguration.sentenceTheory`: the truth sequence of a list of sentences at
  a configuration.

## Main results

* `TauCeti.RelationalConfiguration.sentenceTheory_eq_true_iff` and
  `TauCeti.RelationalConfiguration.sentenceTheory_eq_false_iff`: the `n`-th coordinate is `true`
  exactly when the configuration is a model of `θ n`.
* `TauCeti.RelationalConfiguration.sentenceTheory_eq_iff`: two configurations have the same truth
  sequence exactly when they lie in the same model classes of the list.
* `TauCeti.RelationalConfiguration.measurable_sentenceTheory`: on a countable carrier the truth
  sequence is measurable.
* `FirstOrder.Language.Equiv.sentenceTheory_eq` and
  `TauCeti.RelationalConfiguration.sentenceTheory_eq_of_isoSetoid`: configurations with isomorphic
  decoded structures have the same truth sequence; in particular relabelling by a permutation of
  the carrier preserves it (`TauCeti.RelationalConfiguration.sentenceTheory_perm_smul`).
-/

public section

universe u v w w' uι

open FirstOrder FirstOrder.Language

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {W : Type w'} {ι : Type uι}

open Classical in
/-- The **truth sequence** of a countable list of sentences at a configuration: its `n`-th
coordinate records whether the decoded structure satisfies `θ n`. -/
noncomputable def sentenceTheory (θ : ℕ → L.SentenceInf ι) (c : RelationalConfiguration L V) :
    ℕ → Bool :=
  fun n => decide (c ∈ modelsOf (θ n))

/-- The `n`-th coordinate of the truth sequence is `true` exactly when the configuration lies in
the model class of `θ n`. -/
@[simp]
theorem sentenceTheory_eq_true_iff {θ : ℕ → L.SentenceInf ι} {c : RelationalConfiguration L V}
    {n : ℕ} : sentenceTheory θ c n = true ↔ c ∈ modelsOf (θ n) := by
  simp [sentenceTheory]

open Classical in
/-- The `n`-th coordinate of the truth sequence is the decision of membership in the model class of
`θ n`. -/
theorem sentenceTheory_apply (θ : ℕ → L.SentenceInf ι) (c : RelationalConfiguration L V) (n : ℕ) :
    sentenceTheory θ c n = decide (c ∈ modelsOf (θ n)) :=
  (rfl)

/-- The `n`-th coordinate of the truth sequence is `false` exactly when the configuration lies
outside the model class of `θ n`. -/
@[simp]
theorem sentenceTheory_eq_false_iff {θ : ℕ → L.SentenceInf ι} {c : RelationalConfiguration L V}
    {n : ℕ} : sentenceTheory θ c n = false ↔ c ∉ modelsOf (θ n) := by
  simp [sentenceTheory]

/-- Two configurations, possibly on different carriers, have the same truth sequence exactly when
they lie in the same model classes of the list. -/
theorem sentenceTheory_eq_iff {θ : ℕ → L.SentenceInf ι} {c : RelationalConfiguration L V}
    {d : RelationalConfiguration L W} :
    sentenceTheory θ c = sentenceTheory θ d ↔ ∀ n, (c ∈ modelsOf (θ n) ↔ d ∈ modelsOf (θ n)) := by
  refine funext_iff.trans (forall_congr' fun n => ?_)
  rw [Bool.eq_iff_iff, sentenceTheory_eq_true_iff, sentenceTheory_eq_true_iff]

/-- On a countable carrier, the truth sequence of a list of sentences with countable branching is
a measurable map into Cantor space: each coordinate reads off a measurable model class. -/
@[fun_prop]
theorem measurable_sentenceTheory [Countable ι] [Countable V] (θ : ℕ → L.SentenceInf ι) :
    Measurable (sentenceTheory (V := V) θ) :=
  TauCeti.measurable_pi_decide_mem fun n => measurableSet_modelsOf (V := V) (θ n)

end TauCeti.RelationalConfiguration

namespace FirstOrder.Language.Equiv

open TauCeti RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {W : Type w'} {ι : Type uι}

/-- **Isomorphism invariance.** Configurations, on possibly different carriers, with isomorphic
decoded structures have the same truth sequence. -/
theorem sentenceTheory_eq {c : RelationalConfiguration L V} {d : RelationalConfiguration L W}
    (e : @Language.Equiv L V W c.toStructure d.toStructure) (θ : ℕ → L.SentenceInf ι) :
    sentenceTheory θ c = sentenceTheory θ d :=
  sentenceTheory_eq_iff.2 fun n => e.mem_modelsOf_iff (θ n)

end FirstOrder.Language.Equiv

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {ι : Type uι}

/-- Isomorphic configurations on one carrier have the same truth sequence. -/
theorem sentenceTheory_eq_of_isoSetoid {c d : RelationalConfiguration L V}
    (h : isoSetoid L V c d) (θ : ℕ → L.SentenceInf ι) : sentenceTheory θ c = sentenceTheory θ d :=
  let ⟨e⟩ := isoSetoid_apply.1 h
  e.sentenceTheory_eq θ

/-- Relabelling a configuration by a permutation of the carrier does not change its truth
sequence. -/
@[simp]
theorem sentenceTheory_perm_smul (θ : ℕ → L.SentenceInf ι) (σ : Equiv.Perm V)
    (c : RelationalConfiguration L V) : sentenceTheory θ (σ • c) = sentenceTheory θ c :=
  (sentenceTheory_eq_of_isoSetoid (isoSetoid_perm_smul σ c) θ).symm

end TauCeti.RelationalConfiguration
