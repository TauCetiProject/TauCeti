/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.LanguageMap
import TauCeti.MeasureTheory.Measure.BooleanPartition

/-!
# Truth sequences of families of sentences

For a relational language `L`, a carrier `V` and an indexed family `θ : κ → L.SentenceInf ι` of
infinitary sentences, the **truth sequence** `TauCeti.RelationalConfiguration.sentenceTheory θ c`
of a configuration `c` on `V` records, at each `i : κ`, whether the decoded structure of `c`
satisfies `θ i`. Its `i`-th coordinate is `true` exactly when `c` lies in the model class
`modelsOf (θ i)`.

On a countable carrier, for sentences with countable branching, the truth sequence is measurable
into `κ → Bool` (and in particular into Cantor space `ℕ → Bool` when `κ = ℕ`) without any
countability assumption on `L` or `κ`. It is invariant under isomorphism of the decoded structures
across carriers, commutes with carrier encodings and language equivalences, and pulls back along
language maps by translating the sentences. Truth sequences are the observables through which
indexed families of sentences classify relational configurations.

## Main definitions

* `TauCeti.RelationalConfiguration.sentenceTheory`: the `κ → Bool` truth sequence of a family of
  sentences at a configuration.

## Main results

* `TauCeti.RelationalConfiguration.sentenceTheory_eq_true_iff` and
  `TauCeti.RelationalConfiguration.sentenceTheory_eq_false_iff`: the `i`-th coordinate is `true`
  exactly when the configuration is a model of `θ i`.
* `TauCeti.RelationalConfiguration.sentenceTheory_eq_iff`: two configurations have the same truth
  sequence exactly when they lie in the same model classes of the family.
* `TauCeti.RelationalConfiguration.measurable_sentenceTheory`: on a countable carrier the truth
  sequence is measurable.
* `FirstOrder.Language.Equiv.sentenceTheory_eq`,
  `TauCeti.RelationalConfiguration.sentenceTheory_eq_of_isoSetoid`, and
  `TauCeti.RelationalConfiguration.isoSetoid_le_comap_sentenceTheory`: configurations with
  isomorphic decoded structures have the same truth sequence; in particular relabelling by a
  permutation of the carrier preserves it
  (`TauCeti.RelationalConfiguration.sentenceTheory_perm_smul`).
* `Equiv.sentenceTheory_encodeVia_eq_true_iff`,
  `FirstOrder.Language.LHom.sentenceTheory_reductConfiguration`, and
  `FirstOrder.Language.LEquiv.sentenceTheory_onConfiguration`: interaction of `sentenceTheory` with
  carrier encodings, language reducts, and language equivalences.
-/

public section

universe u v u₀ v₀ w w' uι uκ

open FirstOrder FirstOrder.Language

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {W : Type w'}
  {ι : Type uι} {κ : Type uκ}

open Classical in
/-- The **truth sequence** of an indexed family of sentences at a configuration: its `i`-th
coordinate records whether the decoded structure satisfies `θ i`. -/
noncomputable def sentenceTheory (θ : κ → L.SentenceInf ι) (c : RelationalConfiguration L V) :
    κ → Bool :=
  fun i => decide (c ∈ modelsOf (θ i))

/-- The `i`-th coordinate of the truth sequence is `true` exactly when the configuration lies in
the model class of `θ i`. -/
@[simp]
theorem sentenceTheory_eq_true_iff {θ : κ → L.SentenceInf ι} {c : RelationalConfiguration L V}
    {i : κ} : sentenceTheory θ c i = true ↔ c ∈ modelsOf (θ i) := by
  simp [sentenceTheory]

open Classical in
/-- The `i`-th coordinate of the truth sequence is the decision of membership in the model class of
`θ i`. -/
theorem sentenceTheory_apply (θ : κ → L.SentenceInf ι) (c : RelationalConfiguration L V) (i : κ) :
    sentenceTheory θ c i = decide (c ∈ modelsOf (θ i)) :=
  (rfl)

/-- The `i`-th coordinate of the truth sequence is `false` exactly when the configuration lies
outside the model class of `θ i`. -/
@[simp]
theorem sentenceTheory_eq_false_iff {θ : κ → L.SentenceInf ι} {c : RelationalConfiguration L V}
    {i : κ} : sentenceTheory θ c i = false ↔ c ∉ modelsOf (θ i) := by
  simp [sentenceTheory]

/-- Two configurations, possibly on different carriers, have the same truth sequence exactly when
they lie in the same model classes of the family. -/
theorem sentenceTheory_eq_iff {θ : κ → L.SentenceInf ι} {c : RelationalConfiguration L V}
    {d : RelationalConfiguration L W} :
    sentenceTheory θ c = sentenceTheory θ d ↔ ∀ i, (c ∈ modelsOf (θ i) ↔ d ∈ modelsOf (θ i)) := by
  refine funext_iff.trans (forall_congr' fun i => ?_)
  rw [Bool.eq_iff_iff, sentenceTheory_eq_true_iff, sentenceTheory_eq_true_iff]

/-- On a countable carrier, the truth sequence of a family of sentences with countable branching is
measurable into `κ → Bool`. Neither `L` nor `κ` need be countable. -/
@[fun_prop]
theorem measurable_sentenceTheory [Countable ι] [Countable V] (θ : κ → L.SentenceInf ι) :
    Measurable (sentenceTheory (V := V) θ) :=
  TauCeti.measurable_pi_decide_mem fun i => measurableSet_modelsOf (V := V) (θ i)

/-- Agreement of `sentenceTheory θ` defines a measurable equivalence graph on configurations over a
countable carrier for any countable family of countable-branching sentences. -/
theorem measurableSet_setOf_sentenceTheory_eq [Countable ι] [Countable κ] [Countable V]
    (θ : κ → L.SentenceInf ι) :
    MeasurableSet
      {p : RelationalConfiguration L V × RelationalConfiguration L V |
        sentenceTheory θ p.1 = sentenceTheory θ p.2} :=
  measurableSet_eq_fun
    ((measurable_sentenceTheory θ).comp measurable_fst)
    ((measurable_sentenceTheory θ).comp measurable_snd)

end TauCeti.RelationalConfiguration

namespace FirstOrder.Language.Equiv

open TauCeti RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {W : Type w'}
  {ι : Type uι} {κ : Type uκ}

/-- **Isomorphism invariance.** Configurations, on possibly different carriers, with isomorphic
decoded structures have the same truth sequence. -/
theorem sentenceTheory_eq {c : RelationalConfiguration L V} {d : RelationalConfiguration L W}
    (e : @Language.Equiv L V W c.toStructure d.toStructure) (θ : κ → L.SentenceInf ι) :
    sentenceTheory θ c = sentenceTheory θ d :=
  sentenceTheory_eq_iff.2 fun i => e.mem_modelsOf_iff (θ i)

end FirstOrder.Language.Equiv

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {ι : Type uι} {κ : Type uκ}

/-- Isomorphic configurations on one carrier have the same truth sequence. -/
theorem sentenceTheory_eq_of_isoSetoid {c d : RelationalConfiguration L V}
    (h : isoSetoid L V c d) (θ : κ → L.SentenceInf ι) : sentenceTheory θ c = sentenceTheory θ d :=
  let ⟨e⟩ := isoSetoid_apply.1 h
  e.sentenceTheory_eq θ

/-- Relabelling a configuration by a permutation of the carrier does not change its truth
sequence. -/
@[simp]
theorem sentenceTheory_perm_smul (θ : κ → L.SentenceInf ι) (σ : Equiv.Perm V)
    (c : RelationalConfiguration L V) : sentenceTheory θ (σ • c) = sentenceTheory θ c :=
  (sentenceTheory_eq_of_isoSetoid (isoSetoid_perm_smul σ c) θ).symm

/-- Isomorphism refines equality of `θ`-truth sequences. -/
theorem isoSetoid_le_comap_sentenceTheory (θ : κ → L.SentenceInf ι) :
    isoSetoid L V ≤ (⊥ : Setoid (κ → Bool)).comap (sentenceTheory θ) :=
  fun _ _ h => sentenceTheory_eq_of_isoSetoid h θ

end TauCeti.RelationalConfiguration

namespace Equiv

open TauCeti RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {M : Type w} {V : Type w'} [L.Structure M]
  {ι : Type uι} {κ : Type uκ}

/-- Encoding a structure along a bijection of carriers records its satisfaction of each `θ i`. -/
theorem sentenceTheory_encodeVia_eq_true_iff (e : M ≃ V) (θ : κ → L.SentenceInf ι) (i : κ) :
    sentenceTheory θ (e.encodeVia (L := L)) i = true ↔ SentenceInf.Realize (θ i) M := by
  rw [sentenceTheory_eq_true_iff, mem_modelsOf, e.realize_encodeVia]

end Equiv

namespace FirstOrder.Language.LHom

open TauCeti RelationalConfiguration

variable {L₀ : Language.{u₀, v₀}} {L : Language.{u, v}} [L₀.IsRelational] [L.IsRelational]
  {V : Type w} {ι : Type uι} {κ : Type uκ}

/-- The truth sequence on a reduct configuration is the truth sequence of the translated sentences
along the language map. -/
theorem sentenceTheory_reductConfiguration (g : L₀ →ᴸ L) (θ : κ → L₀.SentenceInf ι)
    (c : RelationalConfiguration L V) :
    sentenceTheory θ (g.reductConfiguration c) =
      sentenceTheory (fun i => g.onBoundedFormulaInf (θ i)) c :=
  funext fun i => Bool.eq_iff_iff.2 <| by
    simp only [sentenceTheory_eq_true_iff, mem_modelsOf, g.realize_sentenceInf_reductConfiguration]

end FirstOrder.Language.LHom

namespace FirstOrder.Language.LEquiv

open TauCeti RelationalConfiguration

variable {L₀ : Language.{u₀, v₀}} {L : Language.{u, v}} [L₀.IsRelational] [L.IsRelational]
  {V : Type w} {ι : Type uι} {κ : Type uκ}

/-- Transporting a configuration and a sentence family along a language equivalence preserves the
truth sequence. -/
@[simp]
theorem sentenceTheory_onConfiguration (e : L₀ ≃ᴸ L) (θ : κ → L₀.SentenceInf ι)
    (c : RelationalConfiguration L₀ V) :
    sentenceTheory (fun i => e.toLHom.onBoundedFormulaInf (θ i)) (e.onConfiguration c) =
      sentenceTheory θ c := by
  rw [← e.toLHom.sentenceTheory_reductConfiguration, e.toLHom_reductConfiguration_onConfiguration]

end FirstOrder.Language.LEquiv
