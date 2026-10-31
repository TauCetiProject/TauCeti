/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.BackAndForth
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
public import TauCeti.ModelTheory.Scott.Formula
public import TauCeti.Data.Setoid.Basic

/-!
# Back-and-forth levels on model classes

Fix a relational language `L` and a carrier `V`. The back-and-forth levels
`TauCeti.RelationalConfiguration.bfEquivSetoid L V α` stratify isomorphism of configurations on
`V` into a decreasing family of equivalence relations, Borel below `ω₁` on a countable carrier.
This file connects these levels to the model classes `modelsOf φ` of infinitary sentences, in two
ways.

**Level classes are model classes.** For a configuration `c` and a countable ordinal `α`, the
level sentence `scottSentenceAtLevel c α` is the canonical Scott formula of the empty tuple of the
structure decoded from `c`, read as a sentence. Its models are exactly the structures whose empty
tuple is `α`-equivalent to that of `c`; on the carrier `V` its model class is the
`bfEquivSetoid L V α`-class of `c`. So every level class below `ω₁` is cut out by a single
`L_{ω₁ω}` sentence, which lets sentence-level arguments (splitting a model class by sentences,
saturation of a sentence under the levels) be applied to level classes.

**Levels restricted to a model class.** The setoid `bfEquivSetoidOn V φ α` is the level
`bfEquivSetoid L V α` restricted to the configurations in `modelsOf φ`. It decreases with `α`, is
refined by isomorphism, and therefore has at most as many classes as isomorphism has on
`modelsOf φ`: the projection of isomorphism classes onto level classes is surjective. Below `ω₁`,
on a countable carrier in a vocabulary with countably many relation symbols of each arity, it has
Borel graph in the standard Borel space `modelsOf φ`. These are the hypotheses under which
dichotomies for Borel equivalence relations, such as Silver's theorem, are applied level by level
when counting the countable models of `φ`.

## Main definitions

* `TauCeti.RelationalConfiguration.scottSentenceAtLevel c α`: the Scott sentence of the empty tuple
  of the structure decoded from `c`, at depth `α`.
* `TauCeti.RelationalConfiguration.bfEquivSetoidOn V φ α`: back-and-forth equivalence at depth `α`,
  restricted to the model class of `φ` on `V`.

## Main results

* `TauCeti.RelationalConfiguration.realize_scottSentenceAtLevel_iff_bfEquiv`: below `ω₁`, a
  structure satisfies the level sentence of `c` exactly when its empty tuple is back-and-forth
  equivalent to that of `c`.
* `TauCeti.RelationalConfiguration.modelsOf_scottSentenceAtLevel`: below `ω₁`, the model class of
  the level sentence of `c` is the level class of `c`.
* `TauCeti.RelationalConfiguration.bfEquivSetoidOn_anti`: the restricted levels decrease.
* `TauCeti.RelationalConfiguration.comap_isoSetoid_le_bfEquivSetoidOn`: isomorphic models are
  equivalent at every level.
* `TauCeti.RelationalConfiguration.mk_quotient_bfEquivSetoidOn_le`: isomorphism classes of models
  project onto level classes (`Setoid.map_of_le_surjective`), so there are at least as many of the
  former.
* `TauCeti.RelationalConfiguration.measurableSet_setOf_bfEquivSetoidOn`: below `ω₁`, the
  restricted levels have Borel graph.

## References

* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII:
  Lemma XII.5 (level classes are defined by sentences) and §XII.1 (the level-by-level use of
  Silver's theorem in Morley's theorem).
* David Marker, *Lectures on Infinitary Model Theory*, the chapter on the space of countable
  models.
* Analogous statements for coded models in `Type`, with the empty-tuple Scott approximation, are
  `modelsOf_scottSentenceAt` in `InfinitaryLogic/Descriptive/MinimallyUncountable.lean` and
  `bfEquivSetoid` with its projection `bfProj` in `InfinitaryLogic/ModelTheory/MorleyCounting.lean`
  of Cameron Freer's `cameronfreer/infinitary-logic` (Apache-2.0), checkpoint
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`.
-/

public section

universe u v w w' o uι

open FirstOrder FirstOrder.Language Cardinal

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

section LevelSentence

variable [Countable (Σ k, L.Relations k)] [Countable V]

/-- The **level sentence** of a configuration `c` at depth `α`: the canonical Scott formula of the
empty tuple of the structure decoded from `c`, read as a sentence. Below `ω₁` its models are the
structures whose empty tuple is back-and-forth equivalent at depth `α` to that of `c`
(`realize_scottSentenceAtLevel_iff_bfEquiv`). -/
noncomputable def scottSentenceAtLevel (c : RelationalConfiguration L V) (α : Ordinal.{o}) :
    L.Sentenceω :=
  @scottFormula L _ V c.toStructure _ 0 Fin.elim0 α

/-- The level sentence is the Scott formula of the empty tuple of the decoded structure. -/
theorem scottSentenceAtLevel_def (c : RelationalConfiguration L V) (α : Ordinal.{o}) :
    scottSentenceAtLevel c α = @scottFormula L _ V c.toStructure _ 0 Fin.elim0 α :=
  (rfl)

/-- Below `ω₁`, a structure on any carrier satisfies the level sentence of `c` exactly when its
empty tuple is back-and-forth equivalent at depth `α` to that of the structure decoded from `c`. -/
@[simp]
theorem realize_scottSentenceAtLevel_iff_bfEquiv {c : RelationalConfiguration L V}
    {α : Ordinal.{o}} (hα : α < Ordinal.omega 1) {N : Type w'} [L.Structure N] :
    SentenceInf.Realize (scottSentenceAtLevel c α) N ↔
      @BFEquiv L _ V N c.toStructure _ α 0 Fin.elim0 Fin.elim0 := by
  rw [scottSentenceAtLevel_def, SentenceInf.realize_def, FormulaInf.realize_def,
    @realize_scottFormula_iff_bfEquiv L _ V c.toStructure _ 0 _ N _ _ _ _ hα,
    Subsingleton.elim (default : Fin 0 → N) Fin.elim0]

/-- Below `ω₁`, a configuration on `V` lies in the model class of the level sentence of `c` exactly
when it is equivalent to `c` at depth `α`. -/
theorem mem_modelsOf_scottSentenceAtLevel {c d : RelationalConfiguration L V} {α : Ordinal.{o}}
    (hα : α < Ordinal.omega 1) :
    d ∈ modelsOf (scottSentenceAtLevel c α) ↔ bfEquivSetoid L V α c d := by
  rw [mem_modelsOf, bfEquivSetoid_apply]
  exact @realize_scottSentenceAtLevel_iff_bfEquiv L _ V _ _ c α hα V d.toStructure

/-- **Level classes are model classes.** Below `ω₁`, the model class on `V` of the level sentence
of `c` is the class of `c` for back-and-forth equivalence at depth `α`. -/
theorem modelsOf_scottSentenceAtLevel (c : RelationalConfiguration L V) {α : Ordinal.{o}}
    (hα : α < Ordinal.omega 1) :
    modelsOf (scottSentenceAtLevel c α) = {d | bfEquivSetoid L V α c d} :=
  Set.ext fun _ => mem_modelsOf_scottSentenceAtLevel hα

/-- Below `ω₁`, a configuration lies in the model class of its own level sentence. -/
theorem self_mem_modelsOf_scottSentenceAtLevel (c : RelationalConfiguration L V)
    {α : Ordinal.{o}} (hα : α < Ordinal.omega 1) :
    c ∈ modelsOf (scottSentenceAtLevel c α) :=
  (mem_modelsOf_scottSentenceAtLevel hα).mpr ((bfEquivSetoid L V α).refl' c)

end LevelSentence

section LevelsOnModels

variable {ι : Type uι}

variable (V) in
/-- Back-and-forth equivalence at depth `α`, restricted to the model class of `φ` on `V`: two
models are related when the empty tuples of their decoded structures are back-and-forth
equivalent at depth `α`. -/
abbrev bfEquivSetoidOn (φ : L.SentenceInf ι) (α : Ordinal.{o}) : Setoid (modelsOf (V := V) φ) :=
  (bfEquivSetoid L V α).comap Subtype.val

/-- Two models are related by the restricted level exactly when they are related by the ambient
level. -/
theorem bfEquivSetoidOn_apply {φ : L.SentenceInf ι} {α : Ordinal.{o}}
    {c d : modelsOf (V := V) φ} :
    bfEquivSetoidOn V φ α c d ↔ bfEquivSetoid L V α c d :=
  Iff.rfl

/-- The restricted levels decrease: equivalence at a level implies equivalence at every lower
level. -/
theorem bfEquivSetoidOn_anti (φ : L.SentenceInf ι) :
    Antitone (bfEquivSetoidOn V φ : Ordinal.{o} → _) :=
  fun _ _ hαβ => Setoid.comap_monotone _ (bfEquivSetoid_anti hαβ)

/-- Isomorphic models are equivalent at every restricted level. -/
theorem comap_isoSetoid_le_bfEquivSetoidOn (φ : L.SentenceInf ι) (α : Ordinal.{o}) :
    (isoSetoid L V).comap ((↑) : modelsOf (V := V) φ → _) ≤ bfEquivSetoidOn V φ α :=
  Setoid.comap_monotone _ (isoSetoid_le_bfEquivSetoid α)

/-- A model class meets at most as many classes at a back-and-forth level as isomorphism
classes. -/
theorem mk_quotient_bfEquivSetoidOn_le (φ : L.SentenceInf ι) (α : Ordinal.{o}) :
    #(Quotient (bfEquivSetoidOn V φ α)) ≤
      #(Quotient ((isoSetoid L V).comap ((↑) : modelsOf (V := V) φ → _))) :=
  mk_le_of_surjective (Setoid.map_of_le_surjective (comap_isoSetoid_le_bfEquivSetoidOn φ α))

/-- Below `ω₁`, on a countable carrier and in a vocabulary with countably many relation symbols of
each arity, each restricted level has Borel graph in the model class. -/
theorem measurableSet_setOf_bfEquivSetoidOn [Countable V] [∀ n, Countable (L.Relations n)]
    (φ : L.SentenceInf ι) {α : Ordinal.{o}} (hα : α < Ordinal.omega 1) :
    MeasurableSet {p : modelsOf (V := V) φ × modelsOf (V := V) φ |
      bfEquivSetoidOn V φ α p.1 p.2} :=
  (measurableSet_setOf_bfEquivSetoid hα).preimage
    (measurable_subtype_coe.prodMap measurable_subtype_coe)

end LevelsOnModels

end TauCeti.RelationalConfiguration
