/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Setoid.Basic
public import TauCeti.ModelTheory.Counting.Classes
public import TauCeti.ModelTheory.RelationalConfiguration.BackAndForth
import TauCeti.SetTheory.Descriptive.Silver

/-!
# Back-and-forth levels on model classes

Fix a relational language `L` and a carrier `V`. The back-and-forth levels
`TauCeti.RelationalConfiguration.bfEquivSetoid L V α` stratify isomorphism of configurations on
`V` into a decreasing family of equivalence relations. Below `ω₁`, on a countable carrier in a
vocabulary with countably many relation symbols of each arity, each level has Borel graph.
This file restricts these levels to the model class `modelsOf φ` of an infinitary sentence `φ` and
applies Silver's theorem at a single countable level. Below `ω₁`, on a countable carrier in a
vocabulary with countably many relation symbols, the ambient level classes are model classes of the
level sentences `TauCeti.RelationalConfiguration.scottSentenceAtLevel`
(`TauCeti.RelationalConfiguration.modelsOf_scottSentenceAtLevel`), so each restricted level class
is the intersection of `modelsOf φ` with the model class of a level sentence.

The setoid `bfEquivSetoidOn V φ α` is the level `bfEquivSetoid L V α` restricted to the
configurations in `modelsOf φ`. It decreases with `α`, is refined by isomorphism, and therefore
has at most as many classes as isomorphism has on `modelsOf φ`: the projection of isomorphism
classes onto level classes is surjective. Below `ω₁`, on a countable carrier in a vocabulary with
countably many relation symbols of each arity, `bfEquivSetoid L V α` restricted to any Borel set
`K` of configurations has Borel graph and is refined by isomorphism, so Silver's theorem gives
either countably many depth-`α` classes met by `K` or a Cantor (hence perfect) antichain in `K` of
pairwise non-isomorphic configurations, together with the cardinal dichotomy "`≤ ℵ₀` or `= 𝔠`".
When `φ` has countable branching, `modelsOf φ` is Borel and these dichotomies specialize to
`bfEquivSetoidOn V φ α`.

## Main definitions

* `TauCeti.RelationalConfiguration.bfEquivSetoidOn V φ α`: back-and-forth equivalence at depth `α`,
  restricted to the model class of `φ` on `V`.

## Main results

* `TauCeti.RelationalConfiguration.bfEquivSetoidOn_anti`: the restricted levels decrease.
* `TauCeti.RelationalConfiguration.isoSetoidOn_le_bfEquivSetoidOn`: isomorphic models are
  equivalent at every level.
* `TauCeti.RelationalConfiguration.mk_quotient_bfEquivSetoidOn_le`: isomorphism classes of models
  project onto level classes (`Setoid.map_of_le_surjective`), so there are at least as many of the
  former.
* `TauCeti.RelationalConfiguration.measurableSet_setOf_bfEquivSetoidOn`: below `ω₁`, the
  restricted levels have Borel graph.
* `TauCeti.RelationalConfiguration.countable_quotient_comap_bfEquivSetoid_or_hasPerfectAntichainOn`
  and `TauCeti.RelationalConfiguration.mk_quotient_comap_bfEquivSetoid_le_aleph0_or_eq_continuum`:
  below `ω₁`, the one-level Silver dichotomy on a Borel set of configurations.
* `TauCeti.RelationalConfiguration.countable_quotient_bfEquivSetoidOn_or_hasPerfectAntichainOn`
  and `TauCeti.RelationalConfiguration.mk_quotient_bfEquivSetoidOn_le_aleph0_or_eq_continuum`:
  the one-level Silver dichotomy specialized to `modelsOf φ`.

## References

* J. H. Silver, *Counting the number of equivalence classes of Borel and coanalytic equivalence
  relations*, Annals of Mathematical Logic 18 (1980), 1–28.
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII,
  §XII.1 (the level-by-level use of Silver's theorem in Morley's theorem).
* David Marker, *Lectures on Infinitary Model Theory*, the chapter on the space of countable
  models.
* An analogous statement for coded models in `Type` is `bfEquivSetoid` with its projection
  `bfProj` in `InfinitaryLogic/ModelTheory/MorleyCounting.lean`, and the one-level dichotomy
  follows `InfinitaryLogic/Conditional/MorleyPerfect.lean`, in Cameron Freer's
  `cameronfreer/infinitary-logic` (Apache-2.0), checkpoint
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`; here Borel sets of configurations on any countable
  carrier are covered before specializing to model classes, and Silver's theorem is discharged
  unconditionally.
-/

public section

universe u v w o uι

open FirstOrder FirstOrder.Language Cardinal Ordinal

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

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
@[simp]
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
theorem isoSetoidOn_le_bfEquivSetoidOn (φ : L.SentenceInf ι) (α : Ordinal.{o}) :
    isoSetoidOn V φ ≤ bfEquivSetoidOn V φ α :=
  Setoid.comap_monotone _ (isoSetoid_le_bfEquivSetoid α)

/-- A model class meets at most as many classes at a back-and-forth level as isomorphism
classes. -/
theorem mk_quotient_bfEquivSetoidOn_le (φ : L.SentenceInf ι) (α : Ordinal.{o}) :
    #(Quotient (bfEquivSetoidOn V φ α)) ≤ #(Quotient (isoSetoidOn V φ)) :=
  mk_le_of_surjective (Setoid.map_of_le_surjective (isoSetoidOn_le_bfEquivSetoidOn φ α))

/-- Below `ω₁`, on a countable carrier and in a vocabulary with countably many relation symbols of
each arity, each restricted level has Borel graph in the model class. -/
theorem measurableSet_setOf_bfEquivSetoidOn [Countable V] [∀ n, Countable (L.Relations n)]
    (φ : L.SentenceInf ι) {α : Ordinal.{o}} (hα : α < Ordinal.omega 1) :
    MeasurableSet {p : modelsOf (V := V) φ × modelsOf (V := V) φ |
      bfEquivSetoidOn V φ α p.1 p.2} :=
  (measurableSet_setOf_bfEquivSetoid hα).preimage
    (measurable_subtype_coe.prodMap measurable_subtype_coe)

end LevelsOnModels

/-! ### One-level Silver dichotomies -/

/-- **One-level dichotomy for Borel sets (Cantor form).** Below `ω₁`, on a countable carrier and in
a vocabulary with countably many relation symbols of each arity, any Borel set `K` of configurations
meets countably many depth-`α` back-and-forth classes or carries a Cantor antichain of pairwise
non-isomorphic configurations. -/
theorem countable_quotient_comap_bfEquivSetoid_or_hasCantorAntichainOn [Countable V]
    [∀ n, Countable (L.Relations n)] {K : Set (RelationalConfiguration L V)} (hK : MeasurableSet K)
    {α : Ordinal.{o}} (hα : α < ω₁) :
    Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : K → _))) ∨
      (isoSetoid L V).HasCantorAntichainOn K :=
  Setoid.countable_or_hasCantorAntichainOn_of_measurableSet hK (isoSetoid L V)
    ((bfEquivSetoid L V α).comap Subtype.val)
    (fun _ _ h => isoSetoid_le_bfEquivSetoid α h)
    ((measurableSet_setOf_bfEquivSetoid hα).preimage
      (measurable_subtype_coe.prodMap measurable_subtype_coe))

/-- **One-level dichotomy for Borel sets (perfect-set form).** Below `ω₁`, on a countable carrier
and in a vocabulary with countably many relation symbols of each arity, any Borel set `K` of
configurations meets countably many depth-`α` back-and-forth classes or contains a nonempty perfect
set of pairwise non-isomorphic configurations. -/
theorem countable_quotient_comap_bfEquivSetoid_or_hasPerfectAntichainOn [Countable V]
    [∀ n, Countable (L.Relations n)] {K : Set (RelationalConfiguration L V)} (hK : MeasurableSet K)
    {α : Ordinal.{o}} (hα : α < ω₁) :
    Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : K → _))) ∨
      (isoSetoid L V).HasPerfectAntichainOn K :=
  (countable_quotient_comap_bfEquivSetoid_or_hasCantorAntichainOn hK hα).imp_right
    Setoid.HasCantorAntichainOn.hasPerfectAntichainOn

/-- **One-level dichotomy for Borel sets (cardinal form).** Below `ω₁`, on a countable carrier and
in a vocabulary with countably many relation symbols of each arity, the depth-`α` back-and-forth
relation restricted to a Borel set `K` of configurations has either at most `ℵ₀` or `𝔠` classes. -/
theorem mk_quotient_comap_bfEquivSetoid_le_aleph0_or_eq_continuum [Countable V]
    [∀ n, Countable (L.Relations n)] {K : Set (RelationalConfiguration L V)} (hK : MeasurableSet K)
    {α : Ordinal.{o}} (hα : α < ω₁) :
    #(Quotient ((bfEquivSetoid L V α).comap (Subtype.val : K → _))) ≤ ℵ₀ ∨
      #(Quotient ((bfEquivSetoid L V α).comap (Subtype.val : K → _))) = 𝔠 := by
  have := hK.standardBorel
  exact Setoid.mk_quotient_le_aleph0_or_eq_continuum ((bfEquivSetoid L V α).comap Subtype.val)
    ((measurableSet_setOf_bfEquivSetoid hα).preimage
      (measurable_subtype_coe.prodMap measurable_subtype_coe))

section LevelDichotomiesOnModels

variable {ι : Type uι}

variable (V) in
/-- **One-level dichotomy on models (Cantor form).** Below `ω₁`, on a countable carrier and in a
vocabulary with countably many relation symbols of each arity, the models of `φ` with countable
branching fall into countably many back-and-forth classes at depth `α`, or carry a Cantor antichain
of pairwise non-isomorphic models. -/
theorem countable_quotient_bfEquivSetoidOn_or_hasCantorAntichainOn [Countable V]
    [∀ n, Countable (L.Relations n)] [Countable ι] (φ : L.SentenceInf ι) {α : Ordinal.{o}}
    (hα : α < ω₁) :
    Countable (Quotient (bfEquivSetoidOn V φ α)) ∨
      (isoSetoid L V).HasCantorAntichainOn (modelsOf φ) :=
  countable_quotient_comap_bfEquivSetoid_or_hasCantorAntichainOn (measurableSet_modelsOf φ) hα

variable (V) in
/-- **One-level dichotomy on models (perfect-set form).** Below `ω₁`, on a countable carrier and in
a vocabulary with countably many relation symbols of each arity, the models of `φ` with countable
branching fall into countably many back-and-forth classes at depth `α`, or contain a nonempty
perfect set of pairwise non-isomorphic models. -/
theorem countable_quotient_bfEquivSetoidOn_or_hasPerfectAntichainOn [Countable V]
    [∀ n, Countable (L.Relations n)] [Countable ι] (φ : L.SentenceInf ι) {α : Ordinal.{o}}
    (hα : α < ω₁) :
    Countable (Quotient (bfEquivSetoidOn V φ α)) ∨
      (isoSetoid L V).HasPerfectAntichainOn (modelsOf φ) :=
  countable_quotient_comap_bfEquivSetoid_or_hasPerfectAntichainOn (measurableSet_modelsOf φ) hα

variable (V) in
/-- **One-level dichotomy on models (cardinal form).** Below `ω₁`, on a countable carrier and in a
vocabulary with countably many relation symbols of each arity, the depth-`α` back-and-forth relation
on the models of `φ` has either at most `ℵ₀` or `𝔠` classes. -/
theorem mk_quotient_bfEquivSetoidOn_le_aleph0_or_eq_continuum [Countable V]
    [∀ n, Countable (L.Relations n)] [Countable ι] (φ : L.SentenceInf ι) {α : Ordinal.{o}}
    (hα : α < ω₁) :
    #(Quotient (bfEquivSetoidOn V φ α)) ≤ ℵ₀ ∨ #(Quotient (bfEquivSetoidOn V φ α)) = 𝔠 :=
  mk_quotient_comap_bfEquivSetoid_le_aleph0_or_eq_continuum (measurableSet_modelsOf φ) hα

end LevelDichotomiesOnModels

end TauCeti.RelationalConfiguration
