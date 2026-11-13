/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Setoid.Countable
public import TauCeti.ModelTheory.Counting.Classes
public import TauCeti.SetTheory.Ordinal.RankBounds

/-!
# Minimally uncountable and minimally unbounded classes of configurations

A set `K` of relational configurations on `V` is *minimally uncountable*
(`TauCeti.MinimallyUncountableOn K`) when it meets uncountably many isomorphism classes, yet every
cut of `K` by an `L_{ω₁ω}` sentence `θ` has at least one side—`K ∩ modelsOf θ` or
`K \ modelsOf θ`—meeting only countably many isomorphism classes. For an ordinal-valued rank `ρ`,
`K` is *minimally unbounded* (`TauCeti.MinimallyUnboundedOn ρ K`) when `ρ` is unbounded below `ω₁`
on `K` and every `L_{ω₁ω}` sentence cut has a side on which `ρ` is strictly bounded below `ω₁`.

These predicates isolate the minimal counterexamples in the Harnik–Makkai and Steel analysis of
Vaught's conjecture and Montalbán's rank-based presentation of Vaught counterexamples. Neither
definition imposes countability of `V` or of `L`, Borelness or isomorphism invariance of `K`, or
isolation of `ρ`. For the model class `modelsOf φ` of an `L_{ω₁ω}` sentence `φ`, the sentence cuts
of `modelsOf φ` are the model classes of the conjunctions `φ ⊓ θ` and `φ ⊓ θ.not`, so minimal
uncountability and minimal unboundedness rewrite directly in terms of strengthenings of `φ`.

## Main definitions

* `TauCeti.MinimallyUncountableOn K`: `K` meets uncountably many isomorphism classes and every
  `L_{ω₁ω}` sentence cut of `K` has a side meeting countably many isomorphism classes.
* `TauCeti.MinimallyUnboundedOn ρ K`: `ρ` is unbounded below `ω₁` on `K` and every `L_{ω₁ω}`
  sentence cut of `K` has a side on which `ρ` is bounded below `ω₁`.

## Main results

* `TauCeti.minimallyUncountableOn_modelsOf_iff_countable_quotient`: for `φ : L.Sentenceω`, minimal
  uncountability of `modelsOf φ` via `isoSetoidOn V (φ ⊓ θ)` and `isoSetoidOn V (φ ⊓ θ.not)`.
* `TauCeti.minimallyUnboundedOn_modelsOf_iff_boundedRankOn`: for `φ : L.Sentenceω`, minimal
  unboundedness of `modelsOf φ` via `BoundedRankOn` on `modelsOf (φ ⊓ θ)` and
  `modelsOf (φ ⊓ θ.not)`.

## References

* V. Harnik and M. Makkai, *A tree argument in infinitary model theory*, Proc. Amer. Math. Soc. 67
  (1977), 309–314.
* J. R. Steel, *On Vaught's conjecture*, Cabal Seminar 76–77, Lecture Notes in Mathematics 689
  (1978), 193–208.
* A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII, §XII.2
  (Definition XII.4, minimally unbounded sentences).
* Minimally uncountable and minimally unbounded classes on `ℕ` are also formalized in Cameron
  Freer's `cameronfreer/infinitary-logic` at checkpoint `518a366cba97b1ae8c4dc64a297a39bc3e0b`,
  `InfinitaryLogic/Descriptive/MinimallyUncountable.lean` and
  `InfinitaryLogic/Descriptive/MinimallyUnbounded.lean` (Apache-2.0); here the definitions are
  given on an arbitrary carrier `V` and for ranks in an arbitrary ordinal universe.
-/

public section

universe u v w r

open FirstOrder FirstOrder.Language Ordinal Set

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}
variable {K : Set (RelationalConfiguration L V)} {ρ : RelationalConfiguration L V → Ordinal.{r}}

/-! ### Minimally uncountable classes -/

/-- A set `K` of configurations on `V` is **minimally uncountable** when it meets uncountably many
isomorphism classes and every cut by an `L_{ω₁ω}` sentence has a side meeting only countably many
isomorphism classes. -/
def MinimallyUncountableOn (K : Set (RelationalConfiguration L V)) : Prop :=
  ¬ (Quotient.mk (isoSetoid L V) '' K).Countable ∧
    ∀ θ : L.Sentenceω,
      (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L V) '' (K \ modelsOf θ)).Countable

/-- Unfolding lemma for `TauCeti.MinimallyUncountableOn`. -/
theorem minimallyUncountableOn_iff :
    MinimallyUncountableOn K ↔
      ¬ (Quotient.mk (isoSetoid L V) '' K).Countable ∧
        ∀ θ : L.Sentenceω,
          (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ)).Countable ∨
            (Quotient.mk (isoSetoid L V) '' (K \ modelsOf θ)).Countable :=
  Iff.rfl

/-- A minimally uncountable class meets uncountably many isomorphism classes. -/
theorem MinimallyUncountableOn.not_countable_isoClasses (h : MinimallyUncountableOn K) :
    ¬ (Quotient.mk (isoSetoid L V) '' K).Countable :=
  h.1

/-- The restricted isomorphism quotient of a minimally uncountable class is uncountable. -/
theorem MinimallyUncountableOn.not_countable_quotient (h : MinimallyUncountableOn K) :
    ¬ Countable (Quotient ((isoSetoid L V).comap (Subtype.val : K → _))) :=
  fun hc => h.1 (Setoid.countable_quotient_comap_val_iff.1 hc)

/-- Every sentence cut of a minimally uncountable class has a side meeting countably many
isomorphism classes. -/
theorem MinimallyUncountableOn.countable_inter_or_sdiff (h : MinimallyUncountableOn K)
    (θ : L.Sentenceω) :
    (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ)).Countable ∨
      (Quotient.mk (isoSetoid L V) '' (K \ modelsOf θ)).Countable :=
  h.2 θ

/-- Every `L_{ω₁ω}` sentence or its negation cuts a minimally uncountable class down to countably
many isomorphism classes. -/
theorem MinimallyUncountableOn.countable_inter_modelsOf_or_modelsOf_not
    (h : MinimallyUncountableOn K) (θ : L.Sentenceω) :
    (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ)).Countable ∨
      (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ.not)).Countable := by
  simpa only [modelsOf_not, ← sdiff_eq] using h.countable_inter_or_sdiff θ

/-- A set meeting countably many isomorphism classes is not minimally uncountable. -/
theorem not_minimallyUncountableOn_of_countable_isoClasses
    (h : (Quotient.mk (isoSetoid L V) '' K).Countable) : ¬ MinimallyUncountableOn K :=
  fun hmin => hmin.not_countable_isoClasses h

/-- The empty set of configurations is not minimally uncountable. -/
@[simp]
theorem not_minimallyUncountableOn_empty :
    ¬ MinimallyUncountableOn (∅ : Set (RelationalConfiguration L V)) :=
  not_minimallyUncountableOn_of_countable_isoClasses (by simp)

/-- A singleton set of configurations is not minimally uncountable. -/
@[simp]
theorem not_minimallyUncountableOn_singleton (c : RelationalConfiguration L V) :
    ¬ MinimallyUncountableOn ({c} : Set (RelationalConfiguration L V)) :=
  not_minimallyUncountableOn_of_countable_isoClasses (by simp)

/-- A minimally uncountable class is nonempty. -/
theorem MinimallyUncountableOn.nonempty (h : MinimallyUncountableOn K) : K.Nonempty :=
  nonempty_iff_ne_empty.2 fun hK => not_minimallyUncountableOn_empty (hK ▸ h)

/-- For an `L_{ω₁ω}` sentence `φ`, `modelsOf φ` is minimally uncountable on `V` exactly when `φ`
has uncountably many models on `V` up to isomorphism and, for every `θ : L.Sentenceω`, either
`φ ⊓ θ` or `φ ⊓ θ.not` has countably many models on `V` up to isomorphism. -/
theorem minimallyUncountableOn_modelsOf_iff_countable_quotient {φ : L.Sentenceω} :
    MinimallyUncountableOn (modelsOf (V := V) φ) ↔
      ¬ Countable (Quotient (isoSetoidOn V φ)) ∧
        ∀ θ : L.Sentenceω,
          Countable (Quotient (isoSetoidOn V (φ ⊓ θ))) ∨
            Countable (Quotient (isoSetoidOn V (φ ⊓ θ.not))) := by
  simp only [minimallyUncountableOn_iff, isoSetoidOn, Setoid.countable_quotient_comap_val_iff,
    modelsOf_inf, modelsOf_not, ← sdiff_eq]

/-! ### Minimally unbounded classes -/

/-- A set `K` of configurations on `V` is **minimally unbounded** for an ordinal-valued rank `ρ`
when `ρ` is unbounded below `ω₁` on `K` and every `L_{ω₁ω}` sentence cut of `K` has a side on which
`ρ` is strictly bounded below `ω₁`. -/
def MinimallyUnboundedOn (ρ : RelationalConfiguration L V → Ordinal.{r})
    (K : Set (RelationalConfiguration L V)) : Prop :=
  UnboundedRankOn ρ K ∧
    ∀ θ : L.Sentenceω, BoundedRankOn ρ (K ∩ modelsOf θ) ∨ BoundedRankOn ρ (K \ modelsOf θ)

/-- Unfolding lemma for `TauCeti.MinimallyUnboundedOn`. -/
theorem minimallyUnboundedOn_iff :
    MinimallyUnboundedOn ρ K ↔
      UnboundedRankOn ρ K ∧
        ∀ θ : L.Sentenceω,
          BoundedRankOn ρ (K ∩ modelsOf θ) ∨ BoundedRankOn ρ (K \ modelsOf θ) :=
  Iff.rfl

/-- A rank is unbounded below `ω₁` on any class that is minimally unbounded for it. -/
theorem MinimallyUnboundedOn.unboundedRankOn (h : MinimallyUnboundedOn ρ K) :
    UnboundedRankOn ρ K :=
  h.1

/-- A class that is minimally unbounded for `ρ` is not rank-bounded below `ω₁`. -/
theorem MinimallyUnboundedOn.not_boundedRankOn (h : MinimallyUnboundedOn ρ K) :
    ¬ BoundedRankOn ρ K :=
  unboundedRankOn_iff_not_boundedRankOn.1 h.1

/-- Every sentence cut of a minimally unbounded class has a rank-bounded side. -/
theorem MinimallyUnboundedOn.boundedRankOn_inter_or_sdiff (h : MinimallyUnboundedOn ρ K)
    (θ : L.Sentenceω) :
    BoundedRankOn ρ (K ∩ modelsOf θ) ∨ BoundedRankOn ρ (K \ modelsOf θ) :=
  h.2 θ

/-- Every `L_{ω₁ω}` sentence or its negation cuts a minimally unbounded class down to a set on
which `ρ` is bounded below `ω₁`. -/
theorem MinimallyUnboundedOn.boundedRankOn_inter_modelsOf_or_modelsOf_not
    (h : MinimallyUnboundedOn ρ K) (θ : L.Sentenceω) :
    BoundedRankOn ρ (K ∩ modelsOf θ) ∨ BoundedRankOn ρ (K ∩ modelsOf θ.not) := by
  simpa only [modelsOf_not, ← sdiff_eq] using h.boundedRankOn_inter_or_sdiff θ

/-- A rank-bounded set is not minimally unbounded. -/
theorem not_minimallyUnboundedOn_of_boundedRankOn (h : BoundedRankOn ρ K) :
    ¬ MinimallyUnboundedOn ρ K :=
  fun hmin => hmin.not_boundedRankOn h

/-- The empty set of configurations is not minimally unbounded for any rank. -/
@[simp]
theorem not_minimallyUnboundedOn_empty (ρ : RelationalConfiguration L V → Ordinal.{r}) :
    ¬ MinimallyUnboundedOn ρ ∅ :=
  not_minimallyUnboundedOn_of_boundedRankOn (boundedRankOn_empty ρ)

/-- A minimally unbounded class is nonempty. -/
theorem MinimallyUnboundedOn.nonempty (h : MinimallyUnboundedOn ρ K) : K.Nonempty :=
  nonempty_iff_ne_empty.2 fun hK => not_minimallyUnboundedOn_empty ρ (hK ▸ h)

/-- For an `L_{ω₁ω}` sentence `φ`, `modelsOf φ` is minimally unbounded for `ρ` on `V` exactly when
`ρ` is unbounded below `ω₁` on `modelsOf φ` and, for every `θ : L.Sentenceω`, `ρ` is bounded below
`ω₁` on `modelsOf (φ ⊓ θ)` or on `modelsOf (φ ⊓ θ.not)`. -/
theorem minimallyUnboundedOn_modelsOf_iff_boundedRankOn {φ : L.Sentenceω} :
    MinimallyUnboundedOn ρ (modelsOf (V := V) φ) ↔
      UnboundedRankOn ρ (modelsOf (V := V) φ) ∧
        ∀ θ : L.Sentenceω,
          BoundedRankOn ρ (modelsOf (V := V) (φ ⊓ θ)) ∨
            BoundedRankOn ρ (modelsOf (V := V) (φ ⊓ θ.not)) := by
  simp only [minimallyUnboundedOn_iff, modelsOf_inf, modelsOf_not, ← sdiff_eq]

end TauCeti
