/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Levels
public import TauCeti.ModelTheory.Counting.Scattered.Basic

/-!
# Morley's theorem on the number of countable models

How many countable models can an infinitary sentence `φ` with countable branching have, up to
isomorphism, in a relational language with countably many relation symbols of each arity? Morley's
theorem answers: either at most `ℵ₁`, or `φ` has a nonempty perfect set of pairwise non-isomorphic
countable models, and therefore continuum many. Neither the continuum hypothesis nor its negation is
assumed: under the continuum hypothesis `ℵ₁` and `𝔠` coincide, so the witnessed form with a perfect
set is strictly more informative than the cardinal dichotomy "`≤ ℵ₁` or `= 𝔠`".

Isomorphism of structures on `ℕ` is analytic rather than Borel in general, so Silver's theorem
cannot be applied to it directly. Instead, Silver's theorem enters level by level through the
decreasing hierarchy of back-and-forth equivalence relations `bfEquivSetoid L ℕ α`
(`TauCeti.RelationalConfiguration.countable_quotient_comap_bfEquivSetoid_or_hasPerfectAntichainOn`).
On `ℕ`, if a Borel set `K` contains no perfect set of pairwise non-isomorphic configurations, every
countable back-and-forth level on `K` has countably many classes
(`TauCeti.BFScattered.of_isThinOn`), and the isolating-rank stratification bound
(`TauCeti.mk_isoClasses_le_aleph_one_of_countable_levels`) bounds the isomorphism classes met by `K`
by `ℵ₁` (`TauCeti.mk_isoClasses_le_aleph_one_or_hasPerfectAntichainOn`). Specializing to the Borel
model class `modelsOf φ` on `ℕ` and combining with the finite-carrier dichotomy across all `Fin n`
(`TauCeti.sum_mk_quotient_isoSetoidOn_fin_le_aleph0_or_hasPerfectlyManyCountableModels`) yields
Morley's theorem in its witnessed form
(`TauCeti.morley_countableModelCount_le_aleph_one_or_hasPerfectlyMany`), from which the cardinal
form (`TauCeti.morley_countableModelCount`) follows via
`TauCeti.HasPerfectlyManyCountableModels.countableModelCount_eq`. The purely cardinal transfer from
levelwise and finite-tier "`≤ ℵ₀` or `= 𝔠`" dichotomies to "`≤ ℵ₁` or `= 𝔠`" is also isolated in
`TauCeti.countableModelCount_le_aleph_one_or_eq_continuum_of_dichotomy`, without assuming a
countable language, countable branching, or Cantor or perfect antichains.

Finally, `TauCeti.IsThinOnNatModels φ` records that `modelsOf (V := ℕ) φ` carries no perfect set of
pairwise non-isomorphic configurations. A thin sentence is back-and-forth scattered on `ℕ`, has at
most `ℵ₁` models on `ℕ` (and exactly `ℵ₁` when uncountable), and has countably many models on `ℕ`
precisely when any isolating rank is bounded below `ω₁` on its models on `ℕ`. Conversely, fewer than
`𝔠` models on `ℕ` forces `φ` to be thin and hence scattered.

## Main definitions

* `TauCeti.IsThinOnNatModels φ`: the model class of `φ` on `ℕ` contains no nonempty perfect set of
  pairwise non-isomorphic configurations.

## Main results

* `TauCeti.mk_isoClasses_le_aleph_one_or_hasPerfectAntichainOn` and
  `TauCeti.mk_isoClasses_le_aleph_one_or_eq_continuum`: a Borel set of configurations on `ℕ` meets
  at most `ℵ₁` isomorphism classes or contains a nonempty perfect set of pairwise non-isomorphic
  configurations (hence `≤ ℵ₁` or `= 𝔠`).
* `TauCeti.mk_quotient_isoSetoidOn_nat_le_aleph_one_or_hasPerfectAntichainOn` and
  `TauCeti.mk_quotient_isoSetoidOn_nat_le_aleph_one_or_eq_continuum`: Morley's dichotomy on the
  tier `ℕ`.
* `TauCeti.morley_countableModelCount_le_aleph_one_or_hasPerfectlyMany` and
  `TauCeti.morley_countableModelCount`: **Morley's theorem** in witnessed and cardinal forms.
* `TauCeti.countableModelCount_le_aleph_one_or_eq_continuum_of_dichotomy`: the cardinal form of
  Morley's theorem from abstract levelwise and finite-tier "`≤ ℵ₀` or `= 𝔠`" dichotomies.
* `TauCeti.IsThinOnNatModels.bfScattered_modelsOf`,
  `TauCeti.IsThinOnNatModels.mk_quotient_isoSetoidOn_le_aleph_one`,
  `TauCeti.IsThinOnNatModels.mk_quotient_isoSetoidOn_eq_aleph_one`,
  `TauCeti.IsThinOnNatModels.countable_quotient_isoSetoidOn_iff_bounded`, and
  `TauCeti.isThinOnNatModels_of_mk_quotient_lt_continuum`: thin sentences on `ℕ`, their level and
  isomorphism-class counts, and thinness from fewer than `𝔠` models.

## References

* M. Morley, *The number of countable models*, J. Symbolic Logic 35 (1970), 14–18.
* J. H. Silver, *Counting the number of equivalence classes of Borel and coanalytic equivalence
  relations*, Annals of Mathematical Logic 18 (1980), 1–28.
* A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII, §XII.1
  (Morley's theorem via Silver's theorem).
* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, the chapters
  on the space of countable models and Vaught counterexamples.
* The counting assembly follows `morley_counting` in
  `InfinitaryLogic/ModelTheory/MorleyCounting.lean`, `morley_counting_or_perfect` and
  `morley_counting_or_perfect_cardinal` in `InfinitaryLogic/Conditional/MorleyPerfect.lean`, and
  `IsThinOnNatModels` in `InfinitaryLogic/Descriptive/StructureIsoSetoid.lean` of Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  Apache-2.0). There `morley_counting` counts coded models in `Type` from a dichotomy hypothesis;
  here Silver's theorem is discharged unconditionally, Borel configuration sets are covered before
  specializing to model classes, the finite tiers are included, and the language and branching
  universes are arbitrary.
-/

public section

universe u v o uι uι'

open FirstOrder FirstOrder.Language Cardinal Ordinal

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {ι : Type uι} {ι' : Type uι'}

/-! ### Borel sets of configurations on `ℕ` -/

/-- **Morley's dichotomy for Borel sets on `ℕ`.** In a relational language with countably many
relation symbols of each arity, any Borel set `K` of configurations on `ℕ` meets at most `ℵ₁`
isomorphism classes or contains a nonempty perfect set of pairwise non-isomorphic configurations.
No isomorphism invariance of `K` is required. -/
theorem mk_isoClasses_le_aleph_one_or_hasPerfectAntichainOn [∀ n, Countable (L.Relations n)]
    {K : Set (RelationalConfiguration L ℕ)} (hK : MeasurableSet K) :
    #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) ≤ ℵ₁ ∨
      (isoSetoid L ℕ).HasPerfectAntichainOn K := by
  refine or_iff_not_imp_right.2 fun hthin => ?_
  have hscat : BFScattered K := BFScattered.of_isThinOn hK (Setoid.isThinOn_iff.2 hthin)
  exact mk_isoClasses_le_aleph_one_of_countable_levels K fun _ hα => hscat.countable_quotient hα

/-- **Morley's cardinal dichotomy for Borel sets on `ℕ`.** In a relational language with countably
many relation symbols of each arity, any Borel set `K` of configurations on `ℕ` meets either at most
`ℵ₁` or `𝔠` isomorphism classes. -/
theorem mk_isoClasses_le_aleph_one_or_eq_continuum [∀ n, Countable (L.Relations n)]
    {K : Set (RelationalConfiguration L ℕ)} (hK : MeasurableSet K) :
    #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) ≤ ℵ₁ ∨
      #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) = 𝔠 :=
  (mk_isoClasses_le_aleph_one_or_hasPerfectAntichainOn hK).imp_right fun h =>
    h.hasCantorAntichainOn.mk_quotient_comap_eq_continuum

/-! ### Morley's theorem -/

/-- **Morley's dichotomy on the tier `ℕ`.** In a relational language with countably many relation
symbols of each arity, the models on `ℕ` of an infinitary sentence with countable branching have at
most `ℵ₁` isomorphism classes, or contain a nonempty perfect set of pairwise non-isomorphic
models. -/
theorem mk_quotient_isoSetoidOn_nat_le_aleph_one_or_hasPerfectAntichainOn
    [∀ n, Countable (L.Relations n)] [Countable ι] (φ : L.SentenceInf ι) :
    #(Quotient (isoSetoidOn ℕ φ)) ≤ ℵ₁ ∨
      (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOf φ) :=
  mk_isoClasses_le_aleph_one_or_hasPerfectAntichainOn (measurableSet_modelsOf φ)

/-- **Morley's cardinal dichotomy on the tier `ℕ`.** In a relational language with countably many
relation symbols of each arity, the models of `φ` on `ℕ` have either at most `ℵ₁` or `𝔠` isomorphism
classes. -/
theorem mk_quotient_isoSetoidOn_nat_le_aleph_one_or_eq_continuum
    [∀ n, Countable (L.Relations n)] [Countable ι] (φ : L.SentenceInf ι) :
    #(Quotient (isoSetoidOn ℕ φ)) ≤ ℵ₁ ∨ #(Quotient (isoSetoidOn ℕ φ)) = 𝔠 :=
  mk_isoClasses_le_aleph_one_or_eq_continuum (measurableSet_modelsOf φ)

/-- **Morley's theorem (witnessed form).** In a relational language with countably many relation
symbols of each arity, an infinitary sentence with countable branching (in particular every sentence
of `L_{ω₁ω}`) either has at most `ℵ₁` countable models up to isomorphism, finite models included, or
has a nonempty perfect set of pairwise non-isomorphic countable models at the tier `ℕ` or at some
finite tier `Fin n`. Neither the continuum hypothesis nor its negation is assumed. -/
theorem morley_countableModelCount_le_aleph_one_or_hasPerfectlyMany
    [∀ n, Countable (L.Relations n)] [Countable ι] (φ : L.SentenceInf ι) :
    countableModelCount φ ≤ ℵ₁ ∨ HasPerfectlyManyCountableModels φ := by
  rcases mk_quotient_isoSetoidOn_nat_le_aleph_one_or_hasPerfectAntichainOn φ with hℕ | hℕ
  · rcases sum_mk_quotient_isoSetoidOn_fin_le_aleph0_or_hasPerfectlyManyCountableModels φ with
      hfin | hfin
    · refine .inl ?_
      rw [countableModelCount_eq_add_sum]
      exact (add_le_add hℕ hfin).trans_eq (add_eq_left (aleph0_le_aleph 1) (aleph0_le_aleph 1))
    · exact .inr hfin
  · exact .inr (.of_nat hℕ)

/-- **Morley's theorem (cardinal form).** In a relational language with countably many relation
symbols of each arity, an infinitary sentence with countable branching has either at most `ℵ₁` or
`𝔠` countable models up to isomorphism. Neither the continuum hypothesis nor its negation is
assumed. -/
theorem morley_countableModelCount [∀ n, Countable (L.Relations n)] [Countable ι]
    (φ : L.SentenceInf ι) :
    countableModelCount φ ≤ ℵ₁ ∨ countableModelCount φ = 𝔠 :=
  (morley_countableModelCount_le_aleph_one_or_hasPerfectlyMany φ).imp_right
    HasPerfectlyManyCountableModels.countableModelCount_eq

/-- If every countable back-and-forth level on `ℕ` and every finite carrier `Fin n` has either at
most `ℵ₀` or `𝔠` classes of models of `φ`, then `φ` has either at most `ℵ₁` or `𝔠` countable models
up to isomorphism. No countability assumption on the language or on the branching index `ι` is
required. -/
theorem countableModelCount_le_aleph_one_or_eq_continuum_of_dichotomy {φ : L.SentenceInf ι}
    (hlevels : ∀ α : Ordinal.{0}, α < ω₁ →
      #(Quotient (bfEquivSetoidOn ℕ φ α)) ≤ ℵ₀ ∨ #(Quotient (bfEquivSetoidOn ℕ φ α)) = 𝔠)
    (hfin : ∀ n,
      #(Quotient (isoSetoidOn (Fin n) φ)) ≤ ℵ₀ ∨ #(Quotient (isoSetoidOn (Fin n) φ)) = 𝔠) :
    countableModelCount φ ≤ ℵ₁ ∨ countableModelCount φ = 𝔠 := by
  have hle : countableModelCount φ ≤ 𝔠 := by
    have hρ := isIsolatingRank_scottHeight L
    have hfib (α : Ordinal.{0}) (hα : α < ω₁) :
        #(rankOnIsoClasses hρ.iso_invariant (modelsOf φ) ⁻¹' {α}) ≤ 𝔠 := by
      obtain ⟨f, hf⟩ := hρ.exists_injective_rank_fiber (modelsOf φ) α
      exact (mk_le_of_injective hf).trans <|
        (hlevels α hα).elim (fun h => h.trans aleph0_le_continuum) le_of_eq
    have hℕ : #(Quotient (isoSetoidOn ℕ φ)) ≤ 𝔠 :=
      (mk_le_aleph_one_mul_of_mk_preimage_le
        (rankOnIsoClasses_lt_omega_one hρ.iso_invariant hρ.lt_omega_one (modelsOf φ)) hfib).trans
        ((mul_le_mul' aleph_one_le_continuum le_rfl).trans_eq (mul_eq_self aleph0_le_continuum))
    exact (countableModelCount_le_add_aleph0_mul hℕ fun n =>
      (hfin n).elim (fun h => h.trans aleph0_le_continuum) le_of_eq).trans_eq
        (by rw [aleph0_mul_continuum, continuum_add_self])
  by_cases hall : ∀ α : Ordinal.{0}, α < ω₁ → #(Quotient (bfEquivSetoidOn ℕ φ α)) ≤ ℵ₀
  · have hℕ : #(Quotient (isoSetoidOn ℕ φ)) ≤ ℵ₁ :=
      mk_isoClasses_le_aleph_one_of_countable_levels (modelsOf φ) fun α hα =>
        mk_le_aleph0_iff.1 (hall α hα)
    rcases sum_mk_quotient_isoSetoidOn_fin_le_aleph0_or_eq_continuum_of_dichotomy hfin with
      hsum | hsum
    · refine .inl ?_
      rw [countableModelCount_eq_add_sum]
      exact (add_le_add hℕ hsum).trans_eq (add_eq_left (aleph0_le_aleph 1) (aleph0_le_aleph 1))
    · refine .inr <| hle.antisymm ?_
      rw [countableModelCount_eq_add_sum, hsum]
      exact self_le_add_left 𝔠 _
  · obtain ⟨α, hα⟩ := not_forall.1 hall
    rw [not_imp] at hα
    have hαc : #(Quotient (bfEquivSetoidOn ℕ φ α)) = 𝔠 := (hlevels α hα.1).resolve_left hα.2
    refine .inr <| hle.antisymm ?_
    exact hαc.symm.trans_le <|
      (mk_quotient_bfEquivSetoidOn_le φ α).trans
        (mk_quotient_isoSetoidOn_nat_le_countableModelCount φ)

/-- A sentence without perfectly many countable models has at most `ℵ₁` countable models up to
isomorphism. -/
theorem countableModelCount_le_aleph_one_of_not_hasPerfectlyManyCountableModels
    [∀ n, Countable (L.Relations n)] [Countable ι] {φ : L.SentenceInf ι}
    (h : ¬ HasPerfectlyManyCountableModels φ) :
    countableModelCount φ ≤ ℵ₁ :=
  (morley_countableModelCount_le_aleph_one_or_hasPerfectlyMany φ).resolve_right h

/-- A sentence with uncountably many countable models and no perfect set of pairwise non-isomorphic
countable models has `ℵ₁` countable models up to isomorphism. -/
theorem countableModelCount_eq_aleph_one_of_aleph0_lt_of_not_hasPerfectlyManyCountableModels
    [∀ n, Countable (L.Relations n)] [Countable ι] {φ : L.SentenceInf ι}
    (h₀ : ℵ₀ < countableModelCount φ) (h : ¬ HasPerfectlyManyCountableModels φ) :
    countableModelCount φ = ℵ₁ :=
  (countableModelCount_le_aleph_one_of_not_hasPerfectlyManyCountableModels h).antisymm
    (aleph_one_le_iff.2 h₀)

/-- A sentence with uncountably many, yet fewer than continuum many, countable models has `ℵ₁`
countable models up to isomorphism. -/
theorem countableModelCount_eq_aleph_one_of_aleph0_lt_of_lt_continuum
    [∀ n, Countable (L.Relations n)] [Countable ι] {φ : L.SentenceInf ι}
    (h₀ : ℵ₀ < countableModelCount φ) (hc : countableModelCount φ < 𝔠) :
    countableModelCount φ = ℵ₁ :=
  ((morley_countableModelCount φ).resolve_right hc.ne).antisymm (aleph_one_le_iff.2 h₀)

/-! ### Thin sentences -/

/-- An infinitary sentence is *thin on its models on `ℕ`* when its model class on `ℕ` contains no
nonempty perfect set of pairwise non-isomorphic configurations. -/
def IsThinOnNatModels (φ : L.SentenceInf ι) : Prop :=
  (isoSetoid L ℕ).IsThinOn (modelsOf φ)

/-- `TauCeti.IsThinOnNatModels` is `Setoid.IsThinOn` for isomorphism on the model class on `ℕ`. -/
theorem isThinOnNatModels_iff_isThinOn {φ : L.SentenceInf ι} :
    IsThinOnNatModels φ ↔ (isoSetoid L ℕ).IsThinOn (modelsOf φ) :=
  Iff.rfl

/-- Unfolding lemma for `TauCeti.IsThinOnNatModels` in terms of `Setoid.HasPerfectAntichainOn`. -/
theorem isThinOnNatModels_iff {φ : L.SentenceInf ι} :
    IsThinOnNatModels φ ↔ ¬ (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOf φ) :=
  Setoid.isThinOn_iff

/-- The false sentence has no models on `ℕ`, hence is thin on `ℕ`. -/
@[simp]
theorem isThinOnNatModels_bot : IsThinOnNatModels (⊥ : L.SentenceInf ι) :=
  isThinOnNatModels_iff.2 fun h => by
    obtain ⟨P, -, ⟨c, hc⟩, hP, -⟩ := Setoid.hasPerfectAntichainOn_iff.1 h
    exact (by simpa using hP hc : False)

/-- In a vocabulary with countably many relation symbols of each arity, a sentence is thin on `ℕ`
exactly when its model class on `ℕ` carries no Cantor antichain of pairwise non-isomorphic
models. -/
theorem isThinOnNatModels_iff_not_hasCantorAntichainOn [∀ n, Countable (L.Relations n)]
    {φ : L.SentenceInf ι} :
    IsThinOnNatModels φ ↔ ¬ (isoSetoid L ℕ).HasCantorAntichainOn (modelsOf φ) :=
  Setoid.isThinOn_iff_not_hasCantorAntichainOn

/-- Thinness on `ℕ` passes to any sentence whose models on `ℕ` are models of a thin sentence. -/
theorem IsThinOnNatModels.of_subset {φ : L.SentenceInf ι} {ψ : L.SentenceInf ι'}
    (h : modelsOf (V := ℕ) φ ⊆ modelsOf ψ) (hψ : IsThinOnNatModels ψ) :
    IsThinOnNatModels φ :=
  hψ.anti h

/-- A sentence fails to have perfectly many countable models exactly when it is thin on `ℕ` and on
every finite carrier `Fin n`. -/
theorem not_hasPerfectlyManyCountableModels_iff {φ : L.SentenceInf ι} :
    ¬ HasPerfectlyManyCountableModels φ ↔
      IsThinOnNatModels φ ∧ ∀ n, (isoSetoid L (Fin n)).IsThinOn (modelsOf φ) := by
  simp only [hasPerfectlyManyCountableModels_iff, not_or, not_exists, isThinOnNatModels_iff,
    Setoid.isThinOn_iff]

/-- A sentence without perfectly many countable models is thin on `ℕ`. -/
theorem IsThinOnNatModels.of_not_hasPerfectlyManyCountableModels {φ : L.SentenceInf ι}
    (h : ¬ HasPerfectlyManyCountableModels φ) : IsThinOnNatModels φ :=
  (not_hasPerfectlyManyCountableModels_iff.1 h).1

/-- A sentence that is thin on `ℕ` has countably many depth-`α` back-and-forth classes of models on
`ℕ` at every countable ordinal `α`. -/
theorem IsThinOnNatModels.countable_quotient_bfEquivSetoidOn
    [∀ n, Countable (L.Relations n)] [Countable ι] {φ : L.SentenceInf ι}
    (h : IsThinOnNatModels φ) {α : Ordinal.{o}} (hα : α < ω₁) :
    Countable (Quotient (bfEquivSetoidOn ℕ φ α)) :=
  (countable_quotient_bfEquivSetoidOn_or_hasPerfectAntichainOn ℕ φ hα).resolve_right
    (isThinOnNatModels_iff.1 h)

/-- **Thin sentences are back-and-forth scattered.** If `φ` is thin on `ℕ`, its model class on `ℕ`
is back-and-forth scattered. -/
theorem IsThinOnNatModels.bfScattered_modelsOf [∀ n, Countable (L.Relations n)] [Countable ι]
    {φ : L.SentenceInf ι} (h : IsThinOnNatModels φ) :
    BFScattered (modelsOf (V := ℕ) φ) :=
  BFScattered.of_isThinOn (measurableSet_modelsOf φ) h

/-- A sentence that is thin on `ℕ` has at most `ℵ₁` models on `ℕ` up to isomorphism. -/
theorem IsThinOnNatModels.mk_quotient_isoSetoidOn_le_aleph_one
    [∀ n, Countable (L.Relations n)] [Countable ι] {φ : L.SentenceInf ι}
    (h : IsThinOnNatModels φ) :
    #(Quotient (isoSetoidOn ℕ φ)) ≤ ℵ₁ :=
  (mk_quotient_isoSetoidOn_nat_le_aleph_one_or_hasPerfectAntichainOn φ).resolve_right
    (isThinOnNatModels_iff.1 h)

/-- A sentence that is thin on `ℕ` and has uncountably many models on `ℕ` up to isomorphism has `ℵ₁`
of them. -/
theorem IsThinOnNatModels.mk_quotient_isoSetoidOn_eq_aleph_one
    [∀ n, Countable (L.Relations n)] [Countable ι] {φ : L.SentenceInf ι}
    (h : IsThinOnNatModels φ) [Uncountable (Quotient (isoSetoidOn ℕ φ))] :
    #(Quotient (isoSetoidOn ℕ φ)) = ℵ₁ :=
  (isIsolatingRank_scottHeight L).mk_isoClasses_eq_aleph_one h.bfScattered_modelsOf

/-- A sentence that is thin on `ℕ` has countably many models on `ℕ` up to isomorphism if and only
if any given isolating rank is bounded below `ω₁` on its model class on `ℕ`. -/
theorem IsThinOnNatModels.countable_quotient_isoSetoidOn_iff_bounded
    [∀ n, Countable (L.Relations n)] [Countable ι] {φ : L.SentenceInf ι}
    (h : IsThinOnNatModels φ) {ρ : RelationalConfiguration L ℕ → Ordinal.{0}}
    (hρ : IsIsolatingRank ρ) :
    Countable (Quotient (isoSetoidOn ℕ φ)) ↔
      ∃ β < ω₁, ∀ c ∈ modelsOf (V := ℕ) φ, ρ c < β :=
  hρ.countable_isoClasses_iff_bounded h.bfScattered_modelsOf

/-- If `φ` has fewer than continuum many models on `ℕ` up to isomorphism, then `φ` is thin on `ℕ`.
No countability assumption on the branching index `ι` is required. -/
theorem isThinOnNatModels_of_mk_quotient_lt_continuum [∀ n, Countable (L.Relations n)]
    {φ : L.SentenceInf ι} (h : #(Quotient (isoSetoidOn ℕ φ)) < 𝔠) :
    IsThinOnNatModels φ :=
  isThinOnNatModels_iff.2 fun hP => h.not_ge hP.hasCantorAntichainOn.continuum_le_mk_quotient_comap

/-- If `φ` has fewer than continuum many countable models in total, it has no perfect set of
pairwise non-isomorphic countable models at any tier. -/
theorem not_hasPerfectlyManyCountableModels_of_lt_continuum [∀ n, Countable (L.Relations n)]
    {φ : L.SentenceInf ι} (h : countableModelCount φ < 𝔠) :
    ¬ HasPerfectlyManyCountableModels φ :=
  fun hP => h.ne hP.countableModelCount_eq

/-- If an infinitary sentence with countable branching has fewer than continuum many models on `ℕ`
up to isomorphism, its model class on `ℕ` is back-and-forth scattered. -/
theorem bfScattered_modelsOf_of_mk_quotient_lt_continuum [∀ n, Countable (L.Relations n)]
    [Countable ι] {φ : L.SentenceInf ι} (h : #(Quotient (isoSetoidOn ℕ φ)) < 𝔠) :
    BFScattered (modelsOf (V := ℕ) φ) :=
  (isThinOnNatModels_of_mk_quotient_lt_continuum h).bfScattered_modelsOf

end TauCeti
