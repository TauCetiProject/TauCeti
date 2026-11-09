/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Levels
public import TauCeti.ModelTheory.Counting.Stratification

/-!
# The bounded-rank dichotomy

On a set of relational configurations on `ℕ`, a countable bound on an isolating rank makes
isomorphism equal to one back-and-forth level. In a countable vocabulary that level is Borel,
so isomorphism has Borel graph on the set.

The set need not be measurable or isomorphism invariant: the graph is measurable for the
induced measurable structure on its square. To apply a dichotomy requiring a standard Borel
domain, the caller must separately establish that the set is Borel.

On a Borel set, Silver's theorem applied to that single level then gives the **bounded-rank
dichotomy**: the set meets countably many isomorphism classes, or it contains a nonempty perfect
set of pairwise non-isomorphic configurations. For the countable models of an infinitary sentence
`φ` with countable branching, combining this on the tier `ℕ` with the finite-carrier dichotomy on
each `Fin n` gives: if some isolating rank is bounded below `ω₁` on the models of `φ` on `ℕ`, then
`φ` has at most `ℵ₀` countable models up to isomorphism or perfectly many. The perfect alternative
may occur on a finite carrier only. Neither the continuum hypothesis nor its negation is used.
Conversely, countably many countable models bound every isolating rank, so for any isolating rank
the sentence has countably many countable models exactly when the rank is bounded and the sentence
does not have perfectly many countable models.

The Scott height supplies the canonical isolating rank. A bound `β` on the internal Scott rank
also suffices, but gives a bound `β + ω` on the Scott height, not necessarily `β` itself.
Countably many isomorphism classes give Borel isomorphism as well, since they bound every
isolating rank.

## Main results

* `TauCeti.IsIsolatingRank.measurableSet_setOf_comap_isoSetoid`: a bounded isolating rank gives
  a Borel isomorphism relation.
* `TauCeti.RelationalConfiguration.measurableSet_setOf_comap_isoSetoid_of_scottHeight_le` and
  `TauCeti.RelationalConfiguration.measurableSet_setOf_comap_isoSetoid_of_internalScottRank_le`:
  the external and internal Scott rank forms.
* `TauCeti.RelationalConfiguration.measurableSet_setOf_comap_isoSetoid_of_countable_isoClasses`:
  countably many isomorphism classes give a Borel isomorphism relation.
* `TauCeti.IsIsolatingRank.countable_isoClasses_or_hasPerfectAntichainOn`: the bounded-rank
  dichotomy for a Borel set of configurations on `ℕ`.
* `TauCeti.IsIsolatingRank.countableModelCount_le_aleph0_or_hasPerfectlyMany_of_bounded` and
  `TauCeti.IsIsolatingRank.countableModelCount_le_aleph0_or_eq_continuum_of_bounded`: the
  **bounded-rank dichotomy** for countable models, in witnessed and cardinal forms.
* `TauCeti.countableModelCount_le_aleph0_or_hasPerfectlyMany_of_scottHeight_le`,
  `TauCeti.countableModelCount_le_aleph0_or_eq_continuum_of_scottHeight_le`,
  `TauCeti.countableModelCount_le_aleph0_or_hasPerfectlyMany_of_internalScottRank_le` and
  `TauCeti.countableModelCount_le_aleph0_or_eq_continuum_of_internalScottRank_le`: the external
  and internal Scott rank forms.
* `TauCeti.IsIsolatingRank.countableModelCount_le_aleph0_iff_bounded_and_not_hasPerfectlyMany`:
  countably many countable models exactly when the rank is bounded and there is no perfect set.

## References

* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016,
  the chapter on the space of countable models.
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2,
  Chapter XII, §XII.1.
* J. H. Silver, *Counting the number of equivalence classes of Borel and coanalytic equivalence
  relations*, Annals of Mathematical Logic 18 (1980), 1–28.

The isolating-rank and Scott-height arguments use the APIs in
`TauCeti.ModelTheory.Counting.Stratification` and `TauCeti.ModelTheory.Scott.Height`; Silver's
theorem enters through the one-level dichotomies of `TauCeti.ModelTheory.Counting.Levels`.
-/

public section

universe u v uι

open FirstOrder Cardinal Ordinal Set

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]
  {K : Set (RelationalConfiguration L ℕ)} {β : Ordinal.{0}}

/-- A countable bound on an isolating rank makes isomorphism Borel on `K`, for the induced
measurable structure. No measurability or invariance of `K` is required. -/
theorem IsIsolatingRank.measurableSet_setOf_comap_isoSetoid
    {ρ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    (hβ : β < ω₁) (hK : ∀ c ∈ K, ρ c ≤ β) :
    MeasurableSet {p : K × K | (isoSetoid L ℕ).comap Subtype.val p.1 p.2} := by
  rw [hρ.comap_isoSetoid_eq_bfEquivSetoid hK]
  exact (measurableSet_setOf_bfEquivSetoid hβ).preimage
    ((measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd))

namespace RelationalConfiguration

/-- A countable uniform bound on the Scott heights of the decoded structures makes
isomorphism Borel on `K`. -/
theorem measurableSet_setOf_comap_isoSetoid_of_scottHeight_le (hβ : β < ω₁)
    (hK : ∀ c ∈ K, @scottHeight L _ ℕ c.toStructure ≤ β) :
    MeasurableSet {p : K × K | (isoSetoid L ℕ).comap Subtype.val p.1 p.2} :=
  (isIsolatingRank_scottHeight L).measurableSet_setOf_comap_isoSetoid hβ hK

/-- A countable bound on the internal Scott ranks of the decoded structures makes
isomorphism Borel on `K`. The associated bound on Scott height is `β + ω`. -/
theorem measurableSet_setOf_comap_isoSetoid_of_internalScottRank_le (hβ : β < ω₁)
    (hK : ∀ c ∈ K, @internalScottRank L _ ℕ c.toStructure ≤ β) :
    MeasurableSet {p : K × K | (isoSetoid L ℕ).comap Subtype.val p.1 p.2} := by
  apply measurableSet_setOf_comap_isoSetoid_of_scottHeight_le (β := β + ω)
    (Ordinal.isPrincipal_add_omega 1 hβ Ordinal.omega0_lt_omega_one)
  intro c hc
  exact (@scottHeight_le_internalScottRank_add_omega0 L _ ℕ c.toStructure).trans
    (add_le_add (hK c hc) le_rfl)

/-- On a set meeting countably many isomorphism classes, isomorphism has Borel graph for
its induced measurable structure, even if the set itself is not Borel. -/
theorem measurableSet_setOf_comap_isoSetoid_of_countable_isoClasses
    [Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _)))] :
    MeasurableSet {p : K × K | (isoSetoid L ℕ).comap Subtype.val p.1 p.2} := by
  obtain ⟨β, hβ, hb⟩ := exists_rank_bound_of_countable_isoClasses
    (isIsolatingRank_scottHeight L).iso_invariant
    (isIsolatingRank_scottHeight L).lt_omega_one K
  exact measurableSet_setOf_comap_isoSetoid_of_scottHeight_le hβ fun c hc => (hb c hc).le

end RelationalConfiguration

/-! ### The bounded-rank dichotomy -/

variable {ι : Type uι} {ρ : RelationalConfiguration L ℕ → Ordinal.{0}}

/-- **The bounded-rank dichotomy for Borel sets.** If an isolating rank is bounded below `ω₁` on a
Borel set `K` of configurations on `ℕ`, then `K` meets countably many isomorphism classes or
contains a nonempty perfect set of pairwise non-isomorphic configurations. No isomorphism
invariance of `K` is required. -/
theorem IsIsolatingRank.countable_isoClasses_or_hasPerfectAntichainOn (hρ : IsIsolatingRank ρ)
    (hK : MeasurableSet K) (hβ : β < ω₁) (hb : ∀ c ∈ K, ρ c ≤ β) :
    Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) ∨
      (isoSetoid L ℕ).HasPerfectAntichainOn K := by
  rw [hρ.comap_isoSetoid_eq_bfEquivSetoid hb]
  exact countable_quotient_comap_bfEquivSetoid_or_hasPerfectAntichainOn hK hβ

/-- **The bounded-rank dichotomy (witnessed form).** If an isolating rank is bounded below `ω₁` on
the models on `ℕ` of an infinitary sentence `φ` with countable branching, then `φ` has at most `ℵ₀`
countable models up to isomorphism, finite models included, or it has a nonempty perfect set of
pairwise non-isomorphic countable models at the tier `ℕ` or at some finite tier `Fin n`. -/
theorem IsIsolatingRank.countableModelCount_le_aleph0_or_hasPerfectlyMany_of_bounded
    [Countable ι] (hρ : IsIsolatingRank ρ) (φ : L.SentenceInf ι) (hβ : β < ω₁)
    (hb : ∀ c ∈ modelsOf (V := ℕ) φ, ρ c ≤ β) :
    countableModelCount φ ≤ ℵ₀ ∨ HasPerfectlyManyCountableModels φ := by
  rcases hρ.countable_isoClasses_or_hasPerfectAntichainOn (measurableSet_modelsOf φ) hβ hb with
    hℕ | hℕ
  · exact (forall_countable_quotient_isoSetoidOn_fin_or_exists_hasPerfectAntichainOn φ).imp
      (fun hfin => countableModelCount_le_aleph0_iff.2 ⟨hℕ, hfin⟩) fun ⟨_, hn⟩ => .of_fin hn
  · exact .inr (.of_nat hℕ)

/-- **The bounded-rank dichotomy (cardinal form).** If an isolating rank is bounded below `ω₁` on
the models on `ℕ` of an infinitary sentence `φ` with countable branching, then `φ` has either at
most `ℵ₀` or exactly `𝔠` countable models up to isomorphism. -/
theorem IsIsolatingRank.countableModelCount_le_aleph0_or_eq_continuum_of_bounded
    [Countable ι] (hρ : IsIsolatingRank ρ) (φ : L.SentenceInf ι) (hβ : β < ω₁)
    (hb : ∀ c ∈ modelsOf (V := ℕ) φ, ρ c ≤ β) :
    countableModelCount φ ≤ ℵ₀ ∨ countableModelCount φ = 𝔠 :=
  (hρ.countableModelCount_le_aleph0_or_hasPerfectlyMany_of_bounded φ hβ hb).imp_right
    HasPerfectlyManyCountableModels.countableModelCount_eq

/-- **The bounded-rank dichotomy for Scott height.** If the models on `ℕ` of an infinitary sentence
`φ` with countable branching have Scott height at most `β < ω₁`, then `φ` has at most `ℵ₀` countable
models up to isomorphism, or it has perfectly many countable models. -/
theorem countableModelCount_le_aleph0_or_hasPerfectlyMany_of_scottHeight_le [Countable ι]
    (φ : L.SentenceInf ι) (hβ : β < ω₁)
    (hb : ∀ c ∈ modelsOf (V := ℕ) φ, @scottHeight L _ ℕ c.toStructure ≤ β) :
    countableModelCount φ ≤ ℵ₀ ∨ HasPerfectlyManyCountableModels φ :=
  (isIsolatingRank_scottHeight L).countableModelCount_le_aleph0_or_hasPerfectlyMany_of_bounded φ
    hβ hb

/-- If the models on `ℕ` of an infinitary sentence `φ` with countable branching have Scott height
at most `β < ω₁`, then `φ` has either at most `ℵ₀` or exactly `𝔠` countable models up to
isomorphism. -/
theorem countableModelCount_le_aleph0_or_eq_continuum_of_scottHeight_le [Countable ι]
    (φ : L.SentenceInf ι) (hβ : β < ω₁)
    (hb : ∀ c ∈ modelsOf (V := ℕ) φ, @scottHeight L _ ℕ c.toStructure ≤ β) :
    countableModelCount φ ≤ ℵ₀ ∨ countableModelCount φ = 𝔠 :=
  (isIsolatingRank_scottHeight L).countableModelCount_le_aleph0_or_eq_continuum_of_bounded φ hβ hb

/-- **The bounded-rank dichotomy for internal Scott rank.** If the models on `ℕ` of an infinitary
sentence `φ` with countable branching have internal Scott rank at most `β < ω₁`, then `φ` has at
most `ℵ₀` countable models up to isomorphism, or it has perfectly many countable models. The
Scott heights are then bounded by `β + ω`. -/
theorem countableModelCount_le_aleph0_or_hasPerfectlyMany_of_internalScottRank_le [Countable ι]
    (φ : L.SentenceInf ι) (hβ : β < ω₁)
    (hb : ∀ c ∈ modelsOf (V := ℕ) φ, @internalScottRank L _ ℕ c.toStructure ≤ β) :
    countableModelCount φ ≤ ℵ₀ ∨ HasPerfectlyManyCountableModels φ :=
  countableModelCount_le_aleph0_or_hasPerfectlyMany_of_scottHeight_le φ
    (Ordinal.isPrincipal_add_omega 1 hβ Ordinal.omega0_lt_omega_one) fun c hc =>
      (@scottHeight_le_internalScottRank_add_omega0 L _ ℕ c.toStructure).trans
        (add_le_add (hb c hc) le_rfl)

/-- If the models on `ℕ` of an infinitary sentence `φ` with countable branching have internal Scott
rank at most `β < ω₁`, then `φ` has either at most `ℵ₀` or exactly `𝔠` countable models up to
isomorphism. -/
theorem countableModelCount_le_aleph0_or_eq_continuum_of_internalScottRank_le [Countable ι]
    (φ : L.SentenceInf ι) (hβ : β < ω₁)
    (hb : ∀ c ∈ modelsOf (V := ℕ) φ, @internalScottRank L _ ℕ c.toStructure ≤ β) :
    countableModelCount φ ≤ ℵ₀ ∨ countableModelCount φ = 𝔠 :=
  (countableModelCount_le_aleph0_or_hasPerfectlyMany_of_internalScottRank_le φ hβ hb).imp_right
    HasPerfectlyManyCountableModels.countableModelCount_eq

/-- For any isolating rank, an infinitary sentence `φ` with countable branching has at most `ℵ₀`
countable models up to isomorphism exactly when the rank is bounded below `ω₁` on the models of `φ`
on `ℕ` and `φ` does not have perfectly many countable models. -/
theorem IsIsolatingRank.countableModelCount_le_aleph0_iff_bounded_and_not_hasPerfectlyMany
    [Countable ι] (hρ : IsIsolatingRank ρ) (φ : L.SentenceInf ι) :
    countableModelCount φ ≤ ℵ₀ ↔
      (∃ β < ω₁, ∀ c ∈ modelsOf (V := ℕ) φ, ρ c < β) ∧ ¬ HasPerfectlyManyCountableModels φ := by
  refine ⟨fun h => ⟨?_, fun hP => ?_⟩, fun ⟨⟨β, hβ, hb⟩, hP⟩ =>
    (hρ.countableModelCount_le_aleph0_or_hasPerfectlyMany_of_bounded φ hβ
      fun c hc => (hb c hc).le).resolve_right hP⟩
  · have := (countableModelCount_le_aleph0_iff.1 h).1
    exact exists_rank_bound_of_countable_isoClasses hρ.iso_invariant hρ.lt_omega_one _
  · exact (h.trans_lt aleph0_lt_continuum).ne hP.countableModelCount_eq

end TauCeti
