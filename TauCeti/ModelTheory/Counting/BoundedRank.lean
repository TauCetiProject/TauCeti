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
so isomorphism has Borel graph on the set, and Silver's theorem applies to it directly.

The set need not be measurable or isomorphism invariant for the graph to be Borel: the graph is
measurable for the induced measurable structure on its square. To apply a dichotomy requiring a
standard Borel domain, the set itself must be Borel, as model classes are.

The Scott height supplies the canonical isolating rank. A bound `β` on the internal Scott rank
also suffices, but gives a bound `β + ω` on the Scott height, not necessarily `β` itself.
Countably many isomorphism classes give Borel isomorphism as well, since they bound every
isolating rank.

The **bounded-rank dichotomy** follows. If an isolating rank is bounded below `ω₁` on the models
on `ℕ` of an infinitary sentence `φ` with countable branching, in a vocabulary with countably many
relation symbols of each arity, then `φ` has at most `ℵ₀` countable models up to isomorphism, or a
nonempty perfect set of pairwise non-isomorphic countable models. On `ℕ` this is Silver's theorem
for the Borel relation of isomorphism on the model class; on each finite carrier `Fin n` it is the
finite-carrier dichotomy, which needs no bound. The perfect set may lie on a finite carrier only:
the bound says nothing about the finite models. Conversely, countably many countable models bound
every isomorphism-invariant countable rank on the models on `ℕ`.

## Main results

* `TauCeti.IsIsolatingRank.measurableSet_setOf_comap_isoSetoid`: a bounded isolating rank gives
  a Borel isomorphism relation.
* `TauCeti.RelationalConfiguration.measurableSet_setOf_comap_isoSetoid_of_scottHeight_le` and
  `TauCeti.RelationalConfiguration.measurableSet_setOf_comap_isoSetoid_of_internalScottRank_le`:
  the external and internal Scott rank forms.
* `TauCeti.RelationalConfiguration.measurableSet_setOf_comap_isoSetoid_of_countable_isoClasses`:
  countably many isomorphism classes give a Borel isomorphism relation.
* `TauCeti.IsIsolatingRank.countable_isoClasses_or_hasPerfectAntichainOn` and
  `TauCeti.IsIsolatingRank.mk_isoClasses_le_aleph0_or_eq_continuum`: a Borel set of configurations
  on `ℕ` of bounded rank meets countably many isomorphism classes or contains a nonempty perfect
  set of pairwise non-isomorphic configurations (hence `≤ ℵ₀` or `= 𝔠` classes).
* `TauCeti.countableModelCount_le_aleph0_or_hasPerfectlyMany_of_bounded`: **the bounded-rank
  dichotomy**, witnessed form.
* `TauCeti.countableModelCount_le_aleph0_or_eq_continuum_of_bounded` and
  `TauCeti.countableModelCount_le_aleph0_or_eq_continuum_of_bounded'`: its cardinal form, from the
  witnessed form and, independently, from the cardinality form of Silver's theorem.
* `TauCeti.countableModelCount_le_aleph0_or_hasPerfectlyMany_of_scottHeight_le` and
  `TauCeti.countableModelCount_le_aleph0_or_hasPerfectlyMany_of_internalScottRank_le`: the forms
  with a bound on the Scott height or on the internal Scott rank of the countably infinite models.
* `TauCeti.exists_rank_bound_of_countableModelCount_le_aleph0` and
  `TauCeti.countableModelCount_le_aleph0_iff_exists_rank_bound`: the converse, and the resulting
  characterization of countably many countable models for a sentence without a perfect set of
  pairwise non-isomorphic countable models.

## References

* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016,
  the chapter on the space of countable models.
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2,
  Chapter XII, §XII.1.
* J. H. Silver, *Counting the number of equivalence classes of Borel and coanalytic equivalence
  relations*, Annals of Mathematical Logic 18 (1980), 1–28.

The isolating-rank and Scott-height arguments use the APIs in
`TauCeti.ModelTheory.Counting.Stratification` and `TauCeti.ModelTheory.Scott.Height`; the
one-level forms of Silver's theorem are those of `TauCeti.ModelTheory.Counting.Levels`.
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

/-! ### Borel sets of bounded rank -/

/-- **The bounded-rank dichotomy for Borel sets on `ℕ`.** In a vocabulary with countably many
relation symbols of each arity, a Borel set `K` of configurations on `ℕ` on which an isolating
rank is bounded below `ω₁` meets countably many isomorphism classes, or contains a nonempty
perfect set of pairwise non-isomorphic configurations. -/
theorem IsIsolatingRank.countable_isoClasses_or_hasPerfectAntichainOn
    {ρ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    (hK : MeasurableSet K) (hβ : β < ω₁) (hKρ : ∀ c ∈ K, ρ c ≤ β) :
    Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) ∨
      (isoSetoid L ℕ).HasPerfectAntichainOn K := by
  rw [hρ.comap_isoSetoid_eq_bfEquivSetoid hKρ]
  exact countable_quotient_comap_bfEquivSetoid_or_hasPerfectAntichainOn hK hβ

/-- **The cardinal bounded-rank dichotomy for Borel sets on `ℕ`.** In a vocabulary with countably
many relation symbols of each arity, a Borel set `K` of configurations on `ℕ` on which an
isolating rank is bounded below `ω₁` meets either at most `ℵ₀` or `𝔠` isomorphism classes. This
is the cardinality form of Silver's theorem for the Borel relation of isomorphism on `K`. -/
theorem IsIsolatingRank.mk_isoClasses_le_aleph0_or_eq_continuum
    {ρ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    (hK : MeasurableSet K) (hβ : β < ω₁) (hKρ : ∀ c ∈ K, ρ c ≤ β) :
    #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) ≤ ℵ₀ ∨
      #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) = 𝔠 := by
  rw [hρ.comap_isoSetoid_eq_bfEquivSetoid hKρ]
  exact mk_quotient_comap_bfEquivSetoid_le_aleph0_or_eq_continuum hK hβ

/-! ### The bounded-rank dichotomy for sentences -/

section Sentences

variable {ι : Type uι} [Countable ι] {φ : L.SentenceInf ι}
  {ρ : RelationalConfiguration L ℕ → Ordinal.{0}}

/-- **The bounded-rank dichotomy.** In a vocabulary with countably many relation symbols of each
arity, if an isolating rank is bounded below `ω₁` on the models on `ℕ` of an infinitary sentence
`φ` with countable branching, then `φ` has at most `ℵ₀` countable models up to isomorphism, finite
models included, or a nonempty perfect set of pairwise non-isomorphic countable models at the
tier `ℕ` or at some finite tier `Fin n`. -/
theorem countableModelCount_le_aleph0_or_hasPerfectlyMany_of_bounded (hρ : IsIsolatingRank ρ)
    (hβ : β < ω₁) (hφ : ∀ c ∈ modelsOf (V := ℕ) φ, ρ c ≤ β) :
    countableModelCount φ ≤ ℵ₀ ∨ HasPerfectlyManyCountableModels φ := by
  rcases hρ.countable_isoClasses_or_hasPerfectAntichainOn (measurableSet_modelsOf φ) hβ hφ with
    hℕ | hℕ
  · rcases forall_countable_quotient_isoSetoidOn_fin_or_exists_hasPerfectAntichainOn φ with
      hfin | ⟨_, hn⟩
    · exact .inl (countableModelCount_le_aleph0_iff.2 ⟨hℕ, hfin⟩)
    · exact .inr (.of_fin hn)
  · exact .inr (.of_nat hℕ)

/-- **The cardinal bounded-rank dichotomy.** In a vocabulary with countably many relation symbols
of each arity, if an isolating rank is bounded below `ω₁` on the models on `ℕ` of an infinitary
sentence `φ` with countable branching, then `φ` has either at most `ℵ₀` or exactly `𝔠` countable
models up to isomorphism. -/
theorem countableModelCount_le_aleph0_or_eq_continuum_of_bounded (hρ : IsIsolatingRank ρ)
    (hβ : β < ω₁) (hφ : ∀ c ∈ modelsOf (V := ℕ) φ, ρ c ≤ β) :
    countableModelCount φ ≤ ℵ₀ ∨ countableModelCount φ = 𝔠 :=
  (countableModelCount_le_aleph0_or_hasPerfectlyMany_of_bounded hρ hβ hφ).imp_right
    HasPerfectlyManyCountableModels.countableModelCount_eq

/-- The cardinal bounded-rank dichotomy, obtained tier by tier from the cardinality form of
Silver's theorem rather than from perfect sets. The statement is that of
`TauCeti.countableModelCount_le_aleph0_or_eq_continuum_of_bounded`. -/
theorem countableModelCount_le_aleph0_or_eq_continuum_of_bounded' (hρ : IsIsolatingRank ρ)
    (hβ : β < ω₁) (hφ : ∀ c ∈ modelsOf (V := ℕ) φ, ρ c ≤ β) :
    countableModelCount φ ≤ ℵ₀ ∨ countableModelCount φ = 𝔠 := by
  have hfin := sum_mk_quotient_isoSetoidOn_fin_le_aleph0_or_eq_continuum φ
  rw [countableModelCount_eq_add_sum]
  rcases hρ.mk_isoClasses_le_aleph0_or_eq_continuum (measurableSet_modelsOf φ) hβ hφ with
    hℕ | hℕ
  · rcases hfin with hfin | hfin
    · exact .inl ((add_le_add hℕ hfin).trans_eq aleph0_add_aleph0)
    · rw [hfin]
      exact .inr (Cardinal.add_eq_right aleph0_le_continuum (hℕ.trans aleph0_le_continuum))
  · rw [hℕ]
    exact .inr (Cardinal.add_eq_left aleph0_le_continuum
      (hfin.elim (fun h => h.trans aleph0_le_continuum) le_of_eq))

/-- **The bounded-rank dichotomy for Scott height.** In a vocabulary with countably many relation
symbols of each arity, if every countably infinite model `M : Type` of an infinitary sentence `φ`
with countable branching has Scott height at most `β < ω₁`, then `φ` has at most `ℵ₀` countable
models up to isomorphism or a nonempty perfect set of pairwise non-isomorphic countable models. -/
theorem countableModelCount_le_aleph0_or_hasPerfectlyMany_of_scottHeight_le (hβ : β < ω₁)
    (hφ : ∀ (M : Type) [L.Structure M] [Countable M] [Infinite M], φ.Realize M →
      scottHeight (L := L) M ≤ β) :
    countableModelCount φ ≤ ℵ₀ ∨ HasPerfectlyManyCountableModels φ :=
  countableModelCount_le_aleph0_or_hasPerfectlyMany_of_bounded (isIsolatingRank_scottHeight L) hβ
    fun c hc => @hφ ℕ c.toStructure _ _ (mem_modelsOf.1 hc)

/-- **The bounded-rank dichotomy for internal Scott rank.** In a vocabulary with countably many
relation symbols of each arity, if every countably infinite model `M : Type` of an infinitary
sentence `φ` with countable branching has internal Scott rank at most `β < ω₁`, then `φ` has at
most `ℵ₀` countable models up to isomorphism or a nonempty perfect set of pairwise
non-isomorphic countable models. The Scott heights of these models are then at most `β + ω`. -/
theorem countableModelCount_le_aleph0_or_hasPerfectlyMany_of_internalScottRank_le (hβ : β < ω₁)
    (hφ : ∀ (M : Type) [L.Structure M] [Countable M] [Infinite M], φ.Realize M →
      internalScottRank (L := L) M ≤ β) :
    countableModelCount φ ≤ ℵ₀ ∨ HasPerfectlyManyCountableModels φ :=
  countableModelCount_le_aleph0_or_hasPerfectlyMany_of_scottHeight_le
    (Ordinal.isPrincipal_add_omega 1 hβ Ordinal.omega0_lt_omega_one)
    fun M _ _ _ hM => (scottHeight_le_internalScottRank_add_omega0 M).trans
      (add_le_add (hφ M hM) le_rfl)

omit [Countable ι] [∀ n, Countable (L.Relations n)] in
/-- **Countably many countable models bound every rank.** If `φ` has at most `ℵ₀` countable
models up to isomorphism, every isomorphism-invariant rank with countable values is bounded
strictly below one countable ordinal on the models of `φ` on `ℕ`. -/
theorem exists_rank_bound_of_countableModelCount_le_aleph0
    (hinv : ∀ ⦃c d⦄, isoSetoid L ℕ c d → ρ c = ρ d) (hρ : ∀ c, ρ c < ω₁)
    (h : countableModelCount φ ≤ ℵ₀) :
    ∃ β < ω₁, ∀ c ∈ modelsOf (V := ℕ) φ, ρ c < β :=
  have := (countableModelCount_le_aleph0_iff.1 h).1
  exists_rank_bound_of_countable_isoClasses hinv hρ _

/-- For a sentence without a perfect set of pairwise non-isomorphic countable models, in a
vocabulary with countably many relation symbols of each arity, there are at most `ℵ₀` countable
models up to isomorphism exactly when a given isolating rank is bounded below `ω₁` on the models
on `ℕ`. -/
theorem countableModelCount_le_aleph0_iff_exists_rank_bound (hρ : IsIsolatingRank ρ)
    (h : ¬ HasPerfectlyManyCountableModels φ) :
    countableModelCount φ ≤ ℵ₀ ↔ ∃ β < ω₁, ∀ c ∈ modelsOf (V := ℕ) φ, ρ c < β := by
  refine ⟨exists_rank_bound_of_countableModelCount_le_aleph0 hρ.iso_invariant hρ.lt_omega_one,
    fun ⟨β, hβ, hφ⟩ => ?_⟩
  exact (countableModelCount_le_aleph0_or_hasPerfectlyMany_of_bounded hρ hβ
    fun c hc => (hφ c hc).le).resolve_right h

end Sentences

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

end TauCeti
