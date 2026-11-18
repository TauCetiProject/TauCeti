/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Basic
public import TauCeti.ModelTheory.Counting.LanguageEquiv
public import TauCeti.ModelTheory.Counting.Morley
public import TauCeti.ModelTheory.Counting.Infinite
import TauCeti.ModelTheory.LanguageMap

/-!
# Vaught's conjecture and its cardinal form

`HasVaughtDichotomy φ` says that `φ` has countably many countable models up to isomorphism,
finite models included, or a perfect set of pairwise non-isomorphic countable models.
`HasVaughtCount φ` replaces the perfect-set alternative by a count of continuum many models.
The universally quantified statements for countable relational languages in universe zero are
`VaughtConjecture` and `CardinalVaughtConjecture`.

Morley's theorem characterizes a counterexample to the witnessed dichotomy as a sentence with
exactly `ℵ₁` countable models and no perfect set. Without assuming CH or its negation, any such
counterexample has a sharp structural profile on its countable models: it has countably many
finite models across all finite tiers `Fin n`, its model class on `ℕ` is thin and therefore
back-and-forth scattered (meeting only countably many classes at every countable back-and-forth
level `α < ω₁`), it has `ℵ₁` countably infinite models up to isomorphism, and every isolating
rank has countable fibres on its models on `ℕ` while being unbounded below `ω₁` there. A
counterexample to the cardinal dichotomy instead has `ℵ₁` countable models with `ℵ₁ < 𝔠`.
Consequently CH proves the cardinal conjecture, not the perfect-set conjecture; under `ℵ₁ < 𝔠`
the two conjectures are equivalent. None of the results here proves or refutes the perfect-set
conjecture.

The infinitude reduction `hasVaughtDichotomy_inf_infiniteSentence_iff` specializes the witnessed
statement to the tier `ℕ`. The finite-carrier dichotomy then gives `vaughtConjecture_iff_nat`,
so quantifying over all countable models is equivalent to quantifying over countably infinite
models. The reduction does not silently omit the finite tiers of an arbitrary sentence.

Finally, `HasVaughtDichotomy` and `HasVaughtCount` are invariant under language equivalences across
arbitrary universes. Combining `smallPresentationEquiv` (shrinking any countable language to
`Language.{0, 0}`) with `uliftEquiv` (lifting `Language.{0, 0}` into any target universes) shows
that `VaughtConjecture` and `CardinalVaughtConjecture` are equivalent to their statements quantified
over countable relational languages in any universe (`vaughtConjecture_iff_forall_universe`,
`cardinalVaughtConjecture_iff_forall_universe`).

## References

* R. L. Vaught, *Denumerable models of complete theories*, in Infinitistic Methods (1961),
  303–321, for the original first-order cardinal conjecture.
* J. R. Steel, *On Vaught's conjecture*, Cabal Seminar 76–77, Lecture Notes in Mathematics 689
  (1978), 193–208, for the perfect-set form.
* U. Andrews, I. Goldbring, S. Hachtman, H. J. Keisler and D. Marker,
  *Scattered sentences have few separable randomizations*, §§1–2, for the distinction between
  the cardinal, absolute and strong forms and their relationship to CH.
* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, the chapter
  on Vaught counterexamples, and A. Montalbán, *Computable Structure Theory: Beyond the
  Arithmetic*, Part 2, Chapter XII, §XII.1, for the scatteredness and rank profile of a Vaught
  counterexample.
-/

public section

universe u v u' v' o uι

open FirstOrder FirstOrder.Language Cardinal Ordinal

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {ι : Type uι}

/-- The perfect-set form of Vaught's dichotomy for one sentence: countably many countable
models up to isomorphism, or perfectly many. Finite and empty models are included. -/
def HasVaughtDichotomy (φ : L.SentenceInf ι) : Prop :=
  countableModelCount φ ≤ ℵ₀ ∨ HasPerfectlyManyCountableModels φ

/-- The characteristic alternatives of the witnessed dichotomy. -/
theorem hasVaughtDichotomy_iff {φ : L.SentenceInf ι} :
    HasVaughtDichotomy φ ↔ countableModelCount φ ≤ ℵ₀ ∨ HasPerfectlyManyCountableModels φ :=
  Iff.rfl

/-- The cardinal form of Vaught's dichotomy for one sentence: countably many or continuum many
countable models up to isomorphism, finite models included. -/
def HasVaughtCount (φ : L.SentenceInf ι) : Prop :=
  countableModelCount φ ≤ ℵ₀ ∨ countableModelCount φ = 𝔠

/-- The characteristic alternatives of the cardinal dichotomy. -/
theorem hasVaughtCount_iff {φ : L.SentenceInf ι} :
    HasVaughtCount φ ↔ countableModelCount φ ≤ ℵ₀ ∨ countableModelCount φ = 𝔠 :=
  Iff.rfl

/-- The witnessed dichotomy implies the cardinal dichotomy. No restriction on branching is
needed for this implication. -/
theorem HasVaughtDichotomy.cardinal [∀ n, Countable (L.Relations n)]
    {φ : L.SentenceInf ι} (h : HasVaughtDichotomy φ) : HasVaughtCount φ :=
  hasVaughtCount_iff.2 <| (hasVaughtDichotomy_iff.1 h).imp_right
    HasPerfectlyManyCountableModels.countableModelCount_eq

/-- A counterexample to the perfect-set dichotomy has exactly `ℵ₁` countable models and no
perfect set of pairwise non-isomorphic countable models. No CH hypothesis is needed. -/
theorem not_hasVaughtDichotomy_iff [∀ n, Countable (L.Relations n)] [Countable ι]
    {φ : L.SentenceInf ι} :
    ¬ HasVaughtDichotomy φ ↔
      countableModelCount φ = ℵ₁ ∧ ¬ HasPerfectlyManyCountableModels φ := by
  rw [hasVaughtDichotomy_iff, not_or, not_le]
  constructor
  · rintro ⟨hcount, hperfect⟩
    exact ⟨countableModelCount_eq_aleph_one_of_aleph0_lt_of_not_hasPerfectlyManyCountableModels
      hcount hperfect, hperfect⟩
  · rintro ⟨hcount, hperfect⟩
    exact ⟨hcount ▸ aleph0_lt_aleph_one, hperfect⟩

/-- A counterexample to the cardinal dichotomy has exactly `ℵ₁` countable models, strictly
fewer than continuum. In particular such a counterexample refutes CH. -/
theorem not_hasVaughtCount_iff [∀ n, Countable (L.Relations n)] [Countable ι]
    {φ : L.SentenceInf ι} :
    ¬ HasVaughtCount φ ↔ countableModelCount φ = ℵ₁ ∧ ℵ₁ < (𝔠 : Cardinal.{v}) := by
  rw [hasVaughtCount_iff, not_or, not_le]
  constructor
  · rintro ⟨hcount, hne⟩
    have hle := (morley_countableModelCount φ).resolve_right hne
    have heq := hle.antisymm (aleph_one_le_iff.2 hcount)
    refine ⟨heq, lt_of_le_of_ne aleph_one_le_continuum ?_⟩
    simpa only [heq] using hne
  · rintro ⟨hcount, hc⟩
    rw [hcount]
    exact ⟨aleph0_lt_aleph_one, hc.ne⟩

/-- Under CH every sentence with countable branching satisfies the cardinal dichotomy. -/
theorem hasVaughtCount_of_aleph_one_eq_continuum [∀ n, Countable (L.Relations n)]
    [Countable ι] (hCH : ℵ₁ = (𝔠 : Cardinal.{v})) (φ : L.SentenceInf ι) : HasVaughtCount φ := by
  by_contra h
  exact (not_hasVaughtCount_iff.1 h).2.ne hCH

/-- When `ℵ₁ < 𝔠`, the cardinal dichotomy for one sentence implies the witnessed dichotomy.
Morley's witnessed theorem supplies the perfect set, not a cardinality argument alone. -/
theorem hasVaughtCount_iff_hasVaughtDichotomy [∀ n, Countable (L.Relations n)] [Countable ι]
    (hc : ℵ₁ < (𝔠 : Cardinal.{v})) {φ : L.SentenceInf ι} :
    HasVaughtCount φ ↔ HasVaughtDichotomy φ := by
  refine ⟨fun h => ?_, HasVaughtDichotomy.cardinal⟩
  rcases hasVaughtCount_iff.1 h with hcount | hcount
  · exact hasVaughtDichotomy_iff.2 (.inl hcount)
  · rcases morley_countableModelCount_le_aleph_one_or_hasPerfectlyMany φ with hle | hperfect
    · exact (hc.not_ge (hcount ▸ hle)).elim
    · exact hasVaughtDichotomy_iff.2 (.inr hperfect)

/-- Conjoining infinitude turns the all-countable-model dichotomy into precisely the
countably-infinite-model dichotomy. This needs no countability assumption on the language. -/
@[simp]
theorem hasVaughtDichotomy_inf_infiniteSentence_iff (φ : L.Sentenceω) :
    HasVaughtDichotomy (φ ⊓ L.infiniteSentence) ↔
      Countable (Quotient (isoSetoidOn ℕ φ)) ∨
        (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOf φ) := by
  rw [hasVaughtDichotomy_iff, countableModelCount_inf_infiniteSentence,
    mk_le_aleph0_iff, hasPerfectlyManyCountableModels_inf_infiniteSentence_iff]

/-- A witnessed dichotomy on the infinite tier implies the all-countable-model dichotomy:
the finite tiers always satisfy their own witnessed dichotomy. -/
theorem hasVaughtDichotomy_of_nat [∀ n, Countable (L.Relations n)] [Countable ι]
    {φ : L.SentenceInf ι}
    (h : Countable (Quotient (isoSetoidOn ℕ φ)) ∨
      (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOf φ)) : HasVaughtDichotomy φ := by
  rcases h with hcount | hperfect
  · rcases forall_countable_quotient_isoSetoidOn_fin_or_exists_hasPerfectAntichainOn φ with
      hfin | ⟨n, hfin⟩
    · exact hasVaughtDichotomy_iff.2 (.inl (countableModelCount_le_aleph0_iff.2 ⟨hcount, hfin⟩))
    · exact hasVaughtDichotomy_iff.2 (.inr (.of_fin hfin))
  · exact hasVaughtDichotomy_iff.2 (.inr (.of_nat hperfect))

/-! ### Profile of a counterexample to Vaught's dichotomy -/

section CounterexampleProfile

/-- A sentence failing `HasVaughtDichotomy` has no perfect set of pairwise non-isomorphic countable
models at any tier. No countability hypothesis on the language or branching is needed. -/
theorem not_hasPerfectlyManyCountableModels_of_not_hasVaughtDichotomy {φ : L.SentenceInf ι}
    (h : ¬ HasVaughtDichotomy φ) : ¬ HasPerfectlyManyCountableModels φ :=
  fun hp => h (hasVaughtDichotomy_iff.2 (.inr hp))

/-- A counterexample to `HasVaughtDichotomy` has thin models on `ℕ`. -/
theorem isThinOnNatModels_of_not_hasVaughtDichotomy {φ : L.SentenceInf ι}
    (h : ¬ HasVaughtDichotomy φ) : IsThinOnNatModels φ :=
  .of_not_hasPerfectlyManyCountableModels
    (not_hasPerfectlyManyCountableModels_of_not_hasVaughtDichotomy h)

/-- A counterexample to `HasVaughtDichotomy` has thin models on every finite carrier `Fin n`. -/
theorem isThinOn_fin_modelsOf_of_not_hasVaughtDichotomy {φ : L.SentenceInf ι}
    (h : ¬ HasVaughtDichotomy φ) (n : ℕ) : (isoSetoid L (Fin n)).IsThinOn (modelsOf φ) :=
  (not_hasPerfectlyManyCountableModels_iff.1
    (not_hasPerfectlyManyCountableModels_of_not_hasVaughtDichotomy h)).2 n

variable [∀ n, Countable (L.Relations n)] [Countable ι] {φ : L.SentenceInf ι}

/-- A counterexample to `HasVaughtDichotomy` has back-and-forth scattered models on `ℕ`. -/
theorem bfScattered_modelsOf_of_not_hasVaughtDichotomy (h : ¬ HasVaughtDichotomy φ) :
    BFScattered (modelsOf (V := ℕ) φ) :=
  (isThinOnNatModels_of_not_hasVaughtDichotomy h).bfScattered_modelsOf

/-- A counterexample to `HasVaughtDichotomy` has countably many depth-`α` back-and-forth classes on
`ℕ` at every countable ordinal `α < ω₁`. -/
theorem countable_quotient_bfEquivSetoidOn_of_not_hasVaughtDichotomy
    (h : ¬ HasVaughtDichotomy φ) {α : Ordinal.{o}} (hα : α < ω₁) :
    Countable (Quotient (bfEquivSetoidOn ℕ φ α)) :=
  (isThinOnNatModels_of_not_hasVaughtDichotomy h).countable_quotient_bfEquivSetoidOn hα

/-- A counterexample to `HasVaughtDichotomy` has countably many models up to isomorphism on each
finite carrier `Fin n`. -/
theorem countable_quotient_isoSetoidOn_fin_of_not_hasVaughtDichotomy
    (h : ¬ HasVaughtDichotomy φ) (n : ℕ) :
    Countable (Quotient (isoSetoidOn (Fin n) φ)) :=
  countable_quotient_isoSetoidOn_fin_of_not_hasPerfectlyManyCountableModels
    (not_hasPerfectlyManyCountableModels_of_not_hasVaughtDichotomy h) n

/-- Across all finite carriers `Fin n` combined, a counterexample to `HasVaughtDichotomy` has
only countably many finite models up to isomorphism. -/
theorem countable_sigma_quotient_isoSetoidOn_fin_of_not_hasVaughtDichotomy
    (h : ¬ HasVaughtDichotomy φ) :
    Countable (Σ n : ℕ, Quotient (isoSetoidOn (Fin n) φ)) :=
  have := countable_quotient_isoSetoidOn_fin_of_not_hasVaughtDichotomy h
  inferInstance

/-- A counterexample to `HasVaughtDichotomy` has uncountably many countably infinite models on `ℕ`
up to isomorphism. -/
theorem not_countable_quotient_isoSetoidOn_nat_of_not_hasVaughtDichotomy
    (h : ¬ HasVaughtDichotomy φ) :
    ¬ Countable (Quotient (isoSetoidOn ℕ φ)) :=
  fun hc => h (hasVaughtDichotomy_of_nat (.inl hc))

/-- A counterexample to `HasVaughtDichotomy` has `ℵ₁` countably infinite models on `ℕ` up to
isomorphism, without assuming CH or its negation. -/
theorem mk_quotient_isoSetoidOn_nat_eq_aleph_one_of_not_hasVaughtDichotomy
    (h : ¬ HasVaughtDichotomy φ) :
    #(Quotient (isoSetoidOn ℕ φ)) = ℵ₁ := by
  have : Uncountable (Quotient (isoSetoidOn ℕ φ)) :=
    not_countable_iff.1 (not_countable_quotient_isoSetoidOn_nat_of_not_hasVaughtDichotomy h)
  exact (isThinOnNatModels_of_not_hasVaughtDichotomy h).mk_quotient_isoSetoidOn_eq_aleph_one

/-- On a counterexample to `HasVaughtDichotomy`, every isolating rank has countable fibres on the
isomorphism classes of models on `ℕ`. -/
theorem IsIsolatingRank.countable_rankOnIsoClasses_preimage_of_not_hasVaughtDichotomy
    {ρ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    (h : ¬ HasVaughtDichotomy φ) (α : Ordinal.{0}) :
    (rankOnIsoClasses hρ.iso_invariant (modelsOf (V := ℕ) φ) ⁻¹' {α}).Countable :=
  hρ.countable_rankOnIsoClasses_preimage (bfScattered_modelsOf_of_not_hasVaughtDichotomy h) α

/-- On a counterexample to `HasVaughtDichotomy`, no countable ordinal bounds any isolating rank on
the models on `ℕ`. -/
theorem IsIsolatingRank.not_exists_rank_bound_of_not_hasVaughtDichotomy
    {ρ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    (h : ¬ HasVaughtDichotomy φ) :
    ¬ ∃ β < ω₁, ∀ c ∈ modelsOf (V := ℕ) φ, ρ c < β :=
  fun hb => not_countable_quotient_isoSetoidOn_nat_of_not_hasVaughtDichotomy h <|
    ((isThinOnNatModels_of_not_hasVaughtDichotomy h).countable_quotient_isoSetoidOn_iff_bounded
      hρ).2 hb

/-- **Every isolating rank is unbounded below `ω₁` on a Vaught counterexample.** If `φ` fails
`HasVaughtDichotomy`, then for every isolating rank `ρ` and every countable ordinal `β < ω₁`, some
model of `φ` on `ℕ` has rank strictly above `β`. -/
theorem IsIsolatingRank.exists_gt_of_not_hasVaughtDichotomy
    {ρ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    (h : ¬ HasVaughtDichotomy φ) {β : Ordinal.{0}} (hβ : β < ω₁) :
    ∃ c ∈ modelsOf (V := ℕ) φ, β < ρ c := by
  by_contra! hle
  have hcount : Countable (Quotient (isoSetoidOn ℕ φ)) := by
    rw [isoSetoidOn, hρ.comap_isoSetoid_eq_bfEquivSetoid hle]
    exact (bfScattered_modelsOf_of_not_hasVaughtDichotomy h).countable_quotient hβ
  exact not_countable_quotient_isoSetoidOn_nat_of_not_hasVaughtDichotomy h hcount

/-- **Internal Scott rank is unbounded below `ω₁` on a Vaught counterexample.** Even though
`internalScottRank` only bounds `scottHeight` up to `+ ω` rather than being an isolating rank
directly, for every `β < ω₁` some model of `φ` on `ℕ` has internal Scott rank strictly above
`β`. -/
theorem exists_lt_internalScottRank_of_not_hasVaughtDichotomy
    (h : ¬ HasVaughtDichotomy φ) {β : Ordinal.{0}} (hβ : β < ω₁) :
    ∃ c ∈ modelsOf (V := ℕ) φ, β < @internalScottRank L _ ℕ c.toStructure := by
  obtain ⟨c, hc, hlt⟩ := (isIsolatingRank_scottHeight L).exists_gt_of_not_hasVaughtDichotomy h
    (Ordinal.isPrincipal_add_omega 1 hβ Ordinal.omega0_lt_omega_one)
  refine ⟨c, hc, not_le.1 fun hle => not_le_of_gt hlt ?_⟩
  exact (@scottHeight_le_internalScottRank_add_omega0 L _ ℕ c.toStructure).trans
    (add_le_add hle le_rfl)

end CounterexampleProfile

end TauCeti

/-! ### Invariance along language equivalences -/

namespace FirstOrder.Language.LEquiv

open TauCeti

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L.IsRelational] [L'.IsRelational]
  (e : L ≃ᴸ L') {ι : Type uι}

/-- **Vaught's witnessed dichotomy along a language equivalence.** The translation of an infinitary
sentence along a language equivalence of relational languages satisfies `HasVaughtDichotomy` if and
only if the sentence does, with no countability assumptions on the languages or branching. -/
@[simp]
theorem hasVaughtDichotomy_onBoundedFormulaInf_iff (φ : L.SentenceInf ι) :
    HasVaughtDichotomy (e.toLHom.onBoundedFormulaInf φ) ↔ HasVaughtDichotomy φ := by
  rw [hasVaughtDichotomy_iff, hasVaughtDichotomy_iff,
    ← Cardinal.lift_le_aleph0.{v', v}, ← e.lift_countableModelCount_onBoundedFormulaInf φ,
    Cardinal.lift_le_aleph0, e.hasPerfectlyManyCountableModels_onBoundedFormulaInf_iff φ]

/-- **Vaught's cardinal dichotomy along a language equivalence.** The translation of an infinitary
sentence along a language equivalence of relational languages satisfies `HasVaughtCount` if and
only if the sentence does, with no countability assumptions on the languages or branching. -/
@[simp]
theorem hasVaughtCount_onBoundedFormulaInf_iff (φ : L.SentenceInf ι) :
    HasVaughtCount (e.toLHom.onBoundedFormulaInf φ) ↔ HasVaughtCount φ := by
  have heq : countableModelCount (e.toLHom.onBoundedFormulaInf φ) = 𝔠 ↔
      countableModelCount φ = 𝔠 := by
    rw [← Cardinal.lift_inj.{v', v}, Cardinal.lift_continuum,
      ← e.lift_countableModelCount_onBoundedFormulaInf φ, ← Cardinal.lift_continuum.{v', v},
      Cardinal.lift_inj]
  rw [hasVaughtCount_iff, hasVaughtCount_iff,
    ← Cardinal.lift_le_aleph0.{v', v}, ← e.lift_countableModelCount_onBoundedFormulaInf φ,
    Cardinal.lift_le_aleph0, heq]

end FirstOrder.Language.LEquiv

namespace TauCeti

open RelationalConfiguration

/-! ### Global statements and universe invariance -/

/-- Vaught's conjecture in perfect-set form for all countable relational languages in universe
zero and all `L_{ω₁ω}` sentences. The count includes all finite carriers and the empty carrier.
This is an open conjecture, not an assertion made by the library. -/
def VaughtConjecture : Prop :=
  ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
    (φ : L.Sentenceω), HasVaughtDichotomy φ

/-- The quantifiers in the perfect-set conjecture. -/
theorem vaughtConjecture_iff :
    VaughtConjecture ↔ ∀ (L : Language.{0, 0}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω), HasVaughtDichotomy φ :=
  Iff.rfl

/-- The cardinal Vaught conjecture for all countable relational languages in universe zero.
Unlike the perfect-set conjecture, this statement follows from CH. -/
def CardinalVaughtConjecture : Prop :=
  ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
    (φ : L.Sentenceω), HasVaughtCount φ

/-- The quantifiers in the cardinal conjecture. -/
theorem cardinalVaughtConjecture_iff :
    CardinalVaughtConjecture ↔ ∀ (L : Language.{0, 0}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω), HasVaughtCount φ :=
  Iff.rfl

/-- The perfect-set Vaught conjecture implies its cardinal form. -/
theorem VaughtConjecture.cardinal (h : VaughtConjecture) : CardinalVaughtConjecture := by
  intro L _ _ φ
  exact (h L φ).cardinal

/-- CH implies the cardinal Vaught conjecture, without settling the perfect-set conjecture. -/
theorem cardinalVaughtConjecture_of_aleph_one_eq_continuum
    (hCH : ℵ₁ = (𝔠 : Cardinal.{0})) : CardinalVaughtConjecture := by
  intro L _ _ φ
  exact hasVaughtCount_of_aleph_one_eq_continuum hCH φ

/-- Under `ℵ₁ < 𝔠`, the cardinal and perfect-set Vaught conjectures are equivalent. -/
theorem cardinalVaughtConjecture_iff_vaughtConjecture (hc : ℵ₁ < (𝔠 : Cardinal.{0})) :
    CardinalVaughtConjecture ↔ VaughtConjecture := by
  refine ⟨fun h L _ _ φ => ?_, VaughtConjecture.cardinal⟩
  exact (hasVaughtCount_iff_hasVaughtDichotomy hc).1 (h L φ)

/-- Vaught's conjecture is equivalent to its statement for countably infinite models. The
reverse implication uses the finite-tier dichotomy; the forward implication applies the
conjecture to the conjunction with infinitude. -/
theorem vaughtConjecture_iff_nat :
    VaughtConjecture ↔ ∀ (L : Language.{0, 0}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω),
      Countable (Quotient (isoSetoidOn ℕ φ)) ∨
        (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOf φ) := by
  constructor
  · intro h L _ _ φ
    exact (hasVaughtDichotomy_inf_infiniteSentence_iff φ).1 (h L (φ ⊓ L.infiniteSentence))
  · intro h L _ _ φ
    exact hasVaughtDichotomy_of_nat (h L φ)

/-- **Universe invariance of Vaught's conjecture.** Quantifying over countable relational languages
in universe zero is equivalent to quantifying over countable relational languages in any fixed pair
of universes `u, v`. -/
theorem vaughtConjecture_iff_forall_universe :
    VaughtConjecture ↔ ∀ (L : Language.{u, v}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω), HasVaughtDichotomy φ := by
  constructor
  · intro h L _ _ φ
    exact (L.smallPresentationEquiv.hasVaughtDichotomy_onBoundedFormulaInf_iff φ).1
      (h L.smallPresentation (L.smallPresentationEquiv.toLHom.onBoundedFormulaInf φ))
  · intro h L₀ _ _ φ₀
    exact (L₀.uliftEquiv.{u, v}.hasVaughtDichotomy_onBoundedFormulaInf_iff φ₀).1
      (h (L₀.ulift.{u, v}) (L₀.uliftEquiv.{u, v}.toLHom.onBoundedFormulaInf φ₀))

/-- **Universe invariance of the cardinal Vaught conjecture.** Quantifying over countable
relational languages in universe zero is equivalent to quantifying over countable relational
languages in any fixed pair of universes `u, v`. -/
theorem cardinalVaughtConjecture_iff_forall_universe :
    CardinalVaughtConjecture ↔ ∀ (L : Language.{u, v}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω), HasVaughtCount φ := by
  constructor
  · intro h L _ _ φ
    exact (L.smallPresentationEquiv.hasVaughtCount_onBoundedFormulaInf_iff φ).1
      (h L.smallPresentation (L.smallPresentationEquiv.toLHom.onBoundedFormulaInf φ))
  · intro h L₀ _ _ φ₀
    exact (L₀.uliftEquiv.{u, v}.hasVaughtCount_onBoundedFormulaInf_iff φ₀).1
      (h (L₀.ulift.{u, v}) (L₀.uliftEquiv.{u, v}.toLHom.onBoundedFormulaInf φ₀))

end TauCeti
