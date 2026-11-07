/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Basic
public import TauCeti.ModelTheory.Counting.Morley
public import TauCeti.ModelTheory.Counting.Infinite

/-!
# Vaught's conjecture and its cardinal form

`HasVaughtDichotomy φ` says that `φ` has countably many countable models up to isomorphism,
finite models included, or a perfect set of pairwise non-isomorphic countable models.
`HasVaughtCount φ` replaces the perfect-set alternative by a count of continuum many models.
The universally quantified statements for countable relational languages in universe zero are
`VaughtConjecture` and `CardinalVaughtConjecture`.

Morley's theorem characterizes a counterexample to the witnessed dichotomy as a sentence with
exactly `ℵ₁` countable models and no perfect set. A counterexample to the cardinal dichotomy
instead has exactly `ℵ₁` countable models with `ℵ₁ < 𝔠`. Consequently CH proves the cardinal
conjecture, not the perfect-set conjecture; under `ℵ₁ < 𝔠` the two conjectures are equivalent.
None of the results here proves or refutes the perfect-set conjecture.

The infinitude reduction `hasVaughtDichotomy_inf_infiniteSentence_iff` specializes the witnessed
statement to the tier `ℕ`. The finite-carrier dichotomy then gives `vaughtConjecture_iff_nat`,
so quantifying over all countable models is equivalent to quantifying over countably infinite
models. The reduction does not silently omit the finite tiers of an arbitrary sentence.

## References

* R. L. Vaught, *Denumerable models of complete theories*, in Infinitistic Methods (1961),
  303–321, for the original first-order cardinal conjecture.
* J. R. Steel, *On Vaught's conjecture*, Cabal Seminar 76–77, Lecture Notes in Mathematics 689
  (1978), 193–208, for the perfect-set form.
* U. Andrews, I. Goldbring, S. Hachtman, H. J. Keisler and D. Marker,
  *Scattered sentences have few separable randomizations*, §§1–2, for the distinction between
  the cardinal, absolute and strong forms and their relationship to CH.
-/

public section

universe u v uι

open FirstOrder FirstOrder.Language Cardinal

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

end TauCeti
