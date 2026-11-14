/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.LopezEscobar
public import TauCeti.SetTheory.Descriptive.Silver
import TauCeti.Data.Set.Countable

/-!
# Sentence spectra, Borel observables, and thinness of configuration classes

Given a countable sequence of infinitary sentences `θ : ℕ → L.SentenceInf ι`, each relational
configuration `c` on a carrier `V` determines a Cantor-space point
`sentenceTheory θ c : ℕ → Bool` recording which sentences `θ n` hold in `c.toStructure`. When the
branching index `ι` and the carrier `V` are countable, `sentenceTheory θ` is Borel measurable and
constant on isomorphism classes.

In a countable relational vocabulary on a countable carrier `V`, relative López–Escobar
(`exists_modelsOf_preimage_eq`) upgrades this construction to a universal property for Borel
invariants:

* **Borel Cantor observables (`exists_sentenceTheory_comp_eq`).** Every measurable map
  `g : X → ℕ → Bool` from a standard Borel space `X` that is invariant across the isomorphism
  fibres of a measurable map `f : X → RelationalConfiguration L V` is realized coordinatewise as
  `fun x => sentenceTheory θ (f x)` for some countable sequence `θ : ℕ → L.Sentenceω`.
* **Cantor recovery (`exists_sentenceTheory_comp_eq_id`).** Along any measurable map
  `f : (ℕ → Bool) → RelationalConfiguration L V` sending distinct Cantor-space points to
  non-isomorphic configurations, some sequence `θ : ℕ → L.Sentenceω` recovers every point `x`
  identically (`sentenceTheory θ (f x) = x`).
* **Sentence-spectrum characterization (`isThinOn_iff_countable_image_sentenceTheory`).**
  Combining Cantor recovery with the relative form of Silver's theorem
  (`Setoid.countable_or_hasCantorAntichainOn_of_measurableSet`), a Borel set
  `C : Set (RelationalConfiguration L V)` is thin for isomorphism (`(isoSetoid L V).IsThinOn C`) if
  and only if every countable `L_{ω₁ω}` sentence sequence `θ` takes only countably many truth-value
  patterns `sentenceTheory θ '' C` on `C`. The backward implication holds without measurability of
  `C` (`isThinOn_of_countable_image_sentenceTheory`).
* **Single-sentence splits (`isThinOn_of_sentence_splits`).** If every single `L_{ω₁ω}` sentence
  splits an abstract invariant presentation of `C` (in particular, the isomorphism classes met by
  `C` in `isThinOn_of_countable_image_quotientMk_inter_or_diff`) with at least one countable side,
  then `C` carries no Cantor antichain and is thin—with no measurability or invariance hypothesis
  on `C`.
* **Smoothness and complete invariants (`isSmooth_comap_isoSetoid_iff_exists_sentenceTheory`).**
  Isomorphism restricted to a Borel set `C` is smooth (`Setoid.IsSmooth`) if and only if some
  countable `L_{ω₁ω}` sentence sequence `θ` is a complete isomorphism invariant on `C`; when `C` is
  also thin, `C` meets only countably many isomorphism classes
  (`countable_quotient_comap_isoSetoid_of_isThinOn_of_isSmooth`).

## Main definitions

* `TauCeti.RelationalConfiguration.sentenceTheory`: the Boolean truth-value trace
  `ℕ → Bool` of a countable sequence of sentences on a relational configuration.

## Main results

* `TauCeti.RelationalConfiguration.measurable_sentenceTheory` and
  `TauCeti.RelationalConfiguration.sentenceTheory_eq_of_isoSetoid`: measurability and isomorphism
  invariance of `sentenceTheory`.
* `TauCeti.RelationalConfiguration.exists_sentenceTheory_comp_eq` and
  `TauCeti.RelationalConfiguration.exists_sentenceTheory_comp_eq_id`: Borel Cantor observables and
  Cantor recovery by `L_{ω₁ω}` sentence sequences.
* `TauCeti.RelationalConfiguration.isThinOn_iff_countable_image_sentenceTheory`: Borel sets of
  configurations are thin iff every countable `L_{ω₁ω}` sentence spectrum on them is countable.
* `TauCeti.RelationalConfiguration.isThinOn_of_sentence_splits` and
  `TauCeti.RelationalConfiguration.isThinOn_of_countable_image_quotientMk_inter_or_diff`:
  single-sentence splits with a countable side force thinness unconditionally on the set.
* `TauCeti.RelationalConfiguration.isSmooth_comap_isoSetoid_iff_exists_sentenceTheory` and
  `TauCeti.RelationalConfiguration.countable_quotient_comap_isoSetoid_of_isThinOn_of_isSmooth`:
  smoothness via complete `L_{ω₁ω}` sentence invariants, and countability of thin smooth classes.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fund. Math. 57
  (1965), 253–272.
* V. Harnik and M. Makkai, *Applications of Vaught sentences and the covering theorem*, J. Symbolic
  Logic 41 (1976), 171–187.
* J. H. Silver, *Counting the number of equivalence classes of Borel and coanalytic equivalence
  relations*, Annals of Mathematical Logic 18 (1980), 1–28.
* Su Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Chapters 5 and 11.
* Related formalizations for `ℕ`-carried structures appear in
  `InfinitaryLogic/ModelTheory/RelativeLopezEscobar.lean` and
  `InfinitaryLogic/Descriptive/ThinSentenceSpectra.lean` of Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  Apache-2.0). Here the results are developed on `RelationalConfiguration L V` for arbitrary
  countable carriers `V`, single-sentence splits and backward thinness drop measurability on `C`,
  and Borel complete invariants are connected directly to `Setoid.IsSmooth`.
-/

public section

universe u v w uι

open Cardinal FirstOrder FirstOrder.Language MeasurableSpace MeasureTheory Set

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {ι : Type uι}

/-! ### Sentence-spectrum maps into Cantor space -/

/-- The **sentence theory** (or truth-value trace) of a configuration `c` along a sequence of
infinitary sentences `θ : ℕ → L.SentenceInf ι`, viewed as a point of Cantor space `ℕ → Bool`. -/
noncomputable def sentenceTheory (θ : ℕ → L.SentenceInf ι) (c : RelationalConfiguration L V) :
    ℕ → Bool :=
  open Classical in
  fun n => decide (c ∈ modelsOf (θ n))

/-- Coordinate `n` of `sentenceTheory θ c` is `true` iff `c` lies in `modelsOf (θ n)`. -/
@[simp]
theorem sentenceTheory_apply_eq_true_iff {θ : ℕ → L.SentenceInf ι}
    {c : RelationalConfiguration L V} {n : ℕ} :
    sentenceTheory θ c n = true ↔ c ∈ modelsOf (θ n) := by
  classical
  simp [sentenceTheory]

/-- Coordinate `n` of `sentenceTheory θ c` is `false` iff `c` does not lie in `modelsOf (θ n)`. -/
@[simp]
theorem sentenceTheory_apply_eq_false_iff {θ : ℕ → L.SentenceInf ι}
    {c : RelationalConfiguration L V} {n : ℕ} :
    sentenceTheory θ c n = false ↔ c ∉ modelsOf (θ n) := by
  classical
  simp [sentenceTheory]

/-- Two configurations have the same `sentenceTheory` along `θ` iff they satisfy the same sentences
`θ n` for every `n`. -/
theorem sentenceTheory_eq_iff {θ : ℕ → L.SentenceInf ι} {c d : RelationalConfiguration L V} :
    sentenceTheory θ c = sentenceTheory θ d ↔ ∀ n, c ∈ modelsOf (θ n) ↔ d ∈ modelsOf (θ n) := by
  rw [funext_iff]
  refine forall_congr' fun n => ?_
  rw [Bool.eq_iff_iff, sentenceTheory_apply_eq_true_iff, sentenceTheory_apply_eq_true_iff]

/-- Configurations on possibly different carriers with isomorphic decoded structures have the same
`sentenceTheory` along every sequence of sentences. -/
theorem _root_.FirstOrder.Language.Equiv.sentenceTheory_eq {W : Type*}
    {c : RelationalConfiguration L V} {d : RelationalConfiguration L W}
    (e : @Language.Equiv L V W c.toStructure d.toStructure) (θ : ℕ → L.SentenceInf ι) :
    sentenceTheory θ c = sentenceTheory θ d :=
  funext fun n => Bool.eq_iff_iff.2 <| by
    simp only [sentenceTheory_apply_eq_true_iff]
    exact e.mem_modelsOf_iff (θ n)

/-- Isomorphic configurations on `V` have the same `sentenceTheory`. -/
theorem sentenceTheory_eq_of_isoSetoid {θ : ℕ → L.SentenceInf ι}
    {c d : RelationalConfiguration L V} (h : isoSetoid L V c d) :
    sentenceTheory θ c = sentenceTheory θ d := by
  obtain ⟨e⟩ := isoSetoid_apply.1 h
  exact e.sentenceTheory_eq θ

/-- On a countable carrier, `sentenceTheory θ` is Borel measurable for any countable-branching
sentence sequence `θ`. -/
@[fun_prop]
theorem measurable_sentenceTheory [Countable ι] [Countable V] (θ : ℕ → L.SentenceInf ι) :
    Measurable (sentenceTheory (V := V) θ) := by
  refine Measurable.of_eval fun n => measurable_to_countable' (Bool.forall_bool.2 ⟨?_, ?_⟩)
  · convert (measurableSet_modelsOf (V := V) (θ n)).compl using 1
    ext c
    simp
  · convert measurableSet_modelsOf (V := V) (θ n) using 1
    ext c
    simp

/-- Agreement of `sentenceTheory θ` defines a measurable equivalence graph on configurations over a
countable carrier. -/
theorem measurableSet_setOf_sentenceTheory_eq [Countable ι] [Countable V]
    (θ : ℕ → L.SentenceInf ι) :
    MeasurableSet
      {p : RelationalConfiguration L V × RelationalConfiguration L V |
        sentenceTheory θ p.1 = sentenceTheory θ p.2} :=
  measurableSet_eq_fun
    ((measurable_sentenceTheory θ).comp measurable_fst)
    ((measurable_sentenceTheory θ).comp measurable_snd)

/-! ### Borel Cantor observables and Cantor recovery -/

/-- **Borel Cantor observables are sentence spectra.** Let `X` be a standard Borel space and
`f : X → RelationalConfiguration L V` a measurable map into configurations on a countable carrier
in a countable relational vocabulary. Every measurable map `g : X → ℕ → Bool` constant across
isomorphic values of `f` agrees with `fun x => sentenceTheory θ (f x)` for some sequence
`θ : ℕ → L.Sentenceω`. -/
theorem exists_sentenceTheory_comp_eq [∀ n, Countable (L.Relations n)] [Countable V]
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    {f : X → RelationalConfiguration L V} (hf : Measurable f)
    {g : X → ℕ → Bool} (hg : Measurable g)
    (hinv : ∀ ⦃x y⦄, isoSetoid L V (f x) (f y) → g x = g y) :
    ∃ θ : ℕ → L.Sentenceω, ∀ x, sentenceTheory θ (f x) = g x := by
  have hcoord (n : ℕ) : ∃ θn : L.Sentenceω, f ⁻¹' modelsOf θn = {x | g x n = true} := by
    have hmeas : MeasurableSet {x : X | g x n = true} :=
      ((measurable_pi_apply n).comp hg) (measurableSet_singleton true)
    exact exists_modelsOf_preimage_eq hf hmeas fun x y hxy hx => by
      simpa [hinv hxy] using hx
  choose θ hθ using hcoord
  refine ⟨θ, fun x => funext fun n => Bool.eq_iff_iff.2 ?_⟩
  rw [sentenceTheory_apply_eq_true_iff, ← mem_preimage, hθ n, mem_ofPred_eq]

/-- **Borel Cantor observables on a Borel set of configurations.** On a Borel subset `C` of
configurations over a countable carrier in a countable relational vocabulary, any measurable
isomorphism-invariant map `g : C → ℕ → Bool` is realized by `sentenceTheory θ` for some sequence
`θ : ℕ → L.Sentenceω`. -/
theorem exists_sentenceTheory_eq_on [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C)
    {g : C → ℕ → Bool} (hg : Measurable g)
    (hinv : ∀ ⦃x y : C⦄, isoSetoid L V x.1 y.1 → g x = g y) :
    ∃ θ : ℕ → L.Sentenceω, ∀ x : C, sentenceTheory θ x.1 = g x := by
  have := hC.standardBorel
  exact exists_sentenceTheory_comp_eq measurable_subtype_coe hg hinv

/-- **Cantor recovery by `L_{ω₁ω}` sentences.** If `f : (ℕ → Bool) → RelationalConfiguration L V`
is measurable and maps distinct Cantor-space points to non-isomorphic configurations on a countable
carrier in a countable relational vocabulary, some sequence `θ : ℕ → L.Sentenceω` recovers every
point `x : ℕ → Bool` as `sentenceTheory θ (f x) = x`. -/
theorem exists_sentenceTheory_comp_eq_id [∀ n, Countable (L.Relations n)] [Countable V]
    {f : (ℕ → Bool) → RelationalConfiguration L V} (hf : Measurable f)
    (hanti : ∀ ⦃x y⦄, x ≠ y → ¬ isoSetoid L V (f x) (f y)) :
    ∃ θ : ℕ → L.Sentenceω, ∀ x, sentenceTheory θ (f x) = x :=
  exists_sentenceTheory_comp_eq hf measurable_id fun _ _ hxy =>
    by_contra fun hne => hanti hne hxy

/-- Coordinatewise form of Cantor recovery: along a measurable Cantor antichain `f`, a sequence of
`L_{ω₁ω}` sentences reads off every coordinate bit `f x ∈ modelsOf (θ n) ↔ x n = true`. -/
theorem exists_forall_mem_modelsOf_iff [∀ n, Countable (L.Relations n)] [Countable V]
    {f : (ℕ → Bool) → RelationalConfiguration L V} (hf : Measurable f)
    (hanti : ∀ ⦃x y⦄, x ≠ y → ¬ isoSetoid L V (f x) (f y)) :
    ∃ θ : ℕ → L.Sentenceω, ∀ n x, f x ∈ modelsOf (θ n) ↔ x n = true := by
  obtain ⟨θ, hθ⟩ := exists_sentenceTheory_comp_eq_id hf hanti
  refine ⟨θ, fun n x => ?_⟩
  rw [← sentenceTheory_apply_eq_true_iff, hθ x]

/-! ### Sentence-spectrum characterization of thinness -/

/-- Cantor space `ℕ → Bool` is uncountable. -/
private theorem not_countable_nat_bool : ¬ Countable (ℕ → Bool) := by
  rw [← mk_le_aleph0_iff]
  simpa using aleph0_lt_continuum

/-- **Countable sentence spectra force thinness.** In a countable relational vocabulary on a
countable carrier `V`, if every countable `L_{ω₁ω}` sentence sequence takes only countably many
truth-value patterns on `C`, then `C` is thin for isomorphism. No measurability or invariance
hypothesis on `C` is required. -/
theorem isThinOn_of_countable_image_sentenceTheory [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)}
    (hcount : ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' C).Countable) :
    (isoSetoid L V).IsThinOn C := by
  rw [Setoid.isThinOn_iff_not_hasCantorAntichainOn]
  intro h
  obtain ⟨f, hf, hfC, hanti⟩ := Setoid.hasCantorAntichainOn_iff.1 h
  obtain ⟨θ, hθ⟩ := exists_sentenceTheory_comp_eq_id hf.measurable fun _ _ => hanti _ _
  have huniv : (univ : Set (ℕ → Bool)).Countable :=
    (hcount θ).mono fun x _ => (mem_image _ _ _).2 ⟨f x, hfC x, hθ x⟩
  exact not_countable_nat_bool (countable_univ_iff.1 huniv)

/-- **Thin Borel sets have countable sentence spectra.** In a countable relational vocabulary on a
countable carrier `V`, if a Borel set `C` is thin for isomorphism, every countable `L_{ω₁ω}`
sentence sequence takes only countably many truth-value patterns on `C`. -/
theorem countable_image_sentenceTheory_of_isThinOn [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C)
    (hthin : (isoSetoid L V).IsThinOn C) (θ : ℕ → L.Sentenceω) :
    (sentenceTheory θ '' C).Countable := by
  let g : C → ℕ → Bool := fun c => sentenceTheory θ c.1
  have hg : Measurable g := (measurable_sentenceTheory θ).comp measurable_subtype_coe
  let F : Setoid C := (⊥ : Setoid (ℕ → Bool)).comap g
  have hF : MeasurableSet {p : C × C | F p.1 p.2} :=
    measurableSet_eq_fun (hg.comp measurable_fst) (hg.comp measurable_snd)
  have hcountF : Countable (Quotient F) :=
    (Setoid.countable_or_hasCantorAntichainOn_of_measurableSet hC (isoSetoid L V) F
      (fun x y hxy => sentenceTheory_eq_of_isoSetoid hxy) hF).resolve_right
      (Setoid.isThinOn_iff_not_hasCantorAntichainOn.1 hthin)
  let qmap : Quotient F → ℕ → Bool := Quotient.lift g fun _ _ h => h
  refine (countable_range qmap).mono ?_
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨Quotient.mk F ⟨c, hc⟩, rfl⟩

/-- **Sentence-spectrum characterization of thinness.** On a countable carrier `V` in a countable
relational vocabulary, a Borel set `C` of configurations is thin for isomorphism if and only if
every countable sequence of `L_{ω₁ω}` sentences takes countably many truth-value patterns on `C`. -/
theorem isThinOn_iff_countable_image_sentenceTheory [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    (isoSetoid L V).IsThinOn C ↔
      ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' C).Countable :=
  ⟨countable_image_sentenceTheory_of_isThinOn hC, isThinOn_of_countable_image_sentenceTheory⟩

/-! ### Single-sentence splits with a countable side -/

/-- **Single-sentence splits forbid Cantor antichains.** Suppose `classOf : C → Q` maps a set of
configurations `C` on a countable carrier `V` (in a countable relational vocabulary) into a type
`Q` equipped with a satisfaction predicate `sat : L.Sentenceω → Q → Prop` agreeing with
`modelsOf` on `C`. If every single `L_{ω₁ω}` sentence splits `Set.range classOf` with at least one
countable side, then `C` carries no Cantor antichain for isomorphism. Neither measurability of `C`
nor surjectivity of `classOf` is assumed. -/
theorem not_hasCantorAntichainOn_of_sentence_splits [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)} {Q : Type*} (classOf : C → Q)
    (sat : L.Sentenceω → Q → Prop)
    (hsat : ∀ (c : C) (θ : L.Sentenceω), c.1 ∈ modelsOf θ ↔ sat θ (classOf c))
    (hsplit : ∀ θ : L.Sentenceω,
      {q ∈ range classOf | sat θ q}.Countable ∨ {q ∈ range classOf | ¬ sat θ q}.Countable) :
    ¬ (isoSetoid L V).HasCantorAntichainOn C := by
  intro h
  obtain ⟨f, hf, hfC, hanti⟩ := Setoid.hasCantorAntichainOn_iff.1 h
  obtain ⟨θ, hθ⟩ := exists_forall_mem_modelsOf_iff hf.measurable fun _ _ => hanti _ _
  let qOf : (ℕ → Bool) → Q := fun x => classOf ⟨f x, hfC x⟩
  have hbit (n : ℕ) (x : ℕ → Bool) : sat (θ n) (qOf x) ↔ x n = true :=
    (hsat ⟨f x, hfC x⟩ (θ n)).symm.trans (hθ n x)
  have hinj : Function.Injective qOf := fun x y hxy =>
    funext fun n => Bool.eq_iff_iff.2 <| (hbit n x).symm.trans (hxy ▸ hbit n y)
  have hcantor_split (n : ℕ) :
      {x : ℕ → Bool | x n = true}.Countable ∨ {x : ℕ → Bool | ¬ x n = true}.Countable := by
    rcases hsplit (θ n) with hpos | hneg
    · refine .inl ((hpos.preimage hinj).mono fun x hx => ?_)
      exact ⟨⟨⟨f x, hfC x⟩, rfl⟩, (hbit n x).2 hx⟩
    · refine .inr ((hneg.preimage hinj).mono fun x hx => ?_)
      exact ⟨⟨⟨f x, hfC x⟩, rfl⟩, mt (hbit n x).1 hx⟩
  have hrange : (range (id : (ℕ → Bool) → ℕ → Bool)).Countable :=
    TauCeti.countable_range_of_splits (P := fun n (x : ℕ → Bool) => x n = true) id
      (fun x y h => funext fun n => Bool.eq_iff_iff.2 (h n)) hcantor_split
  rw [range_id] at hrange
  exact not_countable_nat_bool (countable_univ_iff.1 hrange)

/-- **Single-sentence splits force thinness.** Under the hypotheses of
`not_hasCantorAntichainOn_of_sentence_splits`, the set `C` is thin for isomorphism. -/
theorem isThinOn_of_sentence_splits [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)} {Q : Type*} (classOf : C → Q)
    (sat : L.Sentenceω → Q → Prop)
    (hsat : ∀ (c : C) (θ : L.Sentenceω), c.1 ∈ modelsOf θ ↔ sat θ (classOf c))
    (hsplit : ∀ θ : L.Sentenceω,
      {q ∈ range classOf | sat θ q}.Countable ∨ {q ∈ range classOf | ¬ sat θ q}.Countable) :
    (isoSetoid L V).IsThinOn C :=
  Setoid.isThinOn_iff_not_hasCantorAntichainOn.2
    (not_hasCantorAntichainOn_of_sentence_splits classOf sat hsat hsplit)

/-- **Thinness from single-sentence isomorphism-class cuts.** For any set `C` of configurations on
a countable carrier `V` in a countable relational vocabulary, if for every `θ : L.Sentenceω` either
`C ∩ modelsOf θ` or `C \ modelsOf θ` meets only countably many isomorphism classes, then `C` is
thin for isomorphism. -/
theorem isThinOn_of_countable_image_quotientMk_inter_or_diff
    [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)}
    (hsplit : ∀ θ : L.Sentenceω,
      (Quotient.mk (isoSetoid L V) '' (C ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L V) '' (C \ modelsOf θ)).Countable) :
    (isoSetoid L V).IsThinOn C := by
  let classOf : C → Quotient (isoSetoid L V) := fun c => Quotient.mk (isoSetoid L V) c.1
  let sat : L.Sentenceω → Quotient (isoSetoid L V) → Prop := fun θ =>
    Quotient.lift (fun c => c ∈ modelsOf θ) fun _ _ h =>
      propext ((isomorphismInvariant_modelsOf θ).mem_iff h)
  refine isThinOn_of_sentence_splits classOf sat (fun _ _ => Iff.rfl) fun θ => ?_
  rcases hsplit θ with hpos | hneg
  · refine .inl (hpos.mono ?_)
    rintro _ ⟨⟨c, rfl⟩, hsat⟩
    exact ⟨c.1, ⟨c.2, hsat⟩, rfl⟩
  · refine .inr (hneg.mono ?_)
    rintro _ ⟨⟨c, rfl⟩, hnsat⟩
    exact ⟨c.1, ⟨c.2, hnsat⟩, rfl⟩

/-! ### Smoothness and Borel complete invariants -/

/-- Any countable sequence of countable-branching sentences that separates non-isomorphic members
of `C` witnesses that isomorphism restricted to `C` is smooth (`Setoid.IsSmooth`). -/
theorem isSmooth_comap_isoSetoid_of_sentenceTheory [Countable ι] [Countable V]
    {C : Set (RelationalConfiguration L V)} {θ : ℕ → L.SentenceInf ι}
    (hsep : ∀ ⦃c⦄, c ∈ C → ∀ ⦃d⦄, d ∈ C →
      (isoSetoid L V c d ↔ sentenceTheory θ c = sentenceTheory θ d)) :
    ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth :=
  Setoid.isSmooth_iff.2 ⟨fun c => sentenceTheory θ c.1,
    (measurable_sentenceTheory θ).comp measurable_subtype_coe, fun c d => hsep c.2 d.2⟩

/-- **Smoothness on a Borel class is classification by a countable `L_{ω₁ω}` sentence spectrum.**
On a Borel subset `C` of configurations over a countable carrier in a countable relational
vocabulary, isomorphism restricted to `C` is smooth if and only if some sequence
`θ : ℕ → L.Sentenceω` is a complete isomorphism invariant on `C`. -/
theorem isSmooth_comap_isoSetoid_iff_exists_sentenceTheory
    [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth ↔
      ∃ θ : ℕ → L.Sentenceω,
        ∀ ⦃c⦄, c ∈ C → ∀ ⦃d⦄, d ∈ C →
          (isoSetoid L V c d ↔ sentenceTheory θ c = sentenceTheory θ d) := by
  refine ⟨fun hsmooth => ?_, fun ⟨θ, hθ⟩ => isSmooth_comap_isoSetoid_of_sentenceTheory hθ⟩
  obtain ⟨g, hg, hgE⟩ := Setoid.isSmooth_iff.1 hsmooth
  obtain ⟨θ, hθ⟩ := exists_sentenceTheory_eq_on hC hg fun x y hxy => (hgE x y).1 hxy
  refine ⟨θ, fun c hc d hd => ?_⟩
  rw [hθ ⟨c, hc⟩, hθ ⟨d, hd⟩]
  exact hgE ⟨c, hc⟩ ⟨d, hd⟩

/-- A measurable complete isomorphism invariant on `C` taking values in a countably separated
measurable space makes isomorphism restricted to `C` smooth. -/
theorem isSmooth_comap_isoSetoid_of_countablySeparated
    {C : Set (RelationalConfiguration L V)} {Y : Type*} [MeasurableSpace Y]
    [CountablySeparated Y] {g : C → Y} (hg : Measurable g)
    (hsep : ∀ c d : C, isoSetoid L V c.1 d.1 ↔ g c = g d) :
    ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth :=
  (Setoid.borelReducible_iff.2 ⟨g, hg, hsep⟩).isSmooth (Setoid.isSmooth_bot_iff.2 inferInstance)

/-- **Thin Borel sets with smooth isomorphism meet countably many isomorphism classes.** On a
countable carrier in a countable relational vocabulary, if a Borel set `C` is thin for isomorphism
and isomorphism restricted to `C` is smooth, then `C` meets only countably many isomorphism
classes. -/
theorem countable_quotient_comap_isoSetoid_of_isThinOn_of_isSmooth
    [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C)
    (hthin : (isoSetoid L V).IsThinOn C)
    (hsmooth : ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth) :
    Countable (Quotient ((isoSetoid L V).comap (Subtype.val : C → _))) :=
  (Setoid.countable_or_hasCantorAntichainOn_of_measurableSet hC (isoSetoid L V)
    ((isoSetoid L V).comap Subtype.val) (fun _ _ h => h) hsmooth.measurableSet_setOf).resolve_right
    (Setoid.isThinOn_iff_not_hasCantorAntichainOn.1 hthin)

/-- A thin Borel set of configurations admitting a measurable complete isomorphism invariant into a
countably separated space meets only countably many isomorphism classes. -/
theorem countable_quotient_comap_isoSetoid_of_isThinOn_of_countablySeparated
    [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C)
    (hthin : (isoSetoid L V).IsThinOn C) {Y : Type*} [MeasurableSpace Y] [CountablySeparated Y]
    {g : C → Y} (hg : Measurable g)
    (hsep : ∀ c d : C, isoSetoid L V c.1 d.1 ↔ g c = g d) :
    Countable (Quotient ((isoSetoid L V).comap (Subtype.val : C → _))) :=
  countable_quotient_comap_isoSetoid_of_isThinOn_of_isSmooth hC hthin
    (isSmooth_comap_isoSetoid_of_countablySeparated hg hsep)

end TauCeti.RelationalConfiguration
