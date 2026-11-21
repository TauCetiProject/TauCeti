/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Scattered.Vaught
public import TauCeti.ModelTheory.RelationalConfiguration.FragmentSpectrum

/-!
# Fragment-spectrum characterizations of scattered classes and sentences

Classically, an `L_{ω₁ω}` sentence `φ` is called *scattered* (Morley 1970; Marker, the chapter on
Vaught counterexamples) when
every countable fragment realizes only countably many `n`-types across the countable models of `φ`.
In this library, `TauCeti.BFScattered K` defines scatteredness of a class
`K : Set (RelationalConfiguration L ℕ)` combinatorially through countable back-and-forth levels,
while `TauCeti.IsThinOnNatModels φ` records the descriptive condition that `modelsOf (V := ℕ) φ`
contains no nonempty perfect set of pairwise non-isomorphic configurations.

This file connects those notions to the fragment type spectra of
`TauCeti.ModelTheory.RelationalConfiguration.FragmentSpectrum`:

* On `ℕ`, any back-and-forth scattered set `K` has countable `n`-type spectrum for every fragment
  with countable `n`-slice (`TauCeti.BFScattered.countable_typeSpectrum`), with no Borelness
  hypothesis on `K` and no countability hypothesis on `L`.
* Conversely, in a relational language with countably many relation symbols of each arity, any set
  `K : Set (RelationalConfiguration L ℕ)` on which every countable fragment has countable type
  spectra at all arities is back-and-forth scattered
  (`TauCeti.bfScattered_of_countable_typeSpectrum`, hence
  `TauCeti.bfScattered_iff_countable_typeSpectrum`) and therefore meets at most `ℵ₁` isomorphism
  classes (`TauCeti.mk_isoClasses_le_aleph_one_of_countable_typeSpectrum`), still without Borelness
  or isomorphism invariance of `K`.
* Specializing to `modelsOf φ`, thinness of an infinitary sentence with countable branching on `ℕ`
  is equivalent to countability of all countable-fragment type spectra on `modelsOf (V := ℕ) φ`
  (`TauCeti.isThinOnNatModels_iff_countable_typeSpectrum`), and absence of a perfect set of
  countable models across all countable carriers is equivalent to countable fragment spectra on `ℕ`
  and on every finite carrier `Fin d`
  (`TauCeti.not_hasPerfectlyManyCountableModels_iff_countable_typeSpectrum`).
* Consequently, Vaught's conjecture—and under `ℵ₁ < 𝔠` the cardinal Vaught conjecture—is equivalent
  to countability of `Quotient (isoSetoidOn ℕ φ)` for every `L_{ω₁ω}` sentence whose countable
  fragments all have countable type spectra on `ℕ`
  (`TauCeti.vaughtConjecture_iff_countable_typeSpectrum` and
  `TauCeti.cardinalVaughtConjecture_iff_countable_typeSpectrum`).

## Main results

* `TauCeti.BFScattered.countable_typeSpectrum` and `TauCeti.bfScattered_iff_countable_typeSpectrum`:
  in a countable relational vocabulary, back-and-forth scatteredness of an arbitrary set `K` on `ℕ`
  is equivalent to countability of `F.typeSpectrum n K` for every countable fragment `F` and arity
  `n : ℕ`.
* `TauCeti.mk_isoClasses_le_aleph_one_of_countable_typeSpectrum`: countable fragment spectra on `K`
  bound the isomorphism classes met by `K` on `ℕ` by `ℵ₁`.
* `TauCeti.isThinOnNatModels_iff_countable_typeSpectrum`: in a countable relational vocabulary,
  thinness on `ℕ` of a sentence with countable branching equals classical scatteredness via
  countable fragment spectra.
* `TauCeti.not_hasPerfectlyManyCountableModels_iff_countable_typeSpectrum` and
  `TauCeti.countableModelCount_le_aleph_one_of_countable_typeSpectrum`: extension across `ℕ` and all
  finite carriers `Fin d`.
* `TauCeti.vaughtConjecture_iff_countable_typeSpectrum` and
  `TauCeti.cardinalVaughtConjecture_iff_countable_typeSpectrum`: the classical fragment-spectrum
  formulations of Vaught's conjecture.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 1
  (countable fragments and fragment `n`-types) and the chapters on the space of countable models and
  Vaught counterexamples (scattered sentences).
* M. Morley, *The number of countable models*, J. Symbolic Logic 35 (1970), 14–18.
* J. H. Silver, *Counting the number of equivalence classes of Borel and coanalytic equivalence
  relations*, Annals of Mathematical Logic 18 (1980), 1–28.
* Related formalizations appear in Cameron Freer's `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, `InfinitaryLogic/Descriptive/RealizedSpectrum.lean`
  and `InfinitaryLogic/Conditional/FragmentSpectrumThin.lean` (Apache-2.0); here the equivalence
  with `BFScattered` is unconditional on `K` and Silver's theorem is discharged unconditionally.
-/

public section

universe u v uι

open FirstOrder FirstOrder.Language Cardinal Ordinal Set

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {ι : Type uι} {n : ℕ}
  {K : Set (RelationalConfiguration L ℕ)}

/-! ### Arbitrary configuration classes on `ℕ` -/

/-- **Back-and-forth scattered sets have countable fragment spectra.** If `K` is back-and-forth
scattered on `ℕ`, then `F.typeSpectrum n K` is countable whenever `F.slice n` is countable. Neither
Borelness of `K` nor countability of `L` is assumed. -/
theorem BFScattered.countable_typeSpectrum (hK : BFScattered K) {F : Fragment L}
    (hF : (F.slice n).Countable) :
    (F.typeSpectrum n K).Countable :=
  countable_typeSpectrum_of_countable_bfEquivSetoid hF (bfScattered_iff.mp hK)

/-- **Countable fragment spectra imply back-and-forth scatteredness.** In a relational language with
countably many relation symbols of each arity, any set `K` of configurations on `ℕ` on which every
countable fragment has a countable type spectrum at every arity is back-and-forth scattered. No
Borelness or isomorphism invariance of `K` is required. -/
theorem bfScattered_of_countable_typeSpectrum [∀ k, Countable (L.Relations k)]
    (hspec : ∀ F : Fragment L,
      (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
        ∀ m : ℕ, (F.typeSpectrum m K).Countable) :
    BFScattered K :=
  bfScattered_iff.2 fun _ hα =>
    countable_quotient_comap_bfEquivSetoid_of_countable_typeSpectrum hspec hα

/-- **Fragment-spectrum characterization of back-and-forth scattered sets.** In a relational
language with countably many relation symbols of each arity, an arbitrary set `K` of configurations
on `ℕ` is back-and-forth scattered if and only if every countable fragment `F` has a countable type
spectrum on `K` at every arity `n`. -/
theorem bfScattered_iff_countable_typeSpectrum [∀ k, Countable (L.Relations k)] :
    BFScattered K ↔
      ∀ F : Fragment L,
        (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
          ∀ n : ℕ, (F.typeSpectrum n K).Countable :=
  ⟨fun hK F hF n => hK.countable_typeSpectrum (F.slice_countable hF n),
    bfScattered_of_countable_typeSpectrum⟩

/-- **At most `ℵ₁` isomorphism classes from countable fragment spectra.** In a relational language
with countably many relation symbols of each arity, any set `K` of configurations on `ℕ` on which
every countable fragment has countable type spectra at all arities meets at most `ℵ₁` isomorphism
classes. Because `isoSetoidOn ℕ φ` is an abbreviation, this applies directly to `modelsOf φ`. -/
theorem mk_isoClasses_le_aleph_one_of_countable_typeSpectrum [∀ k, Countable (L.Relations k)]
    (hspec : ∀ F : Fragment L,
      (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
        ∀ m : ℕ, (F.typeSpectrum m K).Countable) :
    #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) ≤ ℵ₁ :=
  mk_isoClasses_le_aleph_one_of_countable_levels K
    (bfScattered_iff.1 (bfScattered_of_countable_typeSpectrum hspec))

/-! ### Model classes of infinitary sentences and Vaught's conjecture -/

/-- In a relational language with countably many relation symbols of each arity, a sentence with
countable branching that is thin on `ℕ` has countable `n`-type spectrum on `modelsOf (V := ℕ) φ` for
every fragment with countable `n`-slice. -/
theorem IsThinOnNatModels.countable_typeSpectrum [∀ k, Countable (L.Relations k)] [Countable ι]
    {φ : L.SentenceInf ι} (h : IsThinOnNatModels φ) {F : Fragment L}
    (hF : (F.slice n).Countable) :
    (F.typeSpectrum n (modelsOf (V := ℕ) φ)).Countable :=
  h.bfScattered_modelsOf.countable_typeSpectrum hF

/-- In a relational language with countably many relation symbols of each arity, countable fragment
spectra at all arities on `modelsOf (V := ℕ) φ` make `φ` thin on `ℕ`, with no countability
assumption on the branching index `ι`. -/
theorem isThinOnNatModels_of_countable_typeSpectrum [∀ k, Countable (L.Relations k)]
    {φ : L.SentenceInf ι}
    (hspec : ∀ F : Fragment L,
      (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
        ∀ m : ℕ, (F.typeSpectrum m (modelsOf (V := ℕ) φ)).Countable) :
    IsThinOnNatModels φ :=
  isThinOnNatModels_iff_isThinOn.2 (isThinOn_of_countable_typeSpectrum hspec)

/-- **Classical scatteredness equals thinness on `ℕ`.** For an infinitary sentence with countable
branching in a relational language with countably many relation symbols of each arity, absence of a
nonempty perfect set of pairwise non-isomorphic models on `ℕ` is equivalent to countability of
`F.typeSpectrum n (modelsOf (V := ℕ) φ)` for every countable fragment `F` and every arity `n`. -/
theorem isThinOnNatModels_iff_countable_typeSpectrum [∀ k, Countable (L.Relations k)] [Countable ι]
    {φ : L.SentenceInf ι} :
    IsThinOnNatModels φ ↔
      ∀ F : Fragment L,
        (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
          ∀ n : ℕ, (F.typeSpectrum n (modelsOf (V := ℕ) φ)).Countable :=
  bfScattered_modelsOf_iff_isThinOnNatModels.symm.trans bfScattered_iff_countable_typeSpectrum

/-- In a relational language with countably many relation symbols of each arity, countable fragment
spectra on `ℕ` and on every finite carrier `Fin d` rule out a perfect set of pairwise
non-isomorphic countable models, with no countability hypothesis on `ι`. -/
theorem not_hasPerfectlyManyCountableModels_of_countable_typeSpectrum
    [∀ k, Countable (L.Relations k)] {φ : L.SentenceInf ι}
    (hℕ : ∀ F : Fragment L,
      (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
        ∀ n : ℕ, (F.typeSpectrum n (modelsOf (V := ℕ) φ)).Countable)
    (hfin : ∀ d : ℕ, ∀ F : Fragment L,
      (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
        ∀ n : ℕ, (F.typeSpectrum n (modelsOf (V := Fin d) φ)).Countable) :
    ¬ HasPerfectlyManyCountableModels φ :=
  not_hasPerfectlyManyCountableModels_iff.2
    ⟨isThinOnNatModels_of_countable_typeSpectrum hℕ,
      fun d => isThinOn_of_countable_typeSpectrum (hfin d)⟩

/-- For an infinitary sentence with countable branching in a countable relational vocabulary, `φ`
has no perfect set of pairwise non-isomorphic countable models if and only if every countable
fragment has countable type spectra on `modelsOf (V := ℕ) φ` and on each `modelsOf (V := Fin d) φ`.
Both tiers are needed: a sentence asserting that the carrier is a singleton in a language with
countably many unary predicates has empty spectra on `ℕ` and continuum many models on `Fin 1`. -/
theorem not_hasPerfectlyManyCountableModels_iff_countable_typeSpectrum
    [∀ k, Countable (L.Relations k)] [Countable ι] {φ : L.SentenceInf ι} :
    ¬ HasPerfectlyManyCountableModels φ ↔
      (∀ F : Fragment L,
        (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
          ∀ n : ℕ, (F.typeSpectrum n (modelsOf (V := ℕ) φ)).Countable) ∧
        ∀ d : ℕ, ∀ F : Fragment L,
          (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
            ∀ n : ℕ, (F.typeSpectrum n (modelsOf (V := Fin d) φ)).Countable := by
  rw [not_hasPerfectlyManyCountableModels_iff, isThinOnNatModels_iff_countable_typeSpectrum]
  exact and_congr_right' <| forall_congr' fun d =>
    isThinOn_iff_countable_typeSpectrum (measurableSet_modelsOf φ)

/-- In a relational language with countably many relation symbols of each arity, countable fragment
spectra on `ℕ` and on each `Fin d` bound the total number of countable models (finite models
included) by `ℵ₁`, with no countability hypothesis on the branching index `ι`. -/
theorem countableModelCount_le_aleph_one_of_countable_typeSpectrum
    [∀ k, Countable (L.Relations k)] {φ : L.SentenceInf ι}
    (hℕ : ∀ F : Fragment L,
      (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
        ∀ n : ℕ, (F.typeSpectrum n (modelsOf (V := ℕ) φ)).Countable)
    (hfin : ∀ d : ℕ, ∀ F : Fragment L,
      (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
        ∀ n : ℕ, (F.typeSpectrum n (modelsOf (V := Fin d) φ)).Countable) :
    countableModelCount φ ≤ ℵ₁ := by
  have hfin_le (d : ℕ) : #(Quotient (isoSetoidOn (Fin d) φ)) ≤ ℵ₀ := by
    let C := modelsOf (V := Fin d) φ
    have : Countable (Quotient (@bfTupleSetoid L _ C (fun _ => Fin d)
        (fun c => c.val.toStructure) (0 : Ordinal.{0}) d)) :=
      countable_quotient_bfTupleSetoid_of_countable_typeSpectrum (hfin d) (Ordinal.omega_pos 1) d
    have : Countable C := Function.Injective.countable
      (f := fun c : C => Quotient.mk (@bfTupleSetoid L _ C (fun _ => Fin d)
        (fun c => c.val.toStructure) (0 : Ordinal.{0}) d) ⟨c, id⟩)
      fun c₁ c₂ hq => Subtype.ext <| RelationalConfiguration.ext fun a => by
        have hbf := (@bfTupleSetoid_apply L _ C (fun _ => Fin d) (fun c => c.val.toStructure)
          (0 : Ordinal.{0}) d ⟨c₁, id⟩ ⟨c₂, id⟩).1 (Quotient.exact hq)
        have hsat := (@BFEquiv.zero L _ (Fin d) (Fin d) c₁.val.toStructure c₂.val.toStructure d
          id id).1 hbf
        induction a using Atom.induction_atom with
        | h R x =>
          rw [Bool.eq_iff_iff, ← toStructure_relMap, ← toStructure_relMap]
          exact @SameAtomicType.rel_iff L d (Fin d) (Fin d) c₁.val.toStructure c₂.val.toStructure _
            id id hsat _ R x
    exact mk_le_aleph0
  simpa only [mul_eq_self le_rfl, add_eq_left (aleph0_le_aleph 1) (aleph0_le_aleph 1)] using
    countableModelCount_le_add_aleph0_mul
      (mk_isoClasses_le_aleph_one_of_countable_typeSpectrum hℕ) hfin_le

/-- **The classical scattered-sentence formulation of Vaught's conjecture.** Vaught's perfect-set
conjecture for all countable models is equivalent, without the continuum hypothesis, to
countability of `Quotient (isoSetoidOn ℕ φ)` for every `L_{ω₁ω}` sentence `φ` whose countable
fragments all realize only countably many `n`-types on `modelsOf (V := ℕ) φ`. -/
theorem vaughtConjecture_iff_countable_typeSpectrum :
    VaughtConjecture ↔
      ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ k, L.Relations k)] (φ : L.Sentenceω),
        (∀ F : Fragment L,
          (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
            ∀ n : ℕ, (F.typeSpectrum n (modelsOf (V := ℕ) φ)).Countable) →
          Countable (Quotient (isoSetoidOn ℕ φ)) := by
  rw [vaughtConjecture_iff_bfScattered]
  exact forall_congr' fun L => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun φ => imp_congr_left bfScattered_iff_countable_typeSpectrum

/-- Under `ℵ₁ < 𝔠`, the cardinal Vaught conjecture is likewise equivalent to countability of
`Quotient (isoSetoidOn ℕ φ)` for every `L_{ω₁ω}` sentence whose countable fragments all have
countable type spectra on `modelsOf (V := ℕ) φ`. -/
theorem cardinalVaughtConjecture_iff_countable_typeSpectrum (hc : ℵ₁ < (𝔠 : Cardinal.{0})) :
    CardinalVaughtConjecture ↔
      ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ k, L.Relations k)] (φ : L.Sentenceω),
        (∀ F : Fragment L,
          (F : Set (Σ m, L.BoundedFormulaω Empty m)).Countable →
            ∀ n : ℕ, (F.typeSpectrum n (modelsOf (V := ℕ) φ)).Countable) →
          Countable (Quotient (isoSetoidOn ℕ φ)) :=
  (cardinalVaughtConjecture_iff_vaughtConjecture hc).trans
    vaughtConjecture_iff_countable_typeSpectrum

end TauCeti
