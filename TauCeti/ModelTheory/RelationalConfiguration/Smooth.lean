/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Sentence.Basic
public import TauCeti.SetTheory.Descriptive.BorelReducibility
import TauCeti.ModelTheory.RelationalConfiguration.Observables
import TauCeti.ModelTheory.Scott.Isomorphism
import TauCeti.SetTheory.Descriptive.Silver

/-!
# Smoothness of isomorphism on relational configurations

On a subset `C ⊆ RelationalConfiguration L V` over a countable carrier `V`, restricted isomorphism
`(isoSetoid L V).comap (Subtype.val : C → _)` is smooth (`Setoid.IsSmooth`) whenever a countable
sequence `θ : ℕ → L.SentenceInf κ` of infinitary sentences with countable branching separates
non-isomorphic members of `C` (`isSmooth_comap_isoSetoid_of_exists_sentenceTheory`). Neither
measurability of `C` nor countability of the vocabulary `L` is needed for this implication.

Conversely, in a relational language with countably many relation symbols of each arity, on any
Borel subset `C ⊆ RelationalConfiguration L V`, restricted isomorphism is smooth if and only if a
single countable sequence `θ : ℕ → L.Sentenceω` decides isomorphism within `C`
(`isSmooth_comap_isoSetoid_iff_exists_sentenceTheory`). Combining smoothness with thinness
characterizes when `C` meets countably many isomorphism classes
(`countable_quotient_comap_isoSetoid_iff_isThinOn_and_isSmooth`).

## Main results

* `TauCeti.RelationalConfiguration.isSmooth_comap_isoSetoid_of_exists_sentenceTheory`: a countable
  sequence of infinitary sentences with countable branching separating non-isomorphic members of
  `C` witnesses smoothness of restricted isomorphism on `C`.
* `TauCeti.RelationalConfiguration.isSmooth_comap_isoSetoid_iff_exists_sentenceTheory`: on a Borel
  subset `C` of configurations over a countable carrier in a countable relational vocabulary,
  restricted isomorphism is smooth if and only if a countable `L_{ω₁ω}` sentence sequence decides
  isomorphism on `C`.
* `TauCeti.RelationalConfiguration.countable_quotient_comap_isoSetoid_iff_isThinOn_and_isSmooth`: a
  Borel set `C` meets countably many isomorphism classes if and only if it is thin for isomorphism
  and restricted isomorphism on `C` is smooth.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae **57** (1965), 253–272.
* J. H. Silver, *Counting the number of equivalence classes of Borel and coanalytic equivalence
  relations*, Annals of Mathematical Logic 18 (1980), 1–28.
* S. Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Chapters 5 and 11.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Chapter 4.
-/

public section

universe u v w uκ

open Cardinal FirstOrder FirstOrder.Language MeasureTheory Set

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} [Countable V] {κ : Type uκ}

/-- If a countable sequence of sentences with countable branching separates non-isomorphic members
of `C`, then restricted isomorphism on `C` is smooth. No measurability of `C` or countability of `L`
is required. -/
theorem isSmooth_comap_isoSetoid_of_exists_sentenceTheory [Countable κ]
    {C : Set (RelationalConfiguration L V)}
    (h : ∃ θ : ℕ → L.SentenceInf κ, ∀ c ∈ C, ∀ d ∈ C,
      isoSetoid L V c d ↔ sentenceTheory θ c = sentenceTheory θ d) :
    ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth := by
  obtain ⟨θ, hθ⟩ := h
  exact Setoid.isSmooth_iff.2 ⟨fun c : C => sentenceTheory θ c.val,
    (measurable_sentenceTheory θ).comp measurable_subtypeVal,
    fun x y => hθ x.val x.property y.val y.property⟩

/-- **Smoothness via complete countable sentence lists.** On a Borel subset `C` of configurations
over a countable carrier in a countable relational vocabulary, restricted isomorphism is smooth if
and only if a single countable sequence `θ : ℕ → L.Sentenceω` decides isomorphism within `C`. -/
theorem isSmooth_comap_isoSetoid_iff_exists_sentenceTheory [∀ n, Countable (L.Relations n)]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth ↔
      ∃ θ : ℕ → L.Sentenceω, ∀ c ∈ C, ∀ d ∈ C,
        isoSetoid L V c d ↔ sentenceTheory θ c = sentenceTheory θ d := by
  refine ⟨fun hsmooth => ?_, isSmooth_comap_isoSetoid_of_exists_sentenceTheory⟩
  have := hC.standardBorel
  obtain ⟨g, hg, hgE⟩ := Setoid.isSmooth_iff.1 hsmooth
  obtain ⟨θ, hθ⟩ := exists_sentenceTheory_eq_iff_of_countablySeparated
    measurable_subtypeVal hg fun x y hxy => (hgE x y).1 hxy
  exact ⟨θ, fun c hc d hd => (hgE ⟨c, hc⟩ ⟨d, hd⟩).trans (hθ ⟨c, hc⟩ ⟨d, hd⟩)⟩

/-- **Characterization of Borel classes with countably many isomorphism classes.** On a countable
carrier in a countable relational vocabulary, a Borel set `C` meets countably many isomorphism
classes if and only if `C` is thin for isomorphism and restricted isomorphism on `C` is smooth. -/
theorem countable_quotient_comap_isoSetoid_iff_isThinOn_and_isSmooth
    [∀ n, Countable (L.Relations n)]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    Countable (Quotient ((isoSetoid L V).comap (Subtype.val : C → _))) ↔
      (isoSetoid L V).IsThinOn C ∧ ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth := by
  refine ⟨fun hcount => ⟨?_, ?_⟩,
    fun ⟨hthin, hsmooth⟩ => hthin.countable_quotient_comap_of_isSmooth hC hsmooth⟩
  · refine Setoid.isThinOn_iff_not_hasCantorAntichainOn.2 fun hcantor => ?_
    exact (aleph0_lt_continuum.trans_le hcantor.continuum_le_mk_quotient_comap).not_ge
      (mk_le_aleph0_iff.2 hcount)
  · -- Each individual isomorphism orbit is the Borel model class of its representative's Scott
    -- sentence.
    refine Setoid.isSmooth_of_countable_quotient fun x => ?_
    have horbit : {d : RelationalConfiguration L V | isoSetoid L V x.val d} =
        modelsOf (@scottSentence L _ V x.val.toStructure _ _) := by
      ext d
      exact isoSetoid_apply.trans
        ((@realize_scottSentence_iff L _ _ V x.val.toStructure _ V d.toStructure _).symm.trans
          mem_modelsOf.symm)
    exact (horbit ▸ measurableSet_modelsOf _).preimage measurable_subtypeVal

end TauCeti.RelationalConfiguration
