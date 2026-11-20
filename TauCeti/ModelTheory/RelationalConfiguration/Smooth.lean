/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.SentenceTheory
public import TauCeti.SetTheory.Descriptive.BorelReducibility
import TauCeti.ModelTheory.RelationalConfiguration.Observables

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
(`isSmooth_comap_isoSetoid_iff_exists_sentenceTheory`).

## Main results

* `TauCeti.RelationalConfiguration.isSmooth_comap_isoSetoid_of_exists_sentenceTheory`: a countable
  sequence of infinitary sentences with countable branching separating non-isomorphic members of
  `C` witnesses smoothness of restricted isomorphism on `C`.
* `TauCeti.RelationalConfiguration.isSmooth_comap_isoSetoid_iff_exists_sentenceTheory`: on a Borel
  subset `C` of configurations over a countable carrier in a countable relational vocabulary,
  restricted isomorphism is smooth if and only if a countable `L_{ω₁ω}` sentence sequence decides
  isomorphism on `C`.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae **57** (1965), 253–272.
* S. Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Chapters 5 and 11.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Chapter 4.
-/

public section

universe u v w uκ

open FirstOrder FirstOrder.Language MeasureTheory Set

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
  have : StandardBorelSpace C := hC.standardBorel
  obtain ⟨g, hg, hgE⟩ := Setoid.isSmooth_iff.1 hsmooth
  obtain ⟨θ, hθ⟩ := exists_sentenceTheory_comp_eq (f := (Subtype.val : C → _))
    measurable_subtypeVal hg fun x y hxy => (hgE x y).1 hxy
  exact ⟨θ, fun c hc d hd => (hgE ⟨c, hc⟩ ⟨d, hd⟩).trans
    ⟨fun h => by rw [hθ ⟨c, hc⟩, hθ ⟨d, hd⟩, h],
      fun h => by rwa [hθ ⟨c, hc⟩, hθ ⟨d, hd⟩] at h⟩⟩

omit [Countable V] in
/-- A measurable complete isomorphism invariant on `C` taking values in a countably separated
measurable space makes isomorphism restricted to `C` smooth. -/
theorem isSmooth_comap_isoSetoid_of_countablySeparated
    {C : Set (RelationalConfiguration L V)} {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountablySeparated Y] {g : C → Y} (hg : Measurable g)
    (hsep : ∀ c d : C, isoSetoid L V c.val d.val ↔ g c = g d) :
    ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth :=
  Setoid.isSmooth_of_countablySeparated hg hsep

end TauCeti.RelationalConfiguration
