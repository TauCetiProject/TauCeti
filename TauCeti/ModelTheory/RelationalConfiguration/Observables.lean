/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Sentence.Basic
import TauCeti.ModelTheory.RelationalConfiguration.LopezEscobar
import TauCeti.Topology.MetricSpace.Polish.Pi

/-!
# Borel observables on relational configurations

Along a measurable family `f : X → RelationalConfiguration L V` parametrized by a standard Borel
space `X` on a countable carrier `V` in a countable relational vocabulary `L`, every
isomorphism-invariant measurable map `g : X → ι → Bool` is realized as `sentenceTheory θ ∘ f` for
a family of `L_{ω₁ω}` sentences `θ : ι → L.Sentenceω` (`exists_sentenceTheory_comp_eq`), without
assuming countability of the index type `ι`.

More generally, every isomorphism-invariant Borel observable `g : X → Z` into a countably separated
measurable space `Z` factors through a measurable injection `e : Z → ℕ → Bool` as
`e ∘ g = sentenceTheory θ ∘ f` (`exists_measurable_injective_comp_eq_sentenceTheory`), and hence
has the same fibres as `sentenceTheory θ ∘ f` for some countable sequence `θ : ℕ → L.Sentenceω`
(`exists_sentenceTheory_eq_iff_of_countablySeparated`). Specializing to a measurable map
`f : (ι → Bool) → RelationalConfiguration L V` on a countable index type `ι` whose values on
distinct sequences are non-isomorphic recovers every coordinate via `sentenceTheory θ (f x) = x`
(`exists_sentenceTheory_apply_eq`, `exists_forall_mem_modelsOf_iff`).

## Main results

* `TauCeti.RelationalConfiguration.exists_sentenceTheory_comp_eq`: every isomorphism-invariant
  Borel map into `ι → Bool` along a standard Borel family is realized by `sentenceTheory θ ∘ f`.
* `TauCeti.RelationalConfiguration.exists_measurable_injective_comp_eq_sentenceTheory` and
  `TauCeti.RelationalConfiguration.exists_sentenceTheory_eq_iff_of_countablySeparated`: every
  isomorphism-invariant Borel observable into a countably separated measurable space has the same
  fibres as `sentenceTheory θ ∘ f` for a countable `L_{ω₁ω}` sentence list `θ`.
* `TauCeti.RelationalConfiguration.exists_sentenceTheory_apply_eq` and
  `TauCeti.RelationalConfiguration.exists_forall_mem_modelsOf_iff`: Cantor recovery along
  measurable families from `ι → Bool` with pairwise non-isomorphic values.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae **57** (1965), 253–272.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Chapter 4.
* S. Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Chapter 11.
-/

public section

universe u v w uι

open FirstOrder FirstOrder.Language MeasureTheory Set

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]
variable {V : Type w} [Countable V] {ι : Type uι}

/-- **Borel observables into Boolean products.** Along a measurable family `f : X →
RelationalConfiguration L V` from a standard Borel space `X`, every isomorphism-invariant
measurable map `g : X → ι → Bool` is realized as `sentenceTheory θ ∘ f` for a family
`θ : ι → L.Sentenceω`. The index type `ι` need not be countable. -/
theorem exists_sentenceTheory_comp_eq {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    {f : X → RelationalConfiguration L V} (hf : Measurable f)
    {g : X → ι → Bool} (hg : Measurable g)
    (hinv : ∀ x y, isoSetoid L V (f x) (f y) → g x = g y) :
    ∃ θ : ι → L.Sentenceω, ∀ x, sentenceTheory θ (f x) = g x := by
  have hcoord (i : ι) : ∃ φ : L.Sentenceω, ∀ x, f x ∈ modelsOf φ ↔ g x i = true := by
    have hgi : Measurable fun x => g x i := (measurable_pi_apply i).comp hg
    refine exists_sentence_mem_modelsOf_iff hf (hgi (measurableSet_singleton true))
      fun x y hxy => ?_
    simp only [mem_preimage, mem_singleton_iff, hinv x y hxy]
  choose θ hθ using hcoord
  refine ⟨θ, fun x => funext fun i => Bool.eq_iff_iff.2 ?_⟩
  simpa only [sentenceTheory_eq_true_iff] using hθ i x

/-- **Borel observables on a Borel set of configurations.** On a Borel subset `C` of
configurations over a countable carrier in a countable relational vocabulary, any measurable
isomorphism-invariant map `g : C → ι → Bool` is realized by `sentenceTheory θ` for some family
`θ : ι → L.Sentenceω`. -/
theorem exists_sentenceTheory_eq_on {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C)
    {g : C → ι → Bool} (hg : Measurable g)
    (hinv : ∀ ⦃x y : C⦄, isoSetoid L V x.val y.val → g x = g y) :
    ∃ θ : ι → L.Sentenceω, ∀ x : C, sentenceTheory θ x.val = g x := by
  have := hC.standardBorel
  exact exists_sentenceTheory_comp_eq measurable_subtypeVal hg fun x y hxy => hinv hxy

/-- **Borel observables into countably separated spaces.** If `Z` is a countably separated
measurable space and `g : X → Z` is an isomorphism-invariant measurable map along a standard Borel
family `f : X → RelationalConfiguration L V`, there are a measurable injection `e : Z → ℕ → Bool`
and sentences `θ : ℕ → L.Sentenceω` such that `e (g x) = sentenceTheory θ (f x)` for all `x`. -/
theorem exists_measurable_injective_comp_eq_sentenceTheory
    {X Z : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    {f : X → RelationalConfiguration L V} (hf : Measurable f)
    {g : X → Z} (hg : Measurable g)
    (hinv : ∀ x y, isoSetoid L V (f x) (f y) → g x = g y) :
    ∃ (e : Z → ℕ → Bool) (θ : ℕ → L.Sentenceω),
      Measurable e ∧ Function.Injective e ∧ ∀ x, e (g x) = sentenceTheory θ (f x) := by
  obtain ⟨e, he_meas, he_inj⟩ :=
    MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated Z
  obtain ⟨θ, hθ⟩ := exists_sentenceTheory_comp_eq hf (he_meas.comp hg)
    fun x y hxy => congrArg e (hinv x y hxy)
  exact ⟨e, θ, he_meas, he_inj, fun x => (hθ x).symm⟩

/-- **Fibrewise representation of Borel observables.** Any isomorphism-invariant measurable map
`g : X → Z` from a standard Borel family into a countably separated measurable space `Z` has the
same fibres as `sentenceTheory θ ∘ f` for some countable sequence `θ : ℕ → L.Sentenceω`. -/
theorem exists_sentenceTheory_eq_iff_of_countablySeparated
    {X Z : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    {f : X → RelationalConfiguration L V} (hf : Measurable f)
    {g : X → Z} (hg : Measurable g)
    (hinv : ∀ x y, isoSetoid L V (f x) (f y) → g x = g y) :
    ∃ θ : ℕ → L.Sentenceω,
      ∀ x y, g x = g y ↔ sentenceTheory θ (f x) = sentenceTheory θ (f y) := by
  obtain ⟨e, θ, -, he_inj, heq⟩ := exists_measurable_injective_comp_eq_sentenceTheory hf hg hinv
  exact ⟨θ, fun x y => ⟨fun h => by rw [← heq x, ← heq y, h],
    fun h => he_inj (by rw [heq x, heq y, h])⟩⟩

/-- **Cantor recovery.** For a countable index type `ι` (in particular `ι = ℕ`) and a measurable
map `f : (ι → Bool) → RelationalConfiguration L V` sending distinct points to non-isomorphic
configurations, some `θ : ι → L.Sentenceω` satisfies `sentenceTheory θ (f x) = x` for every `x`. -/
theorem exists_sentenceTheory_apply_eq [Countable ι]
    {f : (ι → Bool) → RelationalConfiguration L V} (hf : Measurable f)
    (hne : ∀ x y, x ≠ y → ¬ isoSetoid L V (f x) (f y)) :
    ∃ θ : ι → L.Sentenceω, ∀ x, sentenceTheory θ (f x) = x :=
  exists_sentenceTheory_comp_eq hf measurable_id fun x y hxy =>
    by_contra fun h => hne x y h hxy

/-- Coordinatewise form of Cantor recovery: some `θ : ι → L.Sentenceω` satisfies
`f x ∈ modelsOf (θ i) ↔ x i = true` for every `x : ι → Bool` and `i : ι`. -/
theorem exists_forall_mem_modelsOf_iff [Countable ι]
    {f : (ι → Bool) → RelationalConfiguration L V} (hf : Measurable f)
    (hne : ∀ x y, x ≠ y → ¬ isoSetoid L V (f x) (f y)) :
    ∃ θ : ι → L.Sentenceω, ∀ x i, f x ∈ modelsOf (θ i) ↔ x i = true := by
  obtain ⟨θ, hθ⟩ := exists_sentenceTheory_apply_eq hf hne
  refine ⟨θ, fun x i => ?_⟩
  simpa only [sentenceTheory_eq_true_iff] using
    (congrArg (· = true) (congrFun (hθ x) i)).to_iff

end TauCeti.RelationalConfiguration
