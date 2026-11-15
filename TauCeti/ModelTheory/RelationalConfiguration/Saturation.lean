/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.BackAndForth
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
import TauCeti.ModelTheory.RelationalConfiguration.Separation

/-!
# Asymptotic back-and-forth saturation of model classes

On a countable carrier `V` in a relational language `L` with countably many relation symbols of
each arity, the model class `modelsOf θ` of an infinitary sentence `θ` with countable branching is
Borel (`measurableSet_modelsOf`) and invariant under isomorphism (`isoSetoid_mem_modelsOf_iff`).
Applying uniform back-and-forth separation (`exists_bfLevel_mem_iff_of_measurableSet`) therefore
produces a single countable threshold `α < ω₁` above which `bfEquivSetoid L V β` respects `θ`
(`exists_bfLevel_saturated_modelsOf`), both globally on `RelationalConfiguration L V` and
relatively on any analytic set of configurations (`exists_bfLevel_mem_modelsOf_iff_of_analyticSet`).

Descriptive boundedness replaces syntactic induction on infinitary quantifier rank: no hierarchy of
`Π_α` formulas or syntactic preservation theorem is needed to find a countable level at which a
sentence is a union of back-and-forth classes.

## Main results

* `TauCeti.RelationalConfiguration.isoSetoid_mem_modelsOf_iff`: isomorphic configurations on the
  same carrier satisfy the same infinitary sentences.
* `TauCeti.RelationalConfiguration.exists_bfLevel_mem_modelsOf_iff_of_analyticSet`: relative
  asymptotic back-and-forth saturation of `modelsOf θ` on an analytic set of configurations.
* `TauCeti.RelationalConfiguration.exists_bfLevel_saturated_modelsOf`: global asymptotic
  back-and-forth saturation of `modelsOf θ` on a countable carrier.

## References

* Victor Harnik and Michael Makkai, *A tree argument in infinitary model theory*, Proceedings of
  the American Mathematical Society 67 (1977), 309–314.
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Cambridge University
  Press, 2021, Part 2, Chapter XII, §XII.2.
* Specializing uniform back-and-forth separation to `modelsOf θ` adapts the sentence-saturation
  lemmas in `InfinitaryLogic/Descriptive/BFConcentration.lean` and
  `InfinitaryLogic/Descriptive/MinimallyUncountable.lean` of Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  Apache-2.0), generalized here to arbitrary `SentenceInf ι` with countable branching, arbitrary
  countable carriers, and arbitrary ordinal universes.
-/

public section

universe u v w uι o

open FirstOrder FirstOrder.Language MeasureTheory Ordinal Set

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {ι : Type uι}

/-- Isomorphic configurations on the same carrier satisfy the same infinitary sentences. -/
theorem isoSetoid_mem_modelsOf_iff {c d : RelationalConfiguration L V} {φ : L.SentenceInf ι}
    (h : isoSetoid L V c d) : c ∈ modelsOf φ ↔ d ∈ modelsOf φ := by
  obtain ⟨e⟩ := isoSetoid_apply.mp h
  exact e.mem_modelsOf_iff φ

/-- **Relative back-and-forth saturation of a model class.** On a countable carrier in a
relational language with countably many relation symbols of each arity, for any analytic set `C` of
configurations and any infinitary sentence `θ` with countable branching, there is a countable
ordinal `α < ω₁` such that from level `α` onward, `bfEquivSetoid L V β`-equivalent members of `C`
agree on `θ`. -/
theorem exists_bfLevel_mem_modelsOf_iff_of_analyticSet [Countable V]
    [∀ n, Countable (L.Relations n)] [Countable ι]
    {C : Set (RelationalConfiguration L V)} (hC : AnalyticSet C) (θ : L.SentenceInf ι) :
    ∃ α : Ordinal.{o}, α < ω₁ ∧
      ∀ β ≥ α, ∀ c ∈ C, ∀ d ∈ C, bfEquivSetoid L V β c d → (c ∈ modelsOf θ ↔ d ∈ modelsOf θ) :=
  exists_bfLevel_mem_iff_of_measurableSet hC (measurableSet_modelsOf θ) fun _ _ _ _ hcd =>
    (isoSetoid_mem_modelsOf_iff hcd).mp

/-- **Asymptotic back-and-forth saturation of model classes.** On a countable carrier in a
relational language with countably many relation symbols of each arity, for every infinitary
sentence `θ` with countable branching there is a countable ordinal `α < ω₁` such that from level
`α` onward, back-and-forth equivalent configurations agree on `θ`. -/
theorem exists_bfLevel_saturated_modelsOf [Countable V] [∀ n, Countable (L.Relations n)]
    [Countable ι] (θ : L.SentenceInf ι) :
    ∃ α : Ordinal.{o}, α < ω₁ ∧
      ∀ β ≥ α, ∀ c d : RelationalConfiguration L V,
        bfEquivSetoid L V β c d → (c ∈ modelsOf θ ↔ d ∈ modelsOf θ) := by
  have huniv : AnalyticSet (univ : Set (RelationalConfiguration L V)) :=
    MeasurableSet.univ.analyticSet
  obtain ⟨α, hα, hsat⟩ :=
    exists_bfLevel_mem_modelsOf_iff_of_analyticSet.{u, v, w, uι, o} huniv θ
  exact ⟨α, hα, fun β hαβ c d hcd => hsat β hαβ c (mem_univ c) d (mem_univ d) hcd⟩

end TauCeti.RelationalConfiguration
