/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
public import TauCeti.ModelTheory.RelationalConfiguration.Separation
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Asymptotic back-and-forth saturation of model classes

Every infinitary sentence `θ` defines an isomorphism-invariant class `modelsOf θ` of relational
configurations on any carrier (`isomorphismInvariant_modelsOf`). When the carrier `V` is countable,
the branching index `ι` is countable, and the relational language `L` has countably many relation
symbols of each arity, `modelsOf (V := V) θ` is an isomorphism-invariant Borel subset of the Polish
space `RelationalConfiguration L V`.

Applying uniform back-and-forth separation
(`IsomorphismInvariant.exists_bfLevel_mem_iff_of_measurableSet`) therefore produces a countable
ordinal threshold `α < ω₁` from which `modelsOf (V := V) θ` is a union of back-and-forth
equivalence classes (`exists_bfLevel_saturated_modelsOf`): for every `β ≥ α`, configurations on `V`
that are `β`-equivalent agree on `θ`. Neither syntactic quantifier rank nor the López–Escobar
theorem is needed. By regularity of `ω₁`, any countable family of such sentences admits a single
countable saturation threshold (`exists_bfLevel_forall_saturated_modelsOf`).

## Main results

* `TauCeti.RelationalConfiguration.isomorphismInvariant_modelsOf`: model classes are closed under
  isomorphism of configurations on any carrier.
* `TauCeti.RelationalConfiguration.exists_bfLevel_saturated_modelsOf`: on a countable carrier in a
  countable relational vocabulary, every sentence with countable branching is back-and-forth
  saturated from some countable level `α < ω₁` onward.
* `TauCeti.RelationalConfiguration.exists_bfLevel_forall_saturated_modelsOf`: uniform saturation at
  a single countable level `α < ω₁` across a countable family of sentences.

## References

* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016.
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Cambridge University
  Press, 2021, Part 2, Chapter XII.
* Adapted from `exists_bfLevel_saturated_modelsOf` in
  `InfinitaryLogic/Descriptive/MinimallyUncountable.lean` of Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a39bc3e0b`, Apache-2.0),
  generalized here to arbitrary countable carriers, countable branching types, and ordinal
  universes.
-/

public section

universe u v w uι o

open FirstOrder FirstOrder.Language Ordinal

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {ι : Type uι}

/-- Model classes are invariant under isomorphism of decoded structures on any carrier. -/
theorem isomorphismInvariant_modelsOf (θ : L.SentenceInf ι) :
    IsomorphismInvariant (modelsOf (V := V) θ) :=
  isomorphismInvariant_iff.mpr fun _ _ hcd hc => by
    obtain ⟨e⟩ := isoSetoid_apply.mp hcd
    exact (e.mem_modelsOf_iff θ).mp hc

/-- **Asymptotic back-and-forth saturation of a sentence.** On a countable carrier `V` in a
vocabulary with countably many relation symbols of each arity, every infinitary sentence `θ` with
countable branching is saturated from some countable back-and-forth level `α < ω₁` onward: for
every `β ≥ α`, `β`-equivalent configurations on `V` agree on `θ`. -/
theorem exists_bfLevel_saturated_modelsOf [Countable V] [∀ n, Countable (L.Relations n)]
    [Countable ι] (θ : L.SentenceInf ι) :
    ∃ α : Ordinal.{o}, α < ω₁ ∧
      ∀ β ≥ α, ∀ c d : RelationalConfiguration L V,
        bfEquivSetoid L V β c d → (c ∈ modelsOf θ ↔ d ∈ modelsOf θ) :=
  (isomorphismInvariant_modelsOf θ).exists_bfLevel_mem_iff_of_measurableSet
    (measurableSet_modelsOf θ)

/-- **Uniform back-and-forth saturation of a countable family of sentences.** On a countable
carrier `V` in a vocabulary with countably many relation symbols of each arity, any countable
family of sentences with countable branching admits a single countable threshold `α < ω₁` above
which `bfEquivSetoid L V β`-equivalent configurations agree on every sentence in the family. -/
theorem exists_bfLevel_forall_saturated_modelsOf [Countable V] [∀ n, Countable (L.Relations n)]
    [Countable ι] {κ : Type*} [Countable κ] (θ : κ → L.SentenceInf ι) :
    ∃ α : Ordinal.{o}, α < ω₁ ∧
      ∀ i, ∀ β ≥ α, ∀ c d : RelationalConfiguration L V,
        bfEquivSetoid L V β c d → (c ∈ modelsOf (θ i) ↔ d ∈ modelsOf (θ i)) := by
  classical
  choose α hα hsat using fun i => exists_bfLevel_saturated_modelsOf.{u, v, w, uι, o} (V := V) (θ i)
  refine ⟨⨆ i, α i, Ordinal.iSup_lt_omega_one hα, fun i β hβ => ?_⟩
  exact hsat i β ((Ordinal.le_iSup α i).trans hβ)

end TauCeti.RelationalConfiguration
