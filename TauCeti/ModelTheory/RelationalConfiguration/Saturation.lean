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
# Back-and-forth saturation of model classes

On a countable carrier `V`, in a relational language with countably many relation symbols of each
arity, the model class `TauCeti.RelationalConfiguration.modelsOf θ` of an infinitary sentence `θ`
with countable branching is Borel and invariant under isomorphism of decoded structures. By uniform
back-and-forth separation
(`TauCeti.RelationalConfiguration.exists_bfLevel_mem_iff_of_measurableSet`), there is a countable
ordinal `β₀ < ω₁` from which onward `bfEquivSetoid L V β`-equivalent configurations lie on the same
side of `modelsOf θ`: every model class is a union of back-and-forth classes from some countable
level onward.

This descriptive-set-theoretic saturation argument avoids computing a syntactic quantifier rank for
`θ`. By regularity of `ω₁`, any countable family of sentences admits a single countable saturation
level above which all of its members are simultaneously saturated, as needed when building trees of
back-and-forth classes cut by countably many splitting sentences.

## Main results

* `TauCeti.RelationalConfiguration.exists_bfLevel_mem_modelsOf_iff_of_analyticSet`: relative
  saturation of `modelsOf θ` within an analytic set of configurations.
* `TauCeti.RelationalConfiguration.exists_bfLevel_saturated_modelsOf`: every sentence with countable
  branching is saturated from some countable back-and-forth level onward.
* `TauCeti.RelationalConfiguration.exists_bfLevel_forall_saturated_modelsOf`: simultaneous
  saturation of a countable family of sentences at a single countable level.

## References

* V. Harnik and M. Makkai, *A tree argument in infinitary model theory*, Proc. Amer. Math. Soc. 67
  (1977), 309–314.
* A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII, §XII.2
  (saturation of sentences along back-and-forth levels, proved here via uniform separation rather
  than syntactic quantifier complexity).
-/

public section

universe u v w o uι uκ

open FirstOrder FirstOrder.Language MeasureTheory Ordinal Set

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]
variable {V : Type w} [Countable V] {ι : Type uι} [Countable ι]

/-- **Relative back-and-forth saturation of a model class.** Within an analytic set `C` of
configurations on a countable carrier, an infinitary sentence `θ` with countable branching is
invariant from some countable back-and-forth level `β₀ < ω₁` onward. -/
theorem exists_bfLevel_mem_modelsOf_iff_of_analyticSet
    {C : Set (RelationalConfiguration L V)} (hC : AnalyticSet C) (θ : L.SentenceInf ι) :
    ∃ β₀ : Ordinal.{o}, β₀ < ω₁ ∧
      ∀ β ≥ β₀, ∀ c ∈ C, ∀ d ∈ C,
        bfEquivSetoid L V β c d → (c ∈ modelsOf θ ↔ d ∈ modelsOf θ) := by
  refine exists_bfLevel_mem_iff_of_measurableSet hC (measurableSet_modelsOf θ) ?_
  intro c _ d _ hcd hc
  obtain ⟨e⟩ := isoSetoid_apply.mp hcd
  exact (e.mem_modelsOf_iff θ).mp hc

/-- **Back-and-forth saturation of a sentence.** On a countable carrier in a relational language
with countably many relation symbols of each arity, every infinitary sentence `θ` with countable
branching has a countable level `β₀ < ω₁` above which `bfEquivSetoid L V β`-equivalent
configurations agree on `θ`. -/
theorem exists_bfLevel_saturated_modelsOf (θ : L.SentenceInf ι) :
    ∃ β₀ : Ordinal.{o}, β₀ < ω₁ ∧
      ∀ β ≥ β₀, ∀ c d : RelationalConfiguration L V,
        bfEquivSetoid L V β c d → (c ∈ modelsOf θ ↔ d ∈ modelsOf θ) := by
  obtain ⟨β₀, hβ₀, hsat⟩ :=
    exists_bfLevel_mem_modelsOf_iff_of_analyticSet.{u, v, w, o, uι}
      (C := (univ : Set (RelationalConfiguration L V))) isClosed_univ.analyticSet θ
  exact ⟨β₀, hβ₀, fun β hβ c d hcd => hsat β hβ c (mem_univ c) d (mem_univ d) hcd⟩

/-- **Simultaneous back-and-forth saturation of a countable family of sentences.** For a countable
family `θ : κ → L.SentenceInf ι`, there is a single countable level `β₀ < ω₁` above which every
`modelsOf (θ k)` is saturated. -/
theorem exists_bfLevel_forall_saturated_modelsOf {κ : Type uκ} [Countable κ]
    (θ : κ → L.SentenceInf ι) :
    ∃ β₀ : Ordinal.{o}, β₀ < ω₁ ∧
      ∀ β ≥ β₀, ∀ (k : κ) (c d : RelationalConfiguration L V),
        bfEquivSetoid L V β c d → (c ∈ modelsOf (θ k) ↔ d ∈ modelsOf (θ k)) := by
  choose f hf hsat using fun k =>
    exists_bfLevel_saturated_modelsOf.{u, v, w, o, uι} (V := V) (θ k)
  have hbdd : BddAbove (range f) := ⟨ω₁, forall_mem_range.2 fun k => (hf k).le⟩
  refine ⟨⨆ k, f k, Ordinal.iSup_lt_omega_one hf, fun β hβ k c d hcd => ?_⟩
  exact hsat k β ((le_ciSup hbdd k).trans hβ) c d hcd

end TauCeti.RelationalConfiguration
