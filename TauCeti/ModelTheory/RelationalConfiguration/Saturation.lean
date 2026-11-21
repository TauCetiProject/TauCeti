/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.BackAndForth
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
import TauCeti.ModelTheory.BackAndForth.Karp
import TauCeti.ModelTheory.RelationalConfiguration.Separation

/-!
# Asymptotic back-and-forth saturation of model classes

Every infinitary sentence `θ` with countable branching is asymptotically saturated by
back-and-forth equivalence: there is a countable threshold `α < ω₁` such that for all `β ≥ α`,
`bfEquivSetoid L V β`-equivalent configurations agree on `modelsOf θ`
(`exists_bfLevel_saturated_modelsOf`). The threshold is the quantifier rank of `θ`, so no
countability of the carrier or of the vocabulary is needed. On a countable carrier in a vocabulary
with countably many relation symbols of each arity, uniform back-and-forth separation also gives
the relative form on any analytic set `C` of configurations
(`exists_bfLevel_mem_modelsOf_iff_of_analyticSet`).

Asymptotic sentence saturation lets counting and splitting-tree arguments refine sentence cuts of a
configuration class into unions of back-and-forth classes at a common countable level below `ω₁`.

## Main results

* `TauCeti.RelationalConfiguration.exists_bfLevel_mem_modelsOf_iff_of_analyticSet`: relative
  asymptotic back-and-forth saturation of `modelsOf θ` on an analytic set of configurations.
* `TauCeti.RelationalConfiguration.exists_bfLevel_saturated_modelsOf`: global asymptotic
  back-and-forth saturation of `modelsOf θ`, from the quantifier rank of `θ` on.

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
    ((isomorphismInvariant_modelsOf θ).mem_iff hcd).mp

/-- **Asymptotic back-and-forth saturation of model classes.** For every infinitary sentence `θ`
with countable branching there is a countable ordinal `α < ω₁` such that from level `α` onward,
back-and-forth equivalent configurations agree on `θ`. The level is the quantifier rank of `θ`,
which is countable; no countability of the carrier or of the vocabulary is needed. -/
theorem exists_bfLevel_saturated_modelsOf [Countable ι] (θ : L.SentenceInf ι) :
    ∃ α : Ordinal.{o}, α < ω₁ ∧
      ∀ β ≥ α, ∀ c d : RelationalConfiguration L V,
        bfEquivSetoid L V β c d → (c ∈ modelsOf θ ↔ d ∈ modelsOf θ) := by
  -- the quantifier rank of `θ` is countable, so it is the lift of a countable level `α`
  have hθ : Ordinal.lift.{o} θ.qrank ≤ Ordinal.lift.{uι} (ω₁ : Ordinal.{o}) := by
    simpa only [Ordinal.lift_omega, Ordinal.lift_one] using
      Ordinal.lift_le.{o}.2 (BoundedFormulaInf.qrank_lt_omega_one θ).le
  obtain ⟨α, hα⟩ := Ordinal.mem_range_lift_of_le hθ
  refine ⟨α, ?_, fun β hβ c d hcd => ?_⟩
  · rw [← Ordinal.lift_lt.{uι}, hα]
    simpa only [Ordinal.lift_omega, Ordinal.lift_one] using
      Ordinal.lift_lt.{o}.2 (BoundedFormulaInf.qrank_lt_omega_one θ)
  · have h := @BFEquiv.realize_iff_of_qrank_le L V V c.toStructure d.toStructure _ ι 0 θ β
      Fin.elim0 Fin.elim0 (bfEquivSetoid_apply.1 hcd) (hα ▸ Ordinal.lift_le.2 hβ)
      Empty.elim Empty.elim
    simpa only [mem_modelsOf, SentenceInf.realize_def, FormulaInf.realize_def,
      Subsingleton.elim default (Fin.elim0 : Fin 0 → V),
      Subsingleton.elim default (Empty.elim : Empty → V)] using h

end TauCeti.RelationalConfiguration
