/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Statistics.Experiments.Mixture
public import TauCeti.Statistics.Sufficiency.Basic

/-!
# Preservation of sufficiency under countable mixtures

This file proves that sufficiency of a statistic `T` for a parametric family `P : Θ → Measure X`
is preserved under taking countable mixtures `TauCeti.countableMixture P (θss ι)` (with no
domination assumption on `P`), retaining the same parameter-free Markov kernel:

* `TauCeti.IsSufficientStatistic.countableMixture`: sufficiency for a family of countable mixtures
  `fun ι ↦ TauCeti.countableMixture P (θss ι)`.
* `TauCeti.IsSufficientStatistic.sumElim_countableMixture`: sufficiency for the extended family
  `Sum.elim P (fun ι ↦ TauCeti.countableMixture P (θss ι))`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

variable {Θ X S : Type*} [MeasurableSpace X] [MeasurableSpace S]

/-- Taking countable mixtures `TauCeti.countableMixture P (θss ι)` preserves sufficiency of `T`,
with a single common Markov kernel. -/
theorem IsSufficientStatistic.countableMixture {P : Θ → Measure X} {T : X → S}
    (h : IsSufficientStatistic P T) {Ι : Type*} (θss : Ι → ℕ → Θ) :
    IsSufficientStatistic (fun ι ↦ TauCeti.countableMixture P (θss ι)) T := by
  obtain ⟨hT, K, hK, hdis⟩ := isSufficientStatistic_def.mp h
  rw [isSufficientStatistic_def]
  exact ⟨hT, K, hK, fun ι ↦ map_prodMk_countableMixture_eq_compProd hT fun n ↦ hdis (θss ι n)⟩

/-- Adjoining countable mixtures `TauCeti.countableMixture P (θss ι)` to `P` preserves
sufficiency with a single common Markov kernel shared by `P` and all mixtures. -/
theorem IsSufficientStatistic.sumElim_countableMixture {P : Θ → Measure X} {T : X → S}
    (h : IsSufficientStatistic P T) {Ι : Type*} (θss : Ι → ℕ → Θ) :
    IsSufficientStatistic (Sum.elim P (fun ι ↦ TauCeti.countableMixture P (θss ι))) T := by
  obtain ⟨hT, K, hK, hdis⟩ := isSufficientStatistic_def.mp h
  rw [isSufficientStatistic_def]
  refine ⟨hT, K, hK, ?_⟩
  rintro (θ | ι)
  · exact hdis θ
  · exact map_prodMk_countableMixture_eq_compProd hT fun n ↦ hdis (θss ι n)

end TauCeti
