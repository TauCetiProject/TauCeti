/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Scattered.Concentration
public import TauCeti.ModelTheory.RelationalConfiguration.Separation
public import TauCeti.ModelTheory.Counting.Classes

/-!
# Analytic splits of concentrated classes

An isomorphism-invariant split of a concentrated class has a side meeting only countably many
isomorphism classes, provided both sides are analytic. Uniform back-and-forth separation makes
the split saturated at one countable level, where concentration supplies the countable side.
The ambient class need not be invariant under isomorphism.

We also give the relative Borel form and the sentence-cut form. In particular, for a sentence
whose models on `ℕ` are concentrated, every strengthening by another sentence or its negation
has a side with countably many models up to isomorphism. This is the splitting property used in
the characterization of minimally uncountable sentences.

## References

* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII,
  §XII.2 (concentration and minimally uncountable sentences).
* The concentration argument is also formalized in Cameron Freer's
  `cameronfreer/infinitary-logic`, `InfinitaryLogic/Descriptive/BFConcentration.lean`
  (checkpoint `518a366`, Apache-2.0). Here we combine the existing concentration and uniform
  separation APIs, and state the split relative to the ambient class.
-/

public section

universe u v uι

open FirstOrder FirstOrder.Language MeasureTheory Set

namespace TauCeti.ConcentratedAtBFLevels

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational]
variable {B C : Set (RelationalConfiguration L ℕ)}

/-- An isomorphism-invariant split of a concentrated class into two analytic sides has a side
meeting countably many isomorphism classes. No countability of the language is required. -/
theorem countable_isoClasses_inter_or_sdiff_of_analyticSet (hC : ConcentratedAtBFLevels C)
    (hCB : AnalyticSet (C ∩ B)) (hCdiff : AnalyticSet (C \ B))
    (hinv : ∀ c ∈ C, ∀ d ∈ C, isoSetoid L ℕ c d → c ∈ B → d ∈ B) :
    Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : ↥(C ∩ B) → _))) ∨
      Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : ↥(C \ B) → _))) := by
  obtain ⟨α, hα, hsat⟩ := exists_bfLevel_mem_iff_of_analyticSet hCB hCdiff hinv
  have hdiff : C \ (C ∩ B) = C \ B := by ext; simp
  have h := hC.countable_isoClasses_or_of_saturated inter_subset_left hα
    (fun b hb c hc hbc => ⟨hc, (hsat α le_rfl b hb.1 c hc hbc).mp hb.2⟩)
  simp only [Setoid.countable_quotient_comap_val_iff] at h ⊢
  simpa only [hdiff] using h

/-- A relatively isomorphism-invariant Borel cut of an analytic concentrated class has a side
meeting countably many isomorphism classes. -/
theorem countable_isoClasses_inter_or_sdiff_of_measurableSet [∀ n, Countable (L.Relations n)]
    (hC : ConcentratedAtBFLevels C) (hCan : AnalyticSet C) (hB : MeasurableSet B)
    (hinv : ∀ c ∈ C, ∀ d ∈ C, isoSetoid L ℕ c d → c ∈ B → d ∈ B) :
    Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : ↥(C ∩ B) → _))) ∨
      Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : ↥(C \ B) → _))) := by
  exact hC.countable_isoClasses_inter_or_sdiff_of_analyticSet
    (hCan.inter_measurableSet hB) (sdiff_eq C B ▸ hCan.inter_measurableSet hB.compl) hinv

/-- Every sentence cut of an analytic concentrated class has a side meeting countably many
isomorphism classes. The class itself need not be invariant under isomorphism. -/
theorem countable_isoClasses_inter_modelsOf_or_sdiff [∀ n, Countable (L.Relations n)]
    {ι : Type uι} [Countable ι] (hC : ConcentratedAtBFLevels C) (hCan : AnalyticSet C)
    (θ : L.SentenceInf ι) :
    Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : ↥(C ∩ modelsOf θ) → _))) ∨
      Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : ↥(C \ modelsOf θ) → _))) := by
  refine hC.countable_isoClasses_inter_or_sdiff_of_measurableSet hCan
    (measurableSet_modelsOf θ) ?_
  intro c _ d _ hcd hc
  obtain ⟨e⟩ := isoSetoid_apply.mp hcd
  exact (e.mem_modelsOf_iff θ).mp hc

/-- If the models of `φ` on `ℕ` are concentrated, then either `φ ∧ θ` or `φ ∧ ¬θ` has only
countably many models on `ℕ` up to isomorphism. -/
theorem countable_quotient_isoSetoidOn_inf_or_inf_not [∀ n, Countable (L.Relations n)]
    {ι : Type uι} [Countable ι] {φ : L.SentenceInf ι}
    (hφ : ConcentratedAtBFLevels (modelsOf (V := ℕ) φ)) (θ : L.SentenceInf ι) :
    Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ))) ∨
      Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ.not))) := by
  have h := hφ.countable_isoClasses_inter_modelsOf_or_sdiff
    (measurableSet_modelsOf φ).analyticSet θ
  simp only [isoSetoidOn, Setoid.countable_quotient_comap_val_iff] at h ⊢
  simpa only [modelsOf_inf, modelsOf_not, sdiff_eq] using h

end TauCeti.ConcentratedAtBFLevels
