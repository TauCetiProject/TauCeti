/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Scattered.AnalyticSplits
public import TauCeti.ModelTheory.Counting.Scattered.SentenceSplits

/-!
# Minimally uncountable classes of countable structures

A class is minimally uncountable if it meets uncountably many isomorphism classes, but every
cut by an infinitary sentence has a side meeting only countably many. The cuts are by sentences,
not by arbitrary invariant sets. This is the minimality notion used in the reduction of Vaught
counterexamples to minimally uncountable sentences.

A concentrated analytic class is minimally uncountable exactly when it meets uncountably many
isomorphism classes. Conversely, a scattered minimally uncountable class is concentrated.

## References

* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII,
  §XII.2 (minimal unboundedness and the reduction to minimal counterexamples).
* V. Harnik and M. Makkai, *A tree argument in infinitary model theory*, Proceedings of the
  American Mathematical Society 67 (1977), 309–314.
-/

public section

universe u v

open FirstOrder FirstOrder.Language Set MeasureTheory

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational]
variable {K : Set (RelationalConfiguration L ℕ)}

/-- A class meets uncountably many isomorphism classes and every sentence cut has a side
meeting countably many. No definability or invariance of the class is assumed. -/
def MinimallyUncountableOn (K : Set (RelationalConfiguration L ℕ)) : Prop :=
  ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable ∧
    ∀ θ : L.Sentenceω,
      (Quotient.mk (isoSetoid L ℕ) '' (K ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L ℕ) '' (K \ modelsOf θ)).Countable

/-- The defining uncountability and sentence-splitting conditions. -/
theorem minimallyUncountableOn_iff : MinimallyUncountableOn K ↔
    ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable ∧
      ∀ θ : L.Sentenceω,
        (Quotient.mk (isoSetoid L ℕ) '' (K ∩ modelsOf θ)).Countable ∨
          (Quotient.mk (isoSetoid L ℕ) '' (K \ modelsOf θ)).Countable := Iff.rfl

/-- A minimally uncountable class meets uncountably many isomorphism classes. -/
theorem MinimallyUncountableOn.not_countable_isoClasses (h : MinimallyUncountableOn K) :
    ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable := h.1

/-- Every sentence cut of a minimally uncountable class has a countable side. -/
theorem MinimallyUncountableOn.splits (h : MinimallyUncountableOn K) (θ : L.Sentenceω) :
    (Quotient.mk (isoSetoid L ℕ) '' (K ∩ modelsOf θ)).Countable ∨
      (Quotient.mk (isoSetoid L ℕ) '' (K \ modelsOf θ)).Countable := h.2 θ

/-- The empty class is not minimally uncountable. -/
@[simp]
theorem not_minimallyUncountableOn_empty :
    ¬ MinimallyUncountableOn (∅ : Set (RelationalConfiguration L ℕ)) := by
  simp [minimallyUncountableOn_iff]

/-- A sentence has minimally uncountable models on `ℕ` exactly when its isomorphism quotient is
uncountable and every conjunction or negated conjunction has a countable side. -/
theorem minimallyUncountableOn_modelsOf_iff_splits (φ : L.Sentenceω) :
    MinimallyUncountableOn (modelsOf (V := ℕ) φ) ↔
      ¬ Countable (Quotient (isoSetoidOn ℕ φ)) ∧
        ∀ θ : L.Sentenceω, Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ))) ∨
          Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ.not))) := by
  simp only [minimallyUncountableOn_iff, isoSetoidOn,
    Setoid.countable_quotient_comap_val_iff, modelsOf_inf, modelsOf_not, sdiff_eq]

/-- A scattered minimally uncountable class is concentrated at back-and-forth levels. -/
theorem MinimallyUncountableOn.concentratedAtBFLevels [Countable (Σ n, L.Relations n)]
    (h : MinimallyUncountableOn K) (hK : BFScattered K) : ConcentratedAtBFLevels K :=
  concentratedAtBFLevels_of_bfScattered_of_sentence_splits hK h.splits

/-- For an analytic concentrated class, minimal uncountability is equivalent to uncountability
of its isomorphism classes. -/
theorem ConcentratedAtBFLevels.minimallyUncountableOn_iff [∀ n, Countable (L.Relations n)]
    (hK : ConcentratedAtBFLevels K) (han : AnalyticSet K) :
    MinimallyUncountableOn K ↔ ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable := by
  refine ⟨MinimallyUncountableOn.not_countable_isoClasses, fun h => ⟨h, fun θ => ?_⟩⟩
  simpa only [Setoid.countable_quotient_comap_val_iff] using
    hK.countable_isoClasses_inter_modelsOf_or_sdiff han θ

end TauCeti
