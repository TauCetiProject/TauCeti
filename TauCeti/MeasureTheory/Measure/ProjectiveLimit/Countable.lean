/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.ProjectiveLimit.Nat
public import TauCeti.MeasureTheory.Constructions.Projective

/-!
# Projective limits on countable products

This file extends the sequence-indexed Kolmogorov extension theorem from
`TauCeti.MeasureTheory.Measure.ProjectiveLimit.Nat` to an arbitrary countable index type. Finite
index types are handled directly by the law on all coordinates; infinite countable types are
enumerated and reduced to the sequence theorem.

## Main result

* `TauCeti.Measure.exists_isProjectiveLimit_of_countable` realizes every projective family of
  probability laws on finite subsets of a countable family of standard Borel spaces.

* `Function.Embedding.exists_measurePreserving_finset_map_of_countable` realizes the restriction
  of a projective family of probability laws to any countable embedded family of standard Borel
  spaces.
* `Set.exists_measurePreserving_finset_of_countable` states the marginals directly on finite sets
  contained in a countable coordinate set.

The proof transports finite-dimensional laws along measurable equivalences of dependent products.
-/

public section

noncomputable section

open Finset MeasureTheory Function.Embedding

namespace TauCeti

namespace Measure

universe u v

variable {ι : Type u} {κ : Type v} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- A projective family on a finite coordinate type is realized by its law on the full finite
product. -/
private theorem exists_isProjectiveLimit_of_finite [Finite ι]
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃ μ : Measure (∀ i, X i), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P := by
  let _ := Fintype.ofFinite ι
  let e : (Finset.univ : Finset ι) ≃ ι :=
    { toFun := fun i ↦ i
      invFun := fun i ↦ ⟨i, Finset.mem_univ i⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let E : (∀ j : (Finset.univ : Finset ι), X j) ≃ᵐ (∀ i, X i) :=
    MeasurableEquiv.piCongrLeft X e
  refine ⟨(P Finset.univ).map E,
    inferInstance, fun I ↦ ?_⟩
  rw [MeasureTheory.Measure.map_map (Finset.measurable_restrict I) E.measurable]
  have hrestrict : I.restrict ∘ E =
      Finset.restrict₂ (Finset.subset_univ I) := by
    funext x i
    simpa [Function.comp_apply, Finset.restrict_def, Finset.restrict₂_def, E, e] using
      MeasurableEquiv.piCongrLeft_apply_apply
        (β := X) e x ⟨i, Finset.mem_univ (i : ι)⟩
  rw [hrestrict, hP Finset.univ I (Finset.subset_univ I)]

/-- An infinite countable projective family is realized by enumerating its coordinates and
applying the sequence-indexed extension theorem. -/
private theorem exists_isProjectiveLimit_of_countable_infinite [Countable ι] [Infinite ι]
    [∀ i, StandardBorelSpace (X i)]
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃ μ : Measure (∀ i, X i), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P := by
  let e : ℕ ≃ ι := Classical.choice (inferInstance : Nonempty (ℕ ≃ ι))
  let Q : ∀ J : Finset ℕ, Measure (∀ j : J, X (e j)) := reindexFamily e.toEmbedding P
  have hQ : IsProjectiveMeasureFamily (α := fun j ↦ X (e j)) Q :=
    isProjectiveMeasureFamily_reindexFamily e.toEmbedding P hP
  let _ : ∀ n, StandardBorelSpace (X (e (n + 1))) := fun _ ↦ inferInstance
  obtain ⟨ν, hνprob, hν⟩ :=
    exists_isProjectiveLimit_nat (X := fun n ↦ X (e n)) Q hQ
  let E : (∀ n, X (e n)) ≃ᵐ (∀ i, X i) := MeasurableEquiv.piCongrLeft X e
  refine ⟨ν.map E, inferInstance,
    fun I ↦ ?_⟩
  let J : Finset ℕ := I.map e.symm.toEmbedding
  have hmap : J.map e.toEmbedding = I := by
    simp [J, Finset.map_map]
  have hcomm : (J.map e.toEmbedding).restrict ∘ E =
      piFinsetMapMeasurableEquiv e.toEmbedding J ∘ J.restrict := by
    funext x i
    let j : J := (J.equivMap e.toEmbedding).symm i
    rw [Function.comp_apply, Function.comp_apply,
      ← (J.equivMap e.toEmbedding).apply_symm_apply i,
      piFinsetMapMeasurableEquiv_apply_apply]
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := X) e x j
  have hlimit : (ν.map E).map (J.map e.toEmbedding).restrict =
      P (J.map e.toEmbedding) := by
    rw [MeasureTheory.Measure.map_map (Finset.measurable_restrict (J.map e.toEmbedding))
      E.measurable, hcomm]
    exact (e.toEmbedding.isProjectiveLimit_reindexFamily_iff P ν).mp hν J
  exact hmap ▸ hlimit

/-- **Kolmogorov extension on an arbitrary countable index type.** Every projective family of
probability laws on the finite subproducts of a countable family of standard Borel spaces has a
projective limit, which is again a probability measure.

For finite index types the full-dimensional member of the family is already the desired law. For
infinite countable types, an enumeration reduces the result to
`TauCeti.Measure.exists_isProjectiveLimit_nat`. Mathlib's
`MeasureTheory.IsProjectiveLimit.unique` gives uniqueness. -/
theorem exists_isProjectiveLimit_of_countable [Countable ι]
    [∀ i, StandardBorelSpace (X i)]
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃ μ : Measure (∀ i, X i), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P := by
  rcases finite_or_infinite ι with hι | hι
  · exact exists_isProjectiveLimit_of_finite P hP
  · exact exists_isProjectiveLimit_of_countable_infinite P hP

end Measure

end TauCeti

namespace Function.Embedding

open TauCeti.Measure

variable {ι κ : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- Realize a projective family of probability laws along a countable embedding `e : κ ↪ ι`
with standard Borel fibers `X (e j)`. The finite-dimensional marginals are transported by
`piFinsetMapMeasurableEquiv` to the original coordinate labels against `P (J.map e)`. -/
theorem exists_measurePreserving_finset_map_of_countable [Countable κ] (e : κ ↪ ι)
    [∀ j, StandardBorelSpace (X (e j))]
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃ μ : Measure (∀ j, X (e j)), IsProbabilityMeasure μ ∧ ∀ J : Finset κ,
      MeasurePreserving (piFinsetMapMeasurableEquiv e J ∘ J.restrict) μ (P (J.map e)) := by
  let Q := reindexFamily e P
  obtain ⟨μ, hμprob, hμ⟩ := exists_isProjectiveLimit_of_countable (X := fun j ↦ X (e j)) Q
    (isProjectiveMeasureFamily_reindexFamily e P hP)
  refine ⟨μ, hμprob, fun J ↦ ⟨by fun_prop, ?_⟩⟩
  exact (e.isProjectiveLimit_reindexFamily_iff P μ).mp hμ J

end Function.Embedding

namespace Set

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- Realize a projective family of probability laws on a countable set of standard Borel
coordinates. Its marginals are stated directly on finite sets contained in that set. -/
theorem exists_measurePreserving_finset_of_countable (S : Set ι) [Countable S]
    [∀ i : S, StandardBorelSpace (X i)]
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃ μ : Measure (∀ i : S, X i), IsProbabilityMeasure μ ∧
      ∀ (I : Finset ι) (hI : (I : Set ι) ⊆ S),
        MeasurePreserving (fun x (i : I) ↦ x ⟨i.1, hI i.2⟩) μ (P I) := by
  let e : S ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  obtain ⟨μ, hprob, hμ⟩ := e.exists_measurePreserving_finset_map_of_countable P hP
  have hlimit := (e.isProjectiveLimit_reindexFamily_iff P μ).mpr (fun J ↦ (hμ J).map_eq)
  refine ⟨μ, hprob, fun I hI ↦ ⟨by fun_prop, ?_⟩⟩
  exact (S.isProjectiveLimit_reindexFamily_iff P μ).mp hlimit I hI

end Set
