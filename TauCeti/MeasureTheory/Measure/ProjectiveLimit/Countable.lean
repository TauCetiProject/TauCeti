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
  of a projective family of probability laws on finite powers of a standard Borel space to any
  countable embedded coordinate type.

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
  let Q : ∀ J : Finset ℕ, Measure (∀ j : J, X (e j)) := reindexProjectiveFamily e.toEmbedding P
  have hQ : IsProjectiveMeasureFamily (α := fun j ↦ X (e j)) Q :=
    isProjectiveMeasureFamily_reindex e.toEmbedding P hP
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
      finitePiCongrLeft e.toEmbedding J ∘ J.restrict := by
    funext x i
    let j : J := (J.equivMap e.toEmbedding).symm i
    rw [Function.comp_apply, Function.comp_apply,
      ← (J.equivMap e.toEmbedding).apply_symm_apply i,
      finitePiCongrLeft_apply]
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := X) e x j
  have hlimit : (ν.map E).map (J.map e.toEmbedding).restrict =
      P (J.map e.toEmbedding) := by
    rw [MeasureTheory.Measure.map_map (Finset.measurable_restrict (J.map e.toEmbedding))
      E.measurable, hcomm]
    exact (e.toEmbedding.isProjectiveLimit_reindex_iff P ν).mp hν J
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

variable {ι κ : Type*}

/-- Realize a projective family of probability laws on finite powers of a standard Borel
space `E` along a countable embedding `e : κ ↪ ι`. The finite-dimensional marginals are
stated on the original coordinate labels against `P (J.map e)`. -/
theorem exists_measurePreserving_finset_map_of_countable {E : Type*}
    [MeasurableSpace E] [StandardBorelSpace E] [Countable κ] (e : κ ↪ ι)
    (P : (I : Finset ι) → Measure (I → E)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily (α := fun _ ↦ E) P) :
    ∃ μ : Measure (κ → E), IsProbabilityMeasure μ ∧ ∀ J : Finset κ,
      MeasurePreserving (fun x (i : J.map e) ↦ x ((J.equivMap e).symm i)) μ
        (P (J.map e)) := by
  let Q := reindexProjectiveFamily (X := fun _ ↦ E) e P
  have : ∀ J, IsProbabilityMeasure (Q J) := fun J ↦
    reindexProjectiveFamily.instIsProbabilityMeasure (X := fun _ ↦ E) e P J
  obtain ⟨μ, hμprob, hμ⟩ := exists_isProjectiveLimit_of_countable (X := fun _ ↦ E) Q
    (isProjectiveMeasureFamily_reindex (X := fun _ ↦ E) e P hP)
  refine ⟨μ, hμprob, fun J ↦ ⟨by fun_prop, ?_⟩⟩
  have hcomm : (fun (x : κ → E) (i : J.map e) ↦ x ((J.equivMap e).symm i)) =
      finitePiCongrLeft (X := fun _ ↦ E) e J ∘ J.restrict := by
    funext x i
    rw [← (J.equivMap e).apply_symm_apply i, Function.comp_apply,
      finitePiCongrLeft_apply]
    simp only [Equiv.symm_apply_apply, Finset.restrict_def]
  rw [hcomm]
  exact (e.isProjectiveLimit_reindex_iff (X := fun _ ↦ E) P μ).mp hμ J

end Function.Embedding
