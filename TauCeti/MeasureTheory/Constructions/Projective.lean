/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, pi
-/
module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Reindexing projective measure families

Pull back finite-dimensional laws along an embedding of coordinate labels, for dependent
measurable fibers. Projectivity and finiteness are preserved. The projective-limit
characterization states the marginals on the original labels, so that native
`MeasureTheory.IsProjectiveLimit.unique` applies to the reindexed family.
-/

public section

noncomputable section

open Finset MeasureTheory

namespace Function.Embedding

universe u v

variable {ι : Type u} {κ : Type v} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- Reindex a finite dependent product along an embedding of coordinate labels. -/
def finitePiCongrLeft (e : κ ↪ ι) (J : Finset κ) :
    (∀ j : J, X (e j)) ≃ᵐ (∀ i : J.map e, X i) :=
  MeasurableEquiv.piCongrLeft (fun i : J.map e ↦ X i) (J.equivMap e)

/-- Reindexing a finite product preserves the coordinate with its new label. -/
@[simp]
theorem finitePiCongrLeft_apply (e : κ ↪ ι) (J : Finset κ)
    (x : ∀ j : J, X (e j)) (j : J) :
    finitePiCongrLeft e J x (J.equivMap e j) = x j := by
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun i : J.map e ↦ X i) (J.equivMap e) x j

/-- The inverse reindexing evaluates at the embedded coordinate. -/
@[simp]
theorem finitePiCongrLeft_symm_apply (e : κ ↪ ι) (J : Finset κ)
    (x : ∀ i : J.map e, X i) (j : J) :
    (finitePiCongrLeft e J).symm x j = x (J.equivMap e j) := by
  exact Equiv.piCongrLeft_symm_apply (fun i : J.map e ↦ X i) (J.equivMap e) x j

/-- Pull back the finite-dimensional laws of a family along an embedding. -/
def reindexProjectiveFamily (e : κ ↪ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) (J : Finset κ) :
    Measure (∀ j : J, X (e j)) :=
  (P (J.map e)).map (finitePiCongrLeft e J).symm

/-- The reindexed law is the pullback of the law on the image coordinates. -/
theorem reindexProjectiveFamily_def (e : κ ↪ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) (J : Finset κ) :
    reindexProjectiveFamily e P J = (P (J.map e)).map (finitePiCongrLeft e J).symm := by
  rfl

instance reindexProjectiveFamily.instIsFiniteMeasure (e : κ ↪ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsFiniteMeasure (P I)]
    (J : Finset κ) : IsFiniteMeasure (reindexProjectiveFamily e P J) := by
  rw [reindexProjectiveFamily_def]
  infer_instance

instance reindexProjectiveFamily.instIsProbabilityMeasure (e : κ ↪ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (J : Finset κ) : IsProbabilityMeasure (reindexProjectiveFamily e P J) := by
  rw [reindexProjectiveFamily_def]
  infer_instance

/-- Pulling back the coordinate labels of a projective family preserves projectivity. -/
theorem isProjectiveMeasureFamily_reindex (e : κ ↪ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveMeasureFamily (α := fun j ↦ X (e j)) (reindexProjectiveFamily e P) := by
  intro I J hJI
  have hmapJI : J.map e ⊆ I.map e := Finset.map_subset_map.mpr hJI
  rw [reindexProjectiveFamily_def, reindexProjectiveFamily_def,
    hP (I.map e) (J.map e) hmapJI]
  rw [MeasureTheory.Measure.map_map (finitePiCongrLeft e J).symm.measurable
      (Finset.measurable_restrict₂ hmapJI)]
  have hfun :
      ((finitePiCongrLeft e J).symm ∘ Finset.restrict₂ hmapJI :
        (∀ i : I.map e, X i) → (∀ j : J, X (e j))) =
      Finset.restrict₂ (π := fun i ↦ X (e i)) hJI ∘
        (finitePiCongrLeft e I).symm := by
    funext x j
    simp only [Function.comp_apply, Finset.restrict₂_def, finitePiCongrLeft_symm_apply]
    congr 1
  rw [hfun]
  exact (MeasureTheory.Measure.map_map (Finset.measurable_restrict₂ hJI)
    (finitePiCongrLeft e I).symm.measurable).symm

/-- A reindexed family has a given projective limit exactly when its finite-dimensional
marginals, transported to the original labels, agree with the original family. -/
theorem isProjectiveLimit_reindex_iff (e : κ ↪ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) (μ : Measure (∀ j, X (e j))) :
    IsProjectiveLimit μ (reindexProjectiveFamily e P) ↔
      ∀ J : Finset κ, μ.map (finitePiCongrLeft e J ∘ J.restrict) = P (J.map e) := by
  constructor
  · intro hμ J
    rw [← MeasureTheory.Measure.map_map (finitePiCongrLeft e J).measurable
      (Finset.measurable_restrict J), hμ J, reindexProjectiveFamily_def]
    exact (finitePiCongrLeft e J).map_map_symm
  · intro hμ J
    have h := congrArg (fun ν ↦ ν.map (finitePiCongrLeft e J).symm) (hμ J)
    rw [← MeasureTheory.Measure.map_map (finitePiCongrLeft e J).measurable
      (Finset.measurable_restrict J), (finitePiCongrLeft e J).map_symm_map] at h
    exact h

end Function.Embedding
