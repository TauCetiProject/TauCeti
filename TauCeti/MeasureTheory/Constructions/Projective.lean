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
def piFinsetMapMeasurableEquiv (e : κ ↪ ι) (J : Finset κ) :
    (∀ j : J, X (e j)) ≃ᵐ (∀ i : J.map e, X i) :=
  MeasurableEquiv.piCongrLeft (fun i : J.map e ↦ X i) (J.equivMap e)

/-- The finite-product reindexing is the measurable product equivalence on image labels. -/
theorem piFinsetMapMeasurableEquiv_def (e : κ ↪ ι) (J : Finset κ) :
    piFinsetMapMeasurableEquiv (X := X) e J =
      MeasurableEquiv.piCongrLeft (fun i : J.map e ↦ X i) (J.equivMap e) := (rfl)

/-- Evaluate finite-product reindexing at an arbitrary image coordinate, transporting the fiber. -/
theorem piFinsetMapMeasurableEquiv_apply (e : κ ↪ ι) (J : Finset κ)
    (x : ∀ j : J, X (e j)) (i : J.map e) :
    piFinsetMapMeasurableEquiv e J x i =
      (J.equivMap e).apply_symm_apply i ▸ x ((J.equivMap e).symm i) := by
  exact Equiv.piCongrLeft_apply (fun i : J.map e ↦ X i) (J.equivMap e) x i

/-- For constant fibers, evaluation of finite-product reindexing needs no transport. -/
theorem piFinsetMapMeasurableEquiv_apply_const {E : Type*} [MeasurableSpace E]
    (e : κ ↪ ι) (J : Finset κ) (x : J → E) (i : J.map e) :
    piFinsetMapMeasurableEquiv (X := fun _ ↦ E) e J x i = x ((J.equivMap e).symm i) := by
  simp only [piFinsetMapMeasurableEquiv_apply, eq_rec_constant]

/-- Reindexing a finite product preserves the coordinate with its new label. -/
@[simp, grind =]
theorem piFinsetMapMeasurableEquiv_apply_apply (e : κ ↪ ι) (J : Finset κ)
    (x : ∀ j : J, X (e j)) (j : J) :
    piFinsetMapMeasurableEquiv e J x (J.equivMap e j) = x j := by
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun i : J.map e ↦ X i) (J.equivMap e) x j

/-- The inverse reindexing evaluates at the embedded coordinate. -/
@[simp, grind =]
theorem piFinsetMapMeasurableEquiv_symm_apply (e : κ ↪ ι) (J : Finset κ)
    (x : ∀ i : J.map e, X i) (j : J) :
    (piFinsetMapMeasurableEquiv e J).symm x j = x (J.equivMap e j) := by
  exact Equiv.piCongrLeft_symm_apply (fun i : J.map e ↦ X i) (J.equivMap e) x j

/-- Pull back the finite-dimensional laws of a family along an embedding. -/
def reindexFamily (e : κ ↪ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) (J : Finset κ) :
    Measure (∀ j : J, X (e j)) :=
  (P (J.map e)).map (piFinsetMapMeasurableEquiv e J).symm

/-- The reindexed law is the pullback of the law on the image coordinates. -/
theorem reindexFamily_def (e : κ ↪ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) (J : Finset κ) :
    reindexFamily e P J = (P (J.map e)).map (piFinsetMapMeasurableEquiv e J).symm := (rfl)

/-- Transporting a reindexed law back to its original labels recovers the original law. -/
@[simp, grind =]
theorem map_piFinsetMapMeasurableEquiv_reindexFamily (e : κ ↪ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) (J : Finset κ) :
    (reindexFamily e P J).map (piFinsetMapMeasurableEquiv e J) = P (J.map e) := by
  rw [reindexFamily_def]
  exact (piFinsetMapMeasurableEquiv e J).map_map_symm

instance reindexFamily.instIsFiniteMeasure (e : κ ↪ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsFiniteMeasure (P I)]
    (J : Finset κ) : IsFiniteMeasure (reindexFamily e P J) := by
  rw [reindexFamily_def]
  infer_instance

instance reindexFamily.instIsProbabilityMeasure (e : κ ↪ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (J : Finset κ) : IsProbabilityMeasure (reindexFamily e P J) := by
  rw [reindexFamily_def]
  infer_instance

/-- Pulling back the coordinate labels of a projective family preserves projectivity. -/
theorem isProjectiveMeasureFamily_reindexFamily (e : κ ↪ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveMeasureFamily (α := fun j ↦ X (e j)) (reindexFamily e P) := by
  intro I J hJI
  have hmapJI : J.map e ⊆ I.map e := Finset.map_subset_map.mpr hJI
  rw [reindexFamily_def, reindexFamily_def, hP (I.map e) (J.map e) hmapJI]
  rw [MeasureTheory.Measure.map_map (piFinsetMapMeasurableEquiv e J).symm.measurable
      (Finset.measurable_restrict₂ hmapJI)]
  have hfun :
      ((piFinsetMapMeasurableEquiv e J).symm ∘ Finset.restrict₂ hmapJI :
        (∀ i : I.map e, X i) → (∀ j : J, X (e j))) =
      Finset.restrict₂ (π := fun i ↦ X (e i)) hJI ∘
        (piFinsetMapMeasurableEquiv e I).symm := by
    funext x j
    simp only [Function.comp_apply, Finset.restrict₂_def, piFinsetMapMeasurableEquiv_symm_apply]
    congr 1
  rw [hfun]
  exact (MeasureTheory.Measure.map_map (Finset.measurable_restrict₂ hJI)
    (piFinsetMapMeasurableEquiv e I).symm.measurable).symm

/-- A reindexed family has a given projective limit exactly when its finite-dimensional
marginals, transported to the original labels, agree with the original family. -/
theorem isProjectiveLimit_reindexFamily_iff (e : κ ↪ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) (μ : Measure (∀ j, X (e j))) :
    IsProjectiveLimit μ (reindexFamily e P) ↔
      ∀ J : Finset κ, μ.map (piFinsetMapMeasurableEquiv e J ∘ J.restrict) = P (J.map e) := by
  constructor
  · intro hμ J
    rw [← MeasureTheory.Measure.map_map (piFinsetMapMeasurableEquiv e J).measurable
      (Finset.measurable_restrict J), hμ J, map_piFinsetMapMeasurableEquiv_reindexFamily]
  · intro hμ J
    have h := congrArg (fun ν ↦ ν.map (piFinsetMapMeasurableEquiv e J).symm) (hμ J)
    rw [← MeasureTheory.Measure.map_map (piFinsetMapMeasurableEquiv e J).measurable
      (Finset.measurable_restrict J), (piFinsetMapMeasurableEquiv e J).map_symm_map] at h
    exact h

end Function.Embedding

namespace Set

open Function.Embedding

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- A law on a subtype is a projective limit of the restricted family exactly when its
marginals on finite sets contained in the subtype agree with the original family.

The explicit subtype embedding keeps dependent measurable-space instances reducible, so
`MeasureTheory.IsProjectiveLimit.unique` can infer finiteness of the reindexed laws. -/
theorem isProjectiveLimit_reindexFamily_iff (S : Set ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) (μ : Measure (∀ i : S, X i)) :
    IsProjectiveLimit μ ((⟨Subtype.val, Subtype.val_injective⟩ : S ↪ ι).reindexFamily P) ↔
      ∀ (I : Finset ι) (hI : (I : Set ι) ⊆ S),
        μ.map (fun x (i : I) ↦ x ⟨i.1, hI i.2⟩) = P I := by
  classical
  let e : S ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  have hcomm (J : Finset S) (hJ : (↑(J.map e) : Set ι) ⊆ S) :
      (piFinsetMapMeasurableEquiv (X := X) e J ∘ J.restrict) =
        (fun (x : ∀ i : S, X i) (i : J.map e) ↦ x ⟨i.1, hJ i.2⟩) := by
    funext x i
    obtain ⟨j, rfl⟩ := (J.equivMap e).surjective i
    rw [Function.comp_apply, piFinsetMapMeasurableEquiv_apply_apply]
    have hj : (⟨(J.equivMap e j).1, hJ (J.equivMap e j).2⟩ : S) = j.1 :=
      Subtype.ext (Finset.equivMap_apply_coe e J j)
    simp only [Finset.restrict_def]
    exact eq_of_heq (congr_arg_heq x hj.symm)
  constructor
  · intro hlimit I hI
    have hμ := (e.isProjectiveLimit_reindexFamily_iff P μ).mp hlimit
    let J := I.subtype (· ∈ S)
    have hmap : J.map e = I := Finset.subtype_map_of_mem (fun _ hi ↦ hI hi)
    have hPJ (hJ : (↑(J.map e) : Set ι) ⊆ S) :
        μ.map (fun x (i : J.map e) ↦ x ⟨i.1, hJ i.2⟩) = P (J.map e) := by
      rw [← hcomm J hJ]
      exact hμ J
    rw [hmap] at hPJ
    exact hPJ hI
  · intro hμ
    apply (e.isProjectiveLimit_reindexFamily_iff P μ).mpr
    intro J
    rw [hcomm J J.map_subtype_subset]
    exact hμ (J.map e) J.map_subtype_subset

end Set
