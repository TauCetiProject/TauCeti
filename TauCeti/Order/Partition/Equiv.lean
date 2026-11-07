/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Partition.Equipartition
public import TauCeti.Order.Partition.Finpartition

/-!
# Transporting finite partitions along equivalences

Pulling a partition back along an equivalence identifies its cells with the inverse images
of the original cells. This identification preserves cell sizes and hence equitability.
The cell bijection is useful when transporting quantitative comparisons between partitions.
-/

public section

open Finset

namespace Finpartition

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Pulling a partition back by an equivalence preserves and reflects equitability. -/
@[simp]
theorem isEquipartition_comap_equiv_iff (P : Finpartition (univ : Finset W))
    (σ : V ≃ W) :
    ((P.copy (image_univ_equiv σ).symm).comap σ).IsEquipartition ↔ P.IsEquipartition := by
  constructor
  · intro h A B hA hB
    have hA' : A.map σ.symm.toEmbedding ∈
        ((P.copy (image_univ_equiv σ).symm).comap σ).parts := by
      rw [parts_comap_copy_equiv]
      exact mem_image_of_mem _ hA
    have hB' : B.map σ.symm.toEmbedding ∈
        ((P.copy (image_univ_equiv σ).symm).comap σ).parts := by
      rw [parts_comap_copy_equiv]
      exact mem_image_of_mem _ hB
    simpa using h hA' hB'
  · intro h A B hA hB
    rw [parts_comap_copy_equiv] at hA hB
    obtain ⟨A₀, hA₀, rfl⟩ := mem_image.1 hA
    obtain ⟨B₀, hB₀, rfl⟩ := mem_image.1 hB
    simpa using h hA₀ hB₀

/-- The cells of a partition pulled back by an equivalence are canonically in bijection with
the original cells, by taking inverse images. -/
noncomputable def partsComapEquiv (P : Finpartition (univ : Finset W)) (σ : V ≃ W) :
    P.parts ≃ ((P.copy (image_univ_equiv σ).symm).comap σ).parts :=
  (Equiv.finsetCongr σ.symm).subtypeEquiv (fun A ↦ by
    rw [parts_comap_copy_equiv]
    simp only [Equiv.finsetCongr_apply, mem_image, map_inj]
    exact ⟨fun hA ↦ ⟨A, hA, rfl⟩, fun ⟨B, hB, hBA⟩ ↦ hBA ▸ hB⟩)

@[simp]
theorem partsComapEquiv_apply_coe (P : Finpartition (univ : Finset W)) (σ : V ≃ W)
    (A : P.parts) : (P.partsComapEquiv σ A).1 = A.1.map σ.symm.toEmbedding := (rfl)

@[simp]
theorem partsComapEquiv_symm_apply_coe (P : Finpartition (univ : Finset W)) (σ : V ≃ W)
    (B : ((P.copy (image_univ_equiv σ).symm).comap σ).parts) :
    ((P.partsComapEquiv σ).symm B).1 = B.1.map σ.toEmbedding := by
  have h := congrArg (fun A ↦ A.1.map σ.toEmbedding)
    ((P.partsComapEquiv σ).apply_symm_apply B)
  rw [partsComapEquiv_apply_coe, map_map] at h
  simpa using h

end Finpartition
