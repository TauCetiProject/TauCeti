/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Points
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.RingTheory.Huber.Padic.Field
import TauCeti.RingTheory.Huber.Prod

/-!
# Checks for point lifting to completed tensors

The split two-adic pair tests the order of both tensor projections: a lift of the first sheet
on the left and the second sheet on the right kills the left second idempotent but not the
right one. The same two points cannot lift over the split ring itself, because their base
points then differ. The identity check allows a valuation of arbitrary rank and an arbitrary
plus ring.
-/

public section

open TauCeti TauCeti.Huber TauCeti.ValuationSpectrum
open Algebra.TensorProduct

namespace TensorPointChecks

private noncomputable def basePoint : spa (Pair.powerBounded ℚ_[2]).plus :=
  Classical.choice <| Set.Nonempty.to_subtype <| Set.nonempty_iff_ne_empty.mpr <| by
    intro h
    exact not_subsingleton ℚ_[2] ((spa_eq_empty_iff_subsingleton _
      (Pair.powerBounded ℚ_[2]).isRingOfIntegralElements).mp h)

private noncomputable def firstPoint : Spv (ℚ_[2] × ℚ_[2]) :=
  comap (RingHom.fst _ _) basePoint.1

private noncomputable def secondPoint : Spv (ℚ_[2] × ℚ_[2]) :=
  comap (RingHom.snd _ _) basePoint.1

private theorem firstPoint_mem : firstPoint ∈ spa (Pair.powerBounded (ℚ_[2] × ℚ_[2])).plus := by
  rw [firstPoint, mem_spa_iff]
  refine ⟨((mem_spa_iff _ _).mp basePoint.2).1.comap continuous_fst, fun a ha ↦ ?_⟩
  rw [Pair.powerBounded_plus, powerBoundedSubring_prod] at ha
  rw [comap_vle, map_one]
  exact ((mem_spa_iff _ _).mp basePoint.2).2 a.1
    (by simpa only [Pair.powerBounded_plus, SetLike.mem_coe] using ha.1)

private theorem secondPoint_mem : secondPoint ∈ spa (Pair.powerBounded (ℚ_[2] × ℚ_[2])).plus := by
  rw [secondPoint, mem_spa_iff]
  refine ⟨((mem_spa_iff _ _).mp basePoint.2).1.comap continuous_snd, fun a ha ↦ ?_⟩
  rw [Pair.powerBounded_plus, powerBoundedSubring_prod] at ha
  rw [comap_vle, map_one]
  exact ((mem_spa_iff _ _).mp basePoint.2).2 a.2
    (by simpa only [Pair.powerBounded_plus, SetLike.mem_coe] using ha.2)

private theorem compatible : comap (algebraMap ℚ_[2] (ℚ_[2] × ℚ_[2])) firstPoint =
    comap (algebraMap ℚ_[2] (ℚ_[2] × ℚ_[2])) secondPoint := by
  simp only [firstPoint, secondPoint, comap_comap]
  congr 1

private instance : IsAdicHom (algebraMap ℚ_[2] (ℚ_[2] × ℚ_[2])) :=
  IsAdicHom.of_isTateRing (by fun_prop)

private theorem firstPoint_vle : firstPoint.toValuativeRel.vle (0, 1) 0 := by
  rw [firstPoint, comap_vle]
  exact basePoint.1.toValuativeRel.vle_refl 0

private theorem secondPoint_not_vle : ¬ secondPoint.toValuativeRel.vle (0, 1) 0 := by
  rw [secondPoint, comap_vle]
  exact basePoint.1.toValuativeRel.not_vle_one_zero

/-- The two ordered sheets give different values on the left and right second idempotents. -/
example : ∃ z : spa ((Pair.powerBounded (ℚ_[2] × ℚ_[2])).completedTensor ℚ_[2]
      (Pair.powerBounded (ℚ_[2] × ℚ_[2]))).plus,
    z.1.toValuativeRel.vle (CompletedTensor.inl ℚ_[2] _ _ (0, 1)) 0 ∧
      ¬ z.1.toValuativeRel.vle (CompletedTensor.inr ℚ_[2] _ _ (0, 1)) 0 := by
  obtain ⟨z, hz0, hz1⟩ := exists_spaPoint_completedTensor ℚ_[2] _ _
    ⟨firstPoint, firstPoint_mem⟩ ⟨secondPoint, secondPoint_mem⟩ compatible
  refine ⟨z, ?_, ?_⟩
  · have h : (comap (CompletedTensor.inl ℚ_[2] _ _) z.1).toValuativeRel.vle (0, 1) 0 :=
      hz0 ▸ firstPoint_vle
    simpa only [comap_vle, map_zero] using h
  · intro h
    have h' : (comap (CompletedTensor.inr ℚ_[2] _ _) z.1).toValuativeRel.vle (0, 1) 0 := by
      simpa only [comap_vle, map_zero] using h
    have heq := congrArg (fun p : Spv (ℚ_[2] × ℚ_[2]) ↦
      p.toValuativeRel.vle (0, 1) 0) hz1
    exact secondPoint_not_vle (Eq.mp heq h')

/-- Without agreement on the base, there need not be a lift, already for two identity maps. -/
example : ¬ ∃ z : Spv (ℚ_[2] × ℚ_[2]), z = firstPoint ∧ z = secondPoint := by
  rintro ⟨z, rfl, h⟩
  exact secondPoint_not_vle (h ▸ firstPoint_vle)

local instance {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsHuberRing A] : IsAdicHom (algebraMap A A) := by
  simpa using IsAdicHom.id (A := A)

/-- Identity tensors lift every point, without replacing a higher-rank point by a coarsening. -/
example {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
    (S : Pair A) (x : spa S.plus) :
    ∃ z : spa (S.completedTensor A S).plus,
      comap (CompletedTensor.inl A A A) z.1 = x.1 ∧
      comap (CompletedTensor.inr A A A) z.1 = x.1 :=
  exists_spaPoint_completedTensor A S S x x rfl

end TensorPointChecks
