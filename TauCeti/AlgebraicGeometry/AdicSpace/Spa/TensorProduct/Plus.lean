/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.RingTheory.Huber.TensorProduct.Plus

/-!
# Changing plus rings in completed tensor spectra

A continuous valuation on a completed tensor ring is bounded by one on the tensor plus ring
exactly when both its restrictions are bounded by one on the factor plus rings. Consequently,
changing the factor plus rings cuts out the intersection of the two corresponding inverse
images inside any given tensor spectrum. In particular this describes the inclusion on spectra
when the factor plus rings are enlarged. The comparison uses all continuous valuations,
regardless of rank, and requires neither sheafiness nor completeness of the input rings.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, §2.4,
  Definition 2.4.3 and (2.4.3.1).
-/

public section

namespace TauCeti.Huber.Pair.completedTensor

open ValuationSpectrum

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- A continuous point belongs to the completed tensor spectrum exactly when its two
restrictions belong to the factor spectra. -/
theorem mem_spa_iff (S : Pair B) (T : Pair C) {v : Spv (CompletedTensor A B C)}
    (hv : v.IsContinuous) :
    v ∈ spa (S.completedTensor A T).plus ↔
      comap (CompletedTensor.inl A B C) v ∈ spa S.plus ∧
        comap (CompletedTensor.inr A B C) v ∈ spa T.plus := by
  rw [plus_eq_closure_integralClosure, spa_topologicalClosure, spa_integralClosure, spa_sup]
  exact and_congr (mem_spa_map_iff (CompletedTensor.continuous_inl A B C) S.plus hv)
    (mem_spa_map_iff (CompletedTensor.continuous_inr A B C) T.plus hv)

/-- The locus obtained by changing the two factor plus rings is the intersection of their
inverse images under the tensor projections. For enlargements of plus rings this identifies
the smaller spectrum inside the original one; the equality itself needs no inclusions. -/
theorem spa_plus_eq_inter_preimage (S S' : Pair B) (T T' : Pair C) :
    (Subtype.val ⁻¹' spa (S'.completedTensor A T').plus : Set (spa (S.completedTensor A T).plus)) =
      (inl A S T).spaComap ⁻¹' (Subtype.val ⁻¹' spa S'.plus) ∩
        (inr A S T).spaComap ⁻¹' (Subtype.val ⁻¹' spa T'.plus) := by
  ext v
  simpa only [Set.mem_preimage, Set.mem_inter_iff, Hom.spaComap_val, toRingHom_inl,
    toRingHom_inr] using
    mem_spa_iff S' T' ((ValuationSpectrum.mem_spa_iff _ _).mp v.property).1

end TauCeti.Huber.Pair.completedTensor
