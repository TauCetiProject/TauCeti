/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.AdicRing.CompletedTensorProduct

/-!
# Changes of tensor ideals of definition

These examples replace the ideals of definition of the two factors by different positive powers.
The resulting comparison fixes pure tensors in both directions and is bicontinuous, even though
the two factors' exponents need not agree.
-/

open TensorProduct TauCeti TauCeti.AdicRing
open CompletedTensorProduct

variable (A B C : Type*) [CommRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B] [Algebra A B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [Algebra A C]

-- Raising the left ideal to the second power and the right ideal to the third power
-- leaves the image of every pure tensor unchanged.
example (b : B) (c : C) :
    idealEquiv A B C (IsAdicRing.ideal B ^ 2) (IsAdicRing.ideal C ^ 3)
        (is_ideal_adic_pow (IsAdicRing.ideal_spec B).2.1 (by decide))
        (is_ideal_adic_pow (IsAdicRing.ideal_spec C).2.1 (by decide))
        (IsAdicRing.ideal_spec B).1.pow (IsAdicRing.ideal_spec C).1.pow
        (inl A B C b * inr A B C c) =
      algebraMap (B ⊗[A] C) _ (b ⊗ₜ[A] c) := by
  rw [← algebraMap_tmul, AlgEquiv.commutes]

-- The inverse comparison recovers the same product of the two canonical inclusions.
example (b : B) (c : C) :
    (idealEquiv A B C (IsAdicRing.ideal B ^ 2) (IsAdicRing.ideal C ^ 3)
        (is_ideal_adic_pow (IsAdicRing.ideal_spec B).2.1 (by decide))
        (is_ideal_adic_pow (IsAdicRing.ideal_spec C).2.1 (by decide))
        (IsAdicRing.ideal_spec B).1.pow (IsAdicRing.ideal_spec C).1.pow).symm
        (algebraMap (B ⊗[A] C) _ (b ⊗ₜ[A] c)) =
      inl A B C b * inr A B C c := by
  rw [AlgEquiv.commutes, algebraMap_tmul]

-- The topological statement works directly from an importing module.
example :
    let L := (IsAdicRing.ideal B ^ 2).map
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] C) ⊔
      (IsAdicRing.ideal C ^ 3).map
        (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C)
    @IsHomeomorph _ _ _ (L.map (algebraMap (B ⊗[A] C) (AdicCompletion L (B ⊗[A] C)))).adicTopology
      (idealEquiv A B C (IsAdicRing.ideal B ^ 2) (IsAdicRing.ideal C ^ 3)
        (is_ideal_adic_pow (IsAdicRing.ideal_spec B).2.1 (by decide))
        (is_ideal_adic_pow (IsAdicRing.ideal_spec C).2.1 (by decide))
        (IsAdicRing.ideal_spec B).1.pow (IsAdicRing.ideal_spec C).1.pow) :=
  isHomeomorph_idealEquiv A B C _ _ _ _ _ _
