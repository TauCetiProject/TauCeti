/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Completion
public import Mathlib.Topology.Homeomorph.Defs

import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Associativity of completed tensor rings

The completed tensor product of Huber rings along adic structure maps is associative.
`TauCeti.Huber.CompletedTensor.assoc` is the ring equivalence preserving the three
coprojections, and `isHomeomorph_assoc` gives its topological compatibility. The input rings
need not be complete. The construction applies the continuous universal property of
`CompletedTensor.lift` twice in each direction; uniqueness identifies the composites.

## References

* S. Morel, *Adic spaces*, §II.3.2, Proposition II.3.2.1 (the completed tensor universal
  property, whose iterated application gives the associator).
-/

public section

open TensorProduct Topology

namespace TauCeti.Huber.CompletedTensor

variable (A B C D : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C] [IsTopologicalRing D]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  [IsAdicHom (algebraMap A D)]

private noncomputable def assocLeft :
    CompletedTensor A B C →+* CompletedTensor A B (CompletedTensor A C D) :=
  lift (inl A B (CompletedTensor A C D))
    ((inr A B (CompletedTensor A C D)).comp (inl A C D))
    (by ext a; simp) (continuous_inl _ _ _)
    ((continuous_inr _ _ _).comp (continuous_inl _ _ _))

private theorem continuous_assocLeft : Continuous (assocLeft A B C D) :=
  continuous_lift _ _ _ _ _

private noncomputable def assocHom :
    CompletedTensor A (CompletedTensor A B C) D →+*
      CompletedTensor A B (CompletedTensor A C D) :=
  lift (assocLeft A B C D)
    ((inr A B (CompletedTensor A C D)).comp (inr A C D))
    (by
      ext a
      simp only [RingHom.comp_apply]
      rw [algebraMap_eq_inl A B C, RingHom.comp_apply, assocLeft, lift_inl]
      simp)
    (continuous_assocLeft _ _ _ _)
    ((continuous_inr _ _ _).comp (continuous_inr _ _ _))

private theorem continuous_assocHom : Continuous (assocHom A B C D) :=
  continuous_lift _ _ _ _ _

private noncomputable def assocRight :
    CompletedTensor A C D →+* CompletedTensor A (CompletedTensor A B C) D :=
  lift ((inl A (CompletedTensor A B C) D).comp (inr A B C))
    (inr A (CompletedTensor A B C) D)
    (by ext a; simp) ((continuous_inl _ _ _).comp (continuous_inr _ _ _))
    (continuous_inr _ _ _)

private theorem continuous_assocRight : Continuous (assocRight A B C D) :=
  continuous_lift _ _ _ _ _

private noncomputable def assocInv :
    CompletedTensor A B (CompletedTensor A C D) →+*
      CompletedTensor A (CompletedTensor A B C) D :=
  lift ((inl A (CompletedTensor A B C) D).comp (inl A B C))
    (assocRight A B C D)
    (by
      ext a
      simp only [RingHom.comp_apply]
      rw [algebraMap_eq_inl A C D, RingHom.comp_apply, assocRight, lift_inl]
      simp)
    ((continuous_inl _ _ _).comp (continuous_inl _ _ _))
    (continuous_assocRight _ _ _ _)

private theorem continuous_assocInv : Continuous (assocInv A B C D) :=
  continuous_lift _ _ _ _ _

private theorem assocInv_comp_assocHom :
    (assocInv A B C D).comp (assocHom A B C D) = RingHom.id _ := by
  apply hom_ext (f := (assocInv A B C D).comp (assocHom A B C D))
    ((continuous_assocInv _ _ _ _).comp (continuous_assocHom _ _ _ _))
    continuous_id
  · apply hom_ext (f := ((assocInv A B C D).comp (assocHom A B C D)).comp
        (inl A (CompletedTensor A B C) D))
      (((continuous_assocInv _ _ _ _).comp (continuous_assocHom _ _ _ _)).comp
        (continuous_inl _ _ _)) (continuous_inl _ _ _)
    · ext b
      simp [assocHom, assocInv, assocLeft]
    · ext c
      simp [assocHom, assocInv, assocLeft, assocRight]
  · ext d
    simp [assocHom, assocInv, assocRight]

private theorem assocHom_comp_assocInv :
    (assocHom A B C D).comp (assocInv A B C D) = RingHom.id _ := by
  apply hom_ext (f := (assocHom A B C D).comp (assocInv A B C D))
    ((continuous_assocHom _ _ _ _).comp (continuous_assocInv _ _ _ _))
    continuous_id
  · ext b
    simp [assocHom, assocInv, assocLeft]
  · apply hom_ext (f := ((assocHom A B C D).comp (assocInv A B C D)).comp
        (inr A B (CompletedTensor A C D)))
      (((continuous_assocHom _ _ _ _).comp (continuous_assocInv _ _ _ _)).comp
        (continuous_inr _ _ _)) (continuous_inr _ _ _)
    · ext c
      simp [assocHom, assocInv, assocLeft, assocRight]
    · ext d
      simp [assocHom, assocInv, assocRight]

/-- The completed tensor associator preserves the order of the three factors. -/
noncomputable def assoc :
    CompletedTensor A (CompletedTensor A B C) D ≃+*
      CompletedTensor A B (CompletedTensor A C D) :=
  RingEquiv.ofRingHom (assocHom A B C D) (assocInv A B C D)
    (assocHom_comp_assocInv A B C D) (assocInv_comp_assocHom A B C D)

/-- The associator is continuous. -/
@[fun_prop] theorem continuous_assoc : Continuous (assoc A B C D) :=
  continuous_assocHom A B C D

/-- The inverse associator is continuous. -/
@[fun_prop] theorem continuous_assoc_symm : Continuous (assoc A B C D).symm :=
  continuous_assocInv A B C D

/-- Associativity identifies the topologies of the two iterated completed tensors. -/
theorem isHomeomorph_assoc : IsHomeomorph (assoc A B C D) :=
  (assoc A B C D).toEquiv.isHomeomorph_iff.mpr
    ⟨continuous_assoc A B C D, continuous_assoc_symm A B C D⟩

/-- The associator preserves the first coprojection. -/
@[simp] theorem assoc_inl_inl (b : B) :
    assoc A B C D (inl A (CompletedTensor A B C) D (inl A B C b)) =
      inl A B (CompletedTensor A C D) b := by
  simp [assoc, assocHom, assocLeft]

/-- The associator preserves the middle coprojection. -/
@[simp] theorem assoc_inl_inr (c : C) :
    assoc A B C D (inl A (CompletedTensor A B C) D (inr A B C c)) =
      inr A B (CompletedTensor A C D) (inl A C D c) := by
  simp [assoc, assocHom, assocLeft]

/-- The associator preserves the last coprojection. -/
@[simp] theorem assoc_inr (d : D) :
    assoc A B C D (inr A (CompletedTensor A B C) D d) =
      inr A B (CompletedTensor A C D) (inr A C D d) := by
  simp [assoc, assocHom]

/-- The inverse associator preserves the first coprojection. -/
@[simp] theorem assoc_symm_inl (b : B) :
    (assoc A B C D).symm (inl A B (CompletedTensor A C D) b) =
      inl A (CompletedTensor A B C) D (inl A B C b) := by
  simp [assoc, assocInv]

/-- The inverse associator preserves the middle coprojection. -/
@[simp] theorem assoc_symm_inr_inl (c : C) :
    (assoc A B C D).symm (inr A B (CompletedTensor A C D) (inl A C D c)) =
      inl A (CompletedTensor A B C) D (inr A B C c) := by
  simp [assoc, assocInv, assocRight]

/-- The inverse associator preserves the last coprojection. -/
@[simp] theorem assoc_symm_inr_inr (d : D) :
    (assoc A B C D).symm (inr A B (CompletedTensor A C D) (inr A C D d)) =
      inr A (CompletedTensor A B C) D d := by
  simp [assoc, assocInv, assocRight]

/-- On pure tensors the associator sends `(b ⊗ c) ⊗ d` to `b ⊗ (c ⊗ d)`. -/
theorem assoc_tmul (b : B) (c : C) (d : D) :
    assoc A B C D
      (toCompletion A (CompletedTensor A B C) D
        (toCompletion A B C (b ⊗ₜ[A] c) ⊗ₜ[A] d)) =
      toCompletion A B (CompletedTensor A C D)
        (b ⊗ₜ[A] toCompletion A C D (c ⊗ₜ[A] d)) := by
  simp [mul_assoc]

/-- On pure tensors the inverse sends `b ⊗ (c ⊗ d)` to `(b ⊗ c) ⊗ d`. -/
theorem assoc_symm_tmul (b : B) (c : C) (d : D) :
    (assoc A B C D).symm
      (toCompletion A B (CompletedTensor A C D)
        (b ⊗ₜ[A] toCompletion A C D (c ⊗ₜ[A] d))) =
      toCompletion A (CompletedTensor A B C) D
        (toCompletion A B C (b ⊗ₜ[A] c) ⊗ₜ[A] d) := by
  simp [mul_assoc]

end TauCeti.Huber.CompletedTensor
