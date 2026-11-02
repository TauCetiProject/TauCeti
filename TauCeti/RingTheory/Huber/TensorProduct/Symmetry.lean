/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Pair
public import Mathlib.Topology.Homeomorph.Defs

import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Symmetry of completed tensor products

Exchanging the factors of a completed tensor product gives a ring equivalence and a
homeomorphism. This equivalence exchanges the coprojections and identifies the plus rings of
the completed tensor pairs. It therefore compares the actual Huber pairs, including their
rings of integral elements, without completeness assumptions on the factors.

The construction uses the continuous universal property of the completed tensor product;
preservation of the plus rings uses its universal property for rings of integral elements.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, §1.2,
  proof of Proposition 1.2.2(1).
* S. Morel, *Adic spaces*, §II.3.2, Proposition II.3.2.1.
-/

public section

open TensorProduct Topology

namespace TauCeti.Huber

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

namespace CompletedTensor

private noncomputable def commHom : CompletedTensor A B C →+* CompletedTensor A C B :=
  lift (inr A C B) (inl A C B) (inl_comp_algebraMap A C B).symm
    (continuous_inr A C B) (continuous_inl A C B)

private theorem continuous_commHom : Continuous (commHom A B C) :=
  continuous_lift _ _ _ _ _

private theorem commHom_comp_commHom :
    (commHom A C B).comp (commHom A B C) = RingHom.id _ := by
  apply hom_ext (f := (commHom A C B).comp (commHom A B C))
    ((continuous_commHom A C B).comp (continuous_commHom A B C)) continuous_id
  · ext b
    simp [commHom]
  · ext c
    simp [commHom]

/-- Exchanging the two factors of the completed tensor product. -/
noncomputable def comm : CompletedTensor A B C ≃+* CompletedTensor A C B :=
  RingEquiv.ofRingHom (commHom A B C) (commHom A C B)
    (commHom_comp_commHom A C B) (commHom_comp_commHom A B C)

/-- The inverse exchange is the exchange with the factors interchanged. -/
theorem comm_symm : (comm A B C).symm = comm A C B := by
  ext x
  rfl

/-- Exchanging the factors is continuous. -/
@[fun_prop] theorem continuous_comm : Continuous (comm A B C) :=
  continuous_commHom A B C

/-- Exchanging the factors identifies their completed tensor topologies. -/
theorem isHomeomorph_comm : IsHomeomorph (comm A B C) :=
  (comm A B C).toEquiv.isHomeomorph_iff.mpr
    ⟨continuous_comm A B C, continuous_commHom A C B⟩

/-- Exchange sends the left coprojection to the right coprojection. -/
@[simp] theorem comm_inl (b : B) :
    comm A B C (inl A B C b) = inr A C B b := by
  simp [comm, commHom]

/-- Exchange sends the right coprojection to the left coprojection. -/
@[simp] theorem comm_inr (c : C) :
    comm A B C (inr A B C c) = inl A C B c := by
  simp [comm, commHom]

/-- Exchange sends the completed pure tensor `b ⊗ c` to `c ⊗ b`. -/
theorem comm_tmul (b : B) (c : C) :
    comm A B C (toCompletion A B C (b ⊗ₜ[A] c)) =
      toCompletion A C B (c ⊗ₜ[A] b) := by
  simp [mul_comm]

end CompletedTensor

namespace Pair.completedTensor

variable {B C} [IsHuberRing B] [IsHuberRing C] (S : Pair B) (T : Pair C)

private theorem comm_plus_le_comap :
    (S.completedTensor A T).plus ≤
      (T.completedTensor A S).plus.comap (CompletedTensor.comm A B C).toRingHom := by
  have := (T.completedTensor A S).isRingOfIntegralElements.isIntegrallyClosedIn
  exact S.completedTensor_plus_le_comap T
    ((T.completedTensor A S).plus.toAddSubgroup.isClosed_of_isOpen
      (T.completedTensor A S).isRingOfIntegralElements.isOpen)
    (CompletedTensor.continuous_comm A B C)
    (fun b hb ↦ by simpa using T.inr_mem_completedTensor_plus S hb)
    (fun c hc ↦ by simpa using T.inl_mem_completedTensor_plus S hc)

/-- Exchange preserves and reflects membership in the completed tensor plus ring. -/
@[simp] theorem comm_mem_plus (x : CompletedTensor A B C) :
    CompletedTensor.comm A B C x ∈ (T.completedTensor A S).plus ↔
      x ∈ (S.completedTensor A T).plus := by
  constructor
  · intro hx
    have h := comm_plus_le_comap A T S hx
    rw [← CompletedTensor.comm_symm] at h
    simpa using h
  · intro hx
    exact comm_plus_le_comap A S T hx

/-- Exchange carries the completed tensor plus ring exactly onto the exchanged plus ring. -/
theorem comm_plus :
    (S.completedTensor A T).plus.map (CompletedTensor.comm A B C).toRingHom =
      (T.completedTensor A S).plus := by
  ext x
  simpa only [RingEquiv.toRingHom_eq_coe, Subring.mem_map_equiv, CompletedTensor.comm_symm] using
    (comm_mem_plus A T S x)

end Pair.completedTensor

end TauCeti.Huber
