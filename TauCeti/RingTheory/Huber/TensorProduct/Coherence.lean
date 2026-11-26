/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Associator
public import TauCeti.RingTheory.Huber.TensorProduct.Pair

/-!
# Integral elements and completed tensor associativity

The completed tensor ring associator identifies the plus rings of the two iterated
completed tensor products of Huber pairs. Thus reassociating affinoid tensor charts preserves
not only their topological rings but also their rings of integral elements. No completeness
of the input rings, sheafiness, or uniformity is required.

The argument uses the universal property of the completed tensor plus ring twice in each
direction: each of the three original plus rings maps into the target plus ring.

## References

* S. Morel, *Adic spaces*, §II.3.2, Proposition II.3.2.1 (the completed tensor universal
  property).
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, proof of Lemma 3.9(i) (the integral-element subring of the completed tensor).
-/

public section

namespace TauCeti.Huber.Pair.completedTensor

variable (A : Type*) {B C D : Type*}
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C] [IsTopologicalRing D]
  [IsHuberRing B] [IsHuberRing C] [IsHuberRing D]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  [IsAdicHom (algebraMap A D)]
  (S : Pair B) (T : Pair C) (U : Pair D)

private theorem assoc_plus_le :
    ((S.completedTensor A T).completedTensor A U).plus ≤
      (S.completedTensor A (T.completedTensor A U)).plus.comap
        (CompletedTensor.assoc A B C D).toRingHom := by
  let V := S.completedTensor A (T.completedTensor A U)
  let := V.isRingOfIntegralElements.isIntegrallyClosedIn
  have hclosed := V.plus.toAddSubgroup.isClosed_of_isOpen V.isRingOfIntegralElements.isOpen
  apply completedTensor_plus_le_comap (A := A) _ _ hclosed
    (f := (CompletedTensor.assoc A B C D).toRingHom)
    (CompletedTensor.continuous_assoc A B C D)
  · apply S.completedTensor_plus_le_comap (A := A) T hclosed
      (f := (CompletedTensor.assoc A B C D).toRingHom.comp
        (CompletedTensor.inl A (CompletedTensor A B C) D))
      ((CompletedTensor.continuous_assoc A B C D).comp
        (CompletedTensor.continuous_inl A (CompletedTensor A B C) D))
    · intro b hb
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        CompletedTensor.assoc_inl_inl]
      exact S.inl_mem_completedTensor_plus (A := A) (T.completedTensor A U) hb
    · intro c hc
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        CompletedTensor.assoc_inl_inr]
      exact S.inr_mem_completedTensor_plus (A := A) (T.completedTensor A U)
        (T.inl_mem_completedTensor_plus (A := A) U hc)
  · intro d hd
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, CompletedTensor.assoc_inr]
    exact S.inr_mem_completedTensor_plus (A := A) (T.completedTensor A U)
      (T.inr_mem_completedTensor_plus (A := A) U hd)

private theorem assoc_symm_plus_le :
    (S.completedTensor A (T.completedTensor A U)).plus ≤
      ((S.completedTensor A T).completedTensor A U).plus.comap
        (CompletedTensor.assoc A B C D).symm.toRingHom := by
  let V := (S.completedTensor A T).completedTensor A U
  let := V.isRingOfIntegralElements.isIntegrallyClosedIn
  have hclosed := V.plus.toAddSubgroup.isClosed_of_isOpen V.isRingOfIntegralElements.isOpen
  apply completedTensor_plus_le_comap (A := A) _ _ hclosed
    (f := (CompletedTensor.assoc A B C D).symm.toRingHom)
    (CompletedTensor.continuous_assoc_symm A B C D)
  · intro b hb
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      CompletedTensor.assoc_symm_inl]
    exact (S.completedTensor A T).inl_mem_completedTensor_plus (A := A) U
      (S.inl_mem_completedTensor_plus (A := A) T hb)
  · apply T.completedTensor_plus_le_comap (A := A) U hclosed
      (f := (CompletedTensor.assoc A B C D).symm.toRingHom.comp
        (CompletedTensor.inr A B (CompletedTensor A C D)))
      ((CompletedTensor.continuous_assoc_symm A B C D).comp
        (CompletedTensor.continuous_inr A B (CompletedTensor A C D)))
    · intro c hc
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        CompletedTensor.assoc_symm_inr_inl]
      exact (S.completedTensor A T).inl_mem_completedTensor_plus (A := A) U
        (S.inr_mem_completedTensor_plus (A := A) T hc)
    · intro d hd
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        CompletedTensor.assoc_symm_inr_inr]
      exact (S.completedTensor A T).inr_mem_completedTensor_plus (A := A) U hd

/-- Reassociation preserves and reflects membership in the plus ring of an iterated completed
tensor product. -/
@[simp]
theorem assoc_mem_plus_iff (x : CompletedTensor A (CompletedTensor A B C) D) :
    CompletedTensor.assoc A B C D x ∈ (S.completedTensor A (T.completedTensor A U)).plus ↔
      x ∈ ((S.completedTensor A T).completedTensor A U).plus := by
  constructor
  · intro hx
    simpa using assoc_symm_plus_le A S T U hx
  · intro hx
    exact assoc_plus_le A S T U hx

/-- The completed tensor associator transports the entire plus subring, not merely the images
of the three factor plus rings. -/
@[simp]
theorem assoc_plus :
    (((S.completedTensor A T).completedTensor A U).plus.map
      (CompletedTensor.assoc A B C D : _ →+* _)) =
        (S.completedTensor A (T.completedTensor A U)).plus := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (assoc_mem_plus_iff A S T U y).mpr hy
  · intro hx
    refine ⟨(CompletedTensor.assoc A B C D).symm x, ?_, by simp⟩
    exact assoc_symm_plus_le A S T U hx

/-- The completed tensor associator `(B ⊗̂ C) ⊗̂ D → B ⊗̂ (C ⊗̂ D)` as a morphism of Huber pairs. -/
noncomputable def assocHom :
    Hom ((S.completedTensor A T).completedTensor A U)
      (S.completedTensor A (T.completedTensor A U)) where
  toRingHom := (CompletedTensor.assoc A B C D).toRingHom
  continuous_toRingHom := CompletedTensor.continuous_assoc A B C D
  map_mem_plus _ hx := (assoc_mem_plus_iff A S T U _).mpr hx

/-- The inverse completed tensor associator `B ⊗̂ (C ⊗̂ D) → (B ⊗̂ C) ⊗̂ D` as a morphism of Huber
pairs. -/
noncomputable def assocSymmHom :
    Hom (S.completedTensor A (T.completedTensor A U))
      ((S.completedTensor A T).completedTensor A U) where
  toRingHom := (CompletedTensor.assoc A B C D).symm.toRingHom
  continuous_toRingHom := CompletedTensor.continuous_assoc_symm A B C D
  map_mem_plus _ hx := assoc_symm_plus_le A S T U hx

/-- The underlying ring map of `assocHom` is the completed tensor associator. -/
@[simp]
theorem toRingHom_assocHom :
    (assocHom A S T U).toRingHom = (CompletedTensor.assoc A B C D).toRingHom := (rfl)

/-- The underlying ring map of `assocSymmHom` is the inverse completed tensor associator. -/
@[simp]
theorem toRingHom_assocSymmHom :
    (assocSymmHom A S T U).toRingHom = (CompletedTensor.assoc A B C D).symm.toRingHom := (rfl)

/-- The inverse pair associator is a left inverse of the pair associator. -/
@[simp]
theorem assocSymmHom_comp_assocHom :
    (assocSymmHom A S T U).comp (assocHom A S T U) =
      Hom.id ((S.completedTensor A T).completedTensor A U) := by
  ext x
  simp [Hom.toRingHom_comp]

/-- The inverse pair associator is a right inverse of the pair associator. -/
@[simp]
theorem assocHom_comp_assocSymmHom :
    (assocHom A S T U).comp (assocSymmHom A S T U) =
      Hom.id (S.completedTensor A (T.completedTensor A U)) := by
  ext x
  simp [Hom.toRingHom_comp]

/-- The inverse pair associator preserves the first coprojection. -/
@[simp]
theorem assocSymmHom_comp_inl :
    (assocSymmHom A S T U).comp (inl A S (T.completedTensor A U)) =
      (inl A (S.completedTensor A T) U).comp (inl A S T) := by
  ext b
  simp [Hom.toRingHom_comp]

/-- The inverse pair associator preserves the middle coprojection. -/
@[simp]
theorem assocSymmHom_comp_inr_comp_inl :
    (assocSymmHom A S T U).comp ((inr A S (T.completedTensor A U)).comp (inl A T U)) =
      (inl A (S.completedTensor A T) U).comp (inr A S T) := by
  ext c
  simp [Hom.toRingHom_comp]

/-- The inverse pair associator preserves the last coprojection. -/
@[simp]
theorem assocSymmHom_comp_inr_comp_inr :
    (assocSymmHom A S T U).comp ((inr A S (T.completedTensor A U)).comp (inr A T U)) =
      inr A (S.completedTensor A T) U := by
  ext d
  simp [Hom.toRingHom_comp]

end TauCeti.Huber.Pair.completedTensor
