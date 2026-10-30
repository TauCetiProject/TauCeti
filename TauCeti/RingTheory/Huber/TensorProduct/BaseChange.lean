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
# Transitivity of completed base change

For adic structure maps and a compatible tower `A → C → D`, successive completed base
change from `A` to `C` and then to `D` agrees with completed base change directly to `D`.
The comparison is a homeomorphic ring equivalence, preserves the coprojections, and
identifies the completed tensor plus rings when `C → D` preserves the chosen rings of
integral elements. The rings need not be complete, uniform or sheafy.

`CompletedTensor.rightAlgebra` equips `B ⊗̂_A C` with its `C`-algebra structure. It is not a
global instance, to avoid conflicting with the existing base algebra structure.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, §1.2,
  proof of Proposition 1.2.2(1) (the completed cocartesian construction).
* S. Morel, *Adic spaces*, §II.3.2, Proposition II.3.2.1 (the universal property).
-/

public section

open TensorProduct Topology

namespace TauCeti.Huber.CompletedTensor

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

attribute [local instance] rightAlgebra isAdicHom_rightAlgebra

variable (D : Type*) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower A C D]
  [TopologicalSpace D] [IsTopologicalRing D]
  [IsAdicHom (algebraMap C D)]

omit [Algebra A D] [IsScalarTower A C D] in
private theorem inl_inr_eq_inr_algebraMap (c : C) :
    inl C (CompletedTensor A B C) D (inr A B C c) =
      inr C (CompletedTensor A B C) D (algebraMap C D c) := by
  simpa only [algebraMap_rightAlgebra, inr_algebraMap] using
    (inl_algebraMap C (CompletedTensor A B C) D c)

section Construction

variable [IsAdicHom (algebraMap A D)]

private noncomputable def baseChangeLeft :
    CompletedTensor A B C →+* CompletedTensor A B D :=
  lift (inl A B D) ((inr A B D).comp (algebraMap C D))
    (by ext a; simp [IsScalarTower.algebraMap_apply A C D])
    (continuous_inl _ _ _) ((continuous_inr _ _ _).comp (IsAdicHom.continuous inferInstance))

private theorem continuous_baseChangeLeft : Continuous (baseChangeLeft A B C D) :=
  continuous_lift _ _ _ _ _

private noncomputable def baseChangeHom :
    CompletedTensor C (CompletedTensor A B C) D →+* CompletedTensor A B D :=
  lift (baseChangeLeft A B C D) (inr A B D)
    (by ext c; simp [baseChangeLeft])
    (continuous_baseChangeLeft _ _ _ _) (continuous_inr _ _ _)

private theorem continuous_baseChangeHom : Continuous (baseChangeHom A B C D) :=
  continuous_lift _ _ _ _ _

private noncomputable def baseChangeInv :
    CompletedTensor A B D →+* CompletedTensor C (CompletedTensor A B C) D :=
  lift ((inl C (CompletedTensor A B C) D).comp (inl A B C))
    (inr C (CompletedTensor A B C) D)
    (by
      ext a
      simpa only [RingHom.comp_apply, inl_algebraMap A B C, inr_algebraMap A B C,
        ← IsScalarTower.algebraMap_apply A C D] using
        (inl_inr_eq_inr_algebraMap A B C D (algebraMap A C a)))
    ((continuous_inl _ _ _).comp (continuous_inl _ _ _)) (continuous_inr _ _ _)

private theorem continuous_baseChangeInv : Continuous (baseChangeInv A B C D) :=
  continuous_lift _ _ _ _ _

private theorem baseChangeInv_comp_baseChangeHom :
    (baseChangeInv A B C D).comp (baseChangeHom A B C D) = RingHom.id _ := by
  apply hom_ext (f := (baseChangeInv A B C D).comp (baseChangeHom A B C D))
    ((continuous_baseChangeInv _ _ _ _).comp
      (continuous_baseChangeHom _ _ _ _)) continuous_id
  · apply hom_ext (f := ((baseChangeInv A B C D).comp (baseChangeHom A B C D)).comp
        (inl C (CompletedTensor A B C) D))
      (((continuous_baseChangeInv _ _ _ _).comp (continuous_baseChangeHom _ _ _ _)).comp
        (continuous_inl _ _ _)) (continuous_inl _ _ _)
    · ext b
      simp [baseChangeHom, baseChangeLeft, baseChangeInv]
    · ext c
      simp only [RingHom.comp_apply, baseChangeHom, lift_inl, baseChangeLeft, lift_inr,
        baseChangeInv]
      exact (inl_inr_eq_inr_algebraMap A B C D c).symm
  · ext d
    simp [baseChangeHom, baseChangeInv]

private theorem baseChangeHom_comp_baseChangeInv :
    (baseChangeHom A B C D).comp (baseChangeInv A B C D) = RingHom.id _ := by
  apply hom_ext (f := (baseChangeHom A B C D).comp (baseChangeInv A B C D))
    ((continuous_baseChangeHom _ _ _ _).comp
      (continuous_baseChangeInv _ _ _ _)) continuous_id
  · ext b
    simp [baseChangeHom, baseChangeLeft, baseChangeInv]
  · ext d
    simp [baseChangeHom, baseChangeInv]

end Construction

/-- Transitivity of completed base change: `(B ⊗̂_A C) ⊗̂_C D ≃ B ⊗̂_A D`.
The intermediate `C`-algebra structure is `CompletedTensor.rightAlgebra`. -/
noncomputable def cancelBaseChange :
    let _ : IsAdicHom (algebraMap A D) := by
      rw [IsScalarTower.algebraMap_eq A C D]
      exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
    CompletedTensor C (CompletedTensor A B C) D ≃+* CompletedTensor A B D := by
  intro hAD
  exact RingEquiv.ofRingHom (baseChangeHom A B C D) (baseChangeInv A B C D)
    (baseChangeHom_comp_baseChangeInv A B C D) (baseChangeInv_comp_baseChangeHom A B C D)

/-- Completed base-change cancellation is continuous. -/
@[fun_prop] theorem continuous_cancelBaseChange : Continuous (cancelBaseChange A B C D) := by
  have : IsAdicHom (algebraMap A D) := by
    rw [IsScalarTower.algebraMap_eq A C D]
    exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
  exact continuous_baseChangeHom A B C D

/-- The inverse completed base-change comparison is continuous. -/
@[fun_prop] theorem continuous_cancelBaseChange_symm :
    Continuous (cancelBaseChange A B C D).symm := by
  have : IsAdicHom (algebraMap A D) := by
    rw [IsScalarTower.algebraMap_eq A C D]
    exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
  exact continuous_baseChangeInv A B C D

/-- Successive and direct completed base change have the same topology. -/
theorem isHomeomorph_cancelBaseChange : IsHomeomorph (cancelBaseChange A B C D) :=
  (cancelBaseChange A B C D).toEquiv.isHomeomorph_iff.mpr
    ⟨continuous_cancelBaseChange A B C D, continuous_cancelBaseChange_symm A B C D⟩

/-- Cancellation preserves the coprojection from `B`. -/
@[simp] theorem cancelBaseChange_inl_inl (b : B) :
    let _ : IsAdicHom (algebraMap A D) := by
      rw [IsScalarTower.algebraMap_eq A C D]
      exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
    cancelBaseChange A B C D (inl C (CompletedTensor A B C) D (inl A B C b)) =
      inl A B D b := by
  intro hAD
  simp [cancelBaseChange, baseChangeHom, baseChangeLeft]

/-- Cancellation carries the intermediate scalar to its image in `D`. -/
@[simp] theorem cancelBaseChange_inl_inr (c : C) :
    let _ : IsAdicHom (algebraMap A D) := by
      rw [IsScalarTower.algebraMap_eq A C D]
      exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
    cancelBaseChange A B C D (inl C (CompletedTensor A B C) D (inr A B C c)) =
      inr A B D (algebraMap C D c) := by
  intro hAD
  simp [cancelBaseChange, baseChangeHom, baseChangeLeft]

/-- Cancellation preserves the coprojection from `D`. -/
@[simp] theorem cancelBaseChange_inr (d : D) :
    let _ : IsAdicHom (algebraMap A D) := by
      rw [IsScalarTower.algebraMap_eq A C D]
      exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
    cancelBaseChange A B C D (inr C (CompletedTensor A B C) D d) = inr A B D d := by
  intro hAD
  simp [cancelBaseChange, baseChangeHom]

/-- Inverse cancellation includes `B` through the two left coprojections. -/
@[simp] theorem cancelBaseChange_symm_inl (b : B) :
    let _ : IsAdicHom (algebraMap A D) := by
      rw [IsScalarTower.algebraMap_eq A C D]
      exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
    (cancelBaseChange A B C D).symm (inl A B D b) =
      inl C (CompletedTensor A B C) D (inl A B C b) := by
  intro hAD
  simp [cancelBaseChange, baseChangeInv]

/-- Inverse cancellation preserves the coprojection from `D`. -/
@[simp] theorem cancelBaseChange_symm_inr (d : D) :
    let _ : IsAdicHom (algebraMap A D) := by
      rw [IsScalarTower.algebraMap_eq A C D]
      exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
    (cancelBaseChange A B C D).symm (inr A B D d) = inr C (CompletedTensor A B C) D d := by
  intro hAD
  simp [cancelBaseChange, baseChangeInv]

/-- Cancellation sends `(b ⊗ c) ⊗ d` to `b ⊗ (g(c)d)`. -/
theorem cancelBaseChange_tmul (b : B) (c : C) (d : D) :
    let _ : IsAdicHom (algebraMap A D) := by
      rw [IsScalarTower.algebraMap_eq A C D]
      exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
    cancelBaseChange A B C D
      (toCompletion C (CompletedTensor A B C) D
        (toCompletion A B C (b ⊗ₜ[A] c) ⊗ₜ[C] d)) =
      toCompletion A B D (b ⊗ₜ[A] (algebraMap C D c * d)) := by
  intro hAD
  simp [mul_assoc]

/-- Inverse cancellation sends `b ⊗ d` to `(b ⊗ 1) ⊗ d`. -/
theorem cancelBaseChange_symm_tmul (b : B) (d : D) :
    let _ : IsAdicHom (algebraMap A D) := by
      rw [IsScalarTower.algebraMap_eq A C D]
      exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
    (cancelBaseChange A B C D).symm (toCompletion A B D (b ⊗ₜ[A] d)) =
      toCompletion C (CompletedTensor A B C) D
        (toCompletion A B C (b ⊗ₜ[A] (1 : C)) ⊗ₜ[C] d) := by
  intro hAD
  simp

end TauCeti.Huber.CompletedTensor

namespace TauCeti.Huber.Pair.completedTensor

open CompletedTensor

variable (A B C D : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D] [Algebra C D] [IsScalarTower A C D]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C] [IsTopologicalRing D]
  [IsHuberRing B] [IsHuberRing C] [IsHuberRing D]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  [IsAdicHom (algebraMap C D)]

attribute [local instance] CompletedTensor.rightAlgebra CompletedTensor.isAdicHom_rightAlgebra

/-- Transitivity of completed base change identifies the actual tensor plus rings, provided
`C → D` preserves the chosen rings of integral elements. No maximality of the plus rings
is required. -/
theorem cancelBaseChange_plus (S : Pair B) (T : Pair C) (U : Pair D)
    (hCD : T.plus ≤ U.plus.comap (algebraMap C D)) :
    let _ : IsAdicHom (algebraMap A D) := by
      rw [IsScalarTower.algebraMap_eq A C D]
      exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
    (((S.completedTensor A T).completedTensor C U).plus.map
      (CompletedTensor.cancelBaseChange A B C D).toRingHom) = (S.completedTensor A U).plus := by
  intro hAD
  let V := (S.completedTensor A T).completedTensor C U
  let W := S.completedTensor A U
  have hV := V.isRingOfIntegralElements
  have hW := W.isRingOfIntegralElements
  have := hV.isIntegrallyClosedIn
  have := hW.isIntegrallyClosedIn
  have hf : V.plus ≤ W.plus.comap (CompletedTensor.cancelBaseChange A B C D).toRingHom := by
    apply (S.completedTensor A T).completedTensor_plus_le_comap (A := C) U
      (f := (CompletedTensor.cancelBaseChange A B C D).toRingHom)
      (W.plus.toAddSubgroup.isClosed_of_isOpen hW.isOpen) (continuous_cancelBaseChange A B C D)
    · intro x hx
      apply S.completedTensor_plus_le_comap T
        (f := (CompletedTensor.cancelBaseChange A B C D).toRingHom.comp
          (CompletedTensor.inl C (CompletedTensor A B C) D))
        (W.plus.toAddSubgroup.isClosed_of_isOpen hW.isOpen)
        ((continuous_cancelBaseChange A B C D).comp (continuous_inl _ _ _))
        (fun b hb ↦ ?_) (fun c hc ↦ ?_) hx
      · simpa using S.inl_mem_completedTensor_plus U hb
      · simpa using S.inr_mem_completedTensor_plus U (hCD hc)
    · intro d hd
      simpa using S.inr_mem_completedTensor_plus U hd
  have hg : W.plus ≤ V.plus.comap (CompletedTensor.cancelBaseChange A B C D).symm.toRingHom := by
    apply S.completedTensor_plus_le_comap U
      (f := (CompletedTensor.cancelBaseChange A B C D).symm.toRingHom)
      (V.plus.toAddSubgroup.isClosed_of_isOpen hV.isOpen)
      (continuous_cancelBaseChange_symm A B C D)
    · intro b hb
      simpa using (S.completedTensor A T).inl_mem_completedTensor_plus (A := C) U
        (S.inl_mem_completedTensor_plus T hb)
    · intro d hd
      simpa using (S.completedTensor A T).inr_mem_completedTensor_plus (A := C) U hd
  exact le_antisymm (Subring.map_le_iff_le_comap.mpr hf) fun x hx ↦
    ⟨(CompletedTensor.cancelBaseChange A B C D).symm x, hg hx,
      (CompletedTensor.cancelBaseChange A B C D).apply_symm_apply x⟩

/-- Membership in the plus ring is preserved and reflected by completed base-change
cancellation. This is not a simp lemma: the intermediate plus ring is not determined by
the membership statement on the left. -/
theorem cancelBaseChange_mem_plus (S : Pair B) (T : Pair C) (U : Pair D)
    (hCD : T.plus ≤ U.plus.comap (algebraMap C D))
    (x : CompletedTensor C (CompletedTensor A B C) D) :
    let _ : IsAdicHom (algebraMap A D) := by
      rw [IsScalarTower.algebraMap_eq A C D]
      exact (inferInstance : IsAdicHom (algebraMap C D)).comp inferInstance
    CompletedTensor.cancelBaseChange A B C D x ∈ (S.completedTensor A U).plus ↔
      x ∈ ((S.completedTensor A T).completedTensor C U).plus := by
  intro hAD
  rw [← cancelBaseChange_plus A B C D S T U hCD]
  exact (CompletedTensor.cancelBaseChange A B C D).injective.mem_set_image

end TauCeti.Huber.Pair.completedTensor
