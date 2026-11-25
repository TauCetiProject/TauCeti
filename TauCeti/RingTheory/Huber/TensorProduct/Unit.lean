/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Finite.Algebra

/-!
# The unit of the completed tensor product

For an adic map `A → B` with `B` complete Hausdorff, the completed tensor product
`B ⊗̂[A] A` is canonically `B`. The equivalence sends `b ⊗ a` to `b * algebraMap A B a`,
and its inverse is the left coprojection. Neither completeness of `A` nor a Tate hypothesis
is required.

The construction specializes `Pair.finiteAlgebra.baseChangeEquiv` to the rank-one algebra
`A`, then applies Mathlib's algebraic tensor unit. If `A⁺` maps into `B⁺`, this identifies
the completed tensor plus ring with the specified `B⁺`. Thus the unit comparison also
holds for Huber pairs, including pairs whose plus ring is smaller than the power-bounded
subring. Over the base itself, for `A⁺₁ ≤ A⁺₂` on a complete Hausdorff `A`, the right unit
carries the plus ring of `(A, A⁺₁) ⊗̂_A (A, A⁺₂)` onto the larger `A⁺₂`.

## References

* S. Morel, *Adic spaces*, §II.3.2, Proposition II.3.2.1 (the completed tensor universal
  property).
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, §1.2,
  proof of Proposition 1.2.2(1).
-/

public section

open TensorProduct

namespace TauCeti.Huber

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T2Space B] [IsAdicHom (algebraMap A B)]

namespace CompletedTensor

/-- The right unit of the completed tensor product, for a complete Hausdorff Huber algebra. -/
noncomputable def rightUnitor : CompletedTensor A B A ≃+* B :=
  (Pair.finiteAlgebra.baseChangeEquiv A B A).symm.trans
    (Algebra.TensorProduct.rid A B B).toRingEquiv

/-- The right unit sends the left coprojection to the identity. -/
@[simp] theorem rightUnitor_inl (b : B) : rightUnitor A B (inl A B A b) = b := by
  simp [rightUnitor]

/-- The right unit sends the right coprojection to the structure map. -/
@[simp] theorem rightUnitor_inr (a : A) :
    rightUnitor A B (inr A B A a) = algebraMap A B a := by
  simp [rightUnitor, Algebra.smul_def]

/-- The inverse right unit is the left coprojection on every element. -/
@[simp] theorem rightUnitor_symm_apply (b : B) :
    (rightUnitor A B).symm b = inl A B A b := by
  apply (rightUnitor A B).injective
  simp

/-- The left coprojection is also a left inverse to the completed tensor right unit. -/
@[simp] theorem inl_rightUnitor (x : CompletedTensor A B A) :
    inl A B A (rightUnitor A B x) = x := by
  rw [← rightUnitor_symm_apply, RingEquiv.symm_apply_apply]

/-- On pure tensors, the unit comparison multiplies the two factors in `B`. -/
theorem rightUnitor_tmul (b : B) (a : A) :
    rightUnitor A B (toCompletion A B A (b ⊗ₜ[A] a)) = b * algebraMap A B a := by
  simp

/-- The right unit is continuous. -/
@[fun_prop] theorem continuous_rightUnitor : Continuous (rightUnitor A B) := by
  let : TopologicalSpace (B ⊗[A] A) := moduleTopology B (B ⊗[A] A)
  exact (IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.rid A B B).toLinearMap).comp
      ((Pair.finiteAlgebra.baseChangeEquiv A B A).toEquiv.isHomeomorph_iff.mp
        (Pair.finiteAlgebra.isHomeomorph_baseChangeEquiv A B A)).2

/-- The inverse right unit is continuous. -/
@[fun_prop] theorem continuous_rightUnitor_symm : Continuous (rightUnitor A B).symm := by
  exact (continuous_inl A B A).congr fun b => (rightUnitor_symm_apply A B b).symm

/-- The completed tensor right unit is a homeomorphism. -/
theorem isHomeomorph_rightUnitor : IsHomeomorph (rightUnitor A B) :=
  (rightUnitor A B).toEquiv.isHomeomorph_iff.mpr
    ⟨continuous_rightUnitor A B, continuous_rightUnitor_symm A B⟩

end CompletedTensor

namespace Pair.completedTensor

variable {A B} (S : Pair A) (T : Pair B)
  (h : ∀ a ∈ S.plus, algebraMap A B a ∈ T.plus)

include h

/-- Membership in the completed tensor plus ring is detected by the right unit. -/
@[simp] theorem rightUnitor_mem_plus (x : CompletedTensor A B A) :
    x ∈ (T.completedTensor A S).plus ↔ CompletedTensor.rightUnitor A B x ∈ T.plus := by
  have := T.isRingOfIntegralElements.isIntegrallyClosedIn
  constructor
  · intro hx
    exact T.completedTensor_plus_le_comap S
      (f := (CompletedTensor.rightUnitor A B).toRingHom)
      (T.plus.toAddSubgroup.isClosed_of_isOpen T.isRingOfIntegralElements.isOpen)
      (CompletedTensor.continuous_rightUnitor A B)
      (fun b hb => by simpa using hb) (fun a ha => by simpa using h a ha) hx
  · intro hx
    have hx' := T.inl_mem_completedTensor_plus (A := A) S hx
    simpa only [← CompletedTensor.rightUnitor_symm_apply, RingEquiv.symm_apply_apply] using hx'

/-- The completed tensor right unit carries its plus ring exactly onto `B⁺`. -/
theorem rightUnitor_plus :
    (T.completedTensor A S).plus.map (CompletedTensor.rightUnitor A B).toRingHom = T.plus := by
  ext b
  rw [RingEquiv.toRingHom_eq_coe, Subring.mem_map_equiv,
    CompletedTensor.rightUnitor_symm_apply]
  simpa using (rightUnitor_mem_plus S T h (CompletedTensor.inl A B A b))

/-- The unit comparison as a morphism of Huber pairs. -/
noncomputable def rightUnitorHom : Hom (T.completedTensor A S) T where
  toRingHom := (CompletedTensor.rightUnitor A B).toRingHom
  continuous_toRingHom := CompletedTensor.continuous_rightUnitor A B
  map_mem_plus _ hx := (rightUnitor_mem_plus S T h _).mp hx

/-- The underlying ring map of the pair unit is the completed tensor unit. -/
@[simp] theorem toRingHom_rightUnitorHom :
    (rightUnitorHom S T h).toRingHom = (CompletedTensor.rightUnitor A B).toRingHom := (rfl)

/-- The pair unit followed by its inverse is the identity on the completed tensor pair. -/
@[simp] theorem inl_comp_rightUnitorHom :
    (inl A T S).comp (rightUnitorHom S T h) = Hom.id (T.completedTensor A S) := by
  ext x
  simp

/-- The pair unit restricts to the identity on the left factor. -/
@[simp] theorem rightUnitorHom_comp_inl :
    (rightUnitorHom S T h).comp (inl A T S) = Hom.id T := by
  ext b
  simp

end Pair.completedTensor

end TauCeti.Huber

namespace TauCeti.Huber.Pair.completedTensor

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A] [CompleteSpace A] [T2Space A] {S T : Pair A}

/-- **The completed tensor plus ring over the base is the larger plus ring.** For
`A⁺₁ ≤ A⁺₂` on the same complete Hausdorff ring, an element of `A ⊗̂_A A` lies in the plus ring of
`(A, A⁺₁) ⊗̂_A (A, A⁺₂)` exactly when its image under the right unit lies in `A⁺₂`. -/
@[simp] theorem rightUnitor_mem_plus_self_iff (hST : S.plus ≤ T.plus)
    (x : CompletedTensor A A A) :
    x ∈ (S.completedTensor A T).plus ↔ CompletedTensor.rightUnitor A A x ∈ T.plus := by
  have := T.isRingOfIntegralElements.isIntegrallyClosedIn
  constructor
  · intro hx
    exact S.completedTensor_plus_le_comap T
      (f := (CompletedTensor.rightUnitor A A).toRingHom)
      (T.plus.toAddSubgroup.isClosed_of_isOpen T.isRingOfIntegralElements.isOpen)
      (CompletedTensor.continuous_rightUnitor A A)
      (fun b hb ↦ by simpa using hST hb) (fun c hc ↦ by simpa using hc) hx
  · intro hx
    have hinr : CompletedTensor.inr A A A (CompletedTensor.rightUnitor A A x) = x :=
      (CompletedTensor.rightUnitor A A).injective (by simp)
    simpa only [hinr] using S.inr_mem_completedTensor_plus (A := A) T hx

/-- For `A⁺₁ ≤ A⁺₂`, the right unit carries the plus ring of `(A, A⁺₁) ⊗̂_A (A, A⁺₂)` exactly onto
`A⁺₂`. -/
theorem rightUnitor_plus_self (hST : S.plus ≤ T.plus) :
    (S.completedTensor A T).plus.map (CompletedTensor.rightUnitor A A).toRingHom = T.plus := by
  ext b
  rw [RingEquiv.toRingHom_eq_coe, Subring.mem_map_equiv, rightUnitor_mem_plus_self_iff hST,
    RingEquiv.apply_symm_apply]

end TauCeti.Huber.Pair.completedTensor
