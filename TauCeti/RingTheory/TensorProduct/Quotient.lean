/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor products of quotient algebras

Quotienting both factors of a tensor product is the same as quotienting the tensor product
by the sum of the two extended ideals. This is the algebra analogue of Mathlib's linear
`TensorProduct.quotientTensorQuotientEquiv`, and the finite-level comparison used when
completing both factors simultaneously.
-/

public section

open TensorProduct

namespace Algebra.TensorProduct

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]

/-- The tensor product of two quotient algebras is the quotient by the sum of the extended
ideals. The equivalence sends the tensor of two residue classes to the class of their tensor. -/
noncomputable def quotientTensorQuotientEquiv (I : Ideal B) (J : Ideal C) :
    (B ⧸ I) ⊗[A] (C ⧸ J) ≃ₐ[A]
      (B ⊗[A] C) ⧸ (I.map (includeLeft : B →ₐ[A] B ⊗[A] C) ⊔
        J.map (includeRight : C →ₐ[A] B ⊗[A] C)) := by
  let K := I.map (includeLeft : B →ₐ[A] B ⊗[A] C) ⊔
    J.map (includeRight : C →ₐ[A] B ⊗[A] C)
  let l : B ⧸ I →ₐ[A] (B ⊗[A] C) ⧸ K :=
    Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ A K).comp includeLeft)
      (fun b hb ↦ Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hb)))
  let r : C ⧸ J →ₐ[A] (B ⊗[A] C) ⧸ K :=
    Ideal.Quotient.liftₐ J ((Ideal.Quotient.mkₐ A K).comp includeRight)
      (fun c hc ↦ Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hc)))
  let f := Algebra.TensorProduct.lift l r (fun _ _ ↦ Commute.all _ _)
  let g := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ A I) (Ideal.Quotient.mkₐ A J)
  have hg : K ≤ RingHom.ker g := by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.map_le_iff_le_comap.mpr ?_)
    · intro b hb
      simp [g, Ideal.Quotient.eq_zero_iff_mem.mpr hb]
    · intro c hc
      simp [g, Ideal.Quotient.eq_zero_iff_mem.mpr hc]
  have hl (b : B) : l (Ideal.Quotient.mk I b) = Ideal.Quotient.mk K (b ⊗ₜ[A] 1) := rfl
  have hr (c : C) : r (Ideal.Quotient.mk J c) = Ideal.Quotient.mk K (1 ⊗ₜ[A] c) := rfl
  have hq (x : B ⊗[A] C) : Ideal.Quotient.liftₐ K g hg (Ideal.Quotient.mk K x) = g x := rfl
  exact AlgEquiv.ofAlgHom f (Ideal.Quotient.liftₐ K g hg)
    (by
      apply Ideal.Quotient.algHom_ext
      ext b
      · -- Keep the named quotient and lift intact while computing on representatives.
        change f (Ideal.Quotient.liftₐ K g hg (Ideal.Quotient.mk K (b ⊗ₜ[A] 1))) =
          Ideal.Quotient.mk K (b ⊗ₜ[A] 1)
        rw [hq]
        simp [f, g, hl]
      · -- The right inclusion is handled by the same representative equation.
        change f (Ideal.Quotient.liftₐ K g hg (Ideal.Quotient.mk K (1 ⊗ₜ[A] b))) =
          Ideal.Quotient.mk K (1 ⊗ₜ[A] b)
        rw [hq]
        simp [f, g, hr])
    (by
      ext b
      all_goals
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
        simp [f, g, hq, hl, hr])

/-- The double-quotient comparison on tensors of residue classes. -/
@[simp]
theorem quotientTensorQuotientEquiv_tmul (I : Ideal B) (J : Ideal C) (b : B) (c : C) :
    quotientTensorQuotientEquiv (A := A) I J
      (Ideal.Quotient.mk I b ⊗ₜ[A] Ideal.Quotient.mk J c) =
        Ideal.Quotient.mk _ (b ⊗ₜ[A] c) := by
  -- The tensor lift and quotient lifts compute on representatives. Avoid unfolding their
  -- proof fields, which mix algebra-homomorphism and ring-homomorphism coercions.
  change Ideal.Quotient.mk _ (b ⊗ₜ[A] 1) * Ideal.Quotient.mk _ (1 ⊗ₜ[A] c) =
    Ideal.Quotient.mk _ (b ⊗ₜ[A] c)
  simp [← map_mul]

/-- The double-quotient comparison on the left factor inclusion. -/
@[simp]
theorem quotientTensorQuotientEquiv_tmul_one (I : Ideal B) (J : Ideal C) (b : B) :
    quotientTensorQuotientEquiv (A := A) I J (Ideal.Quotient.mk I b ⊗ₜ[A] 1) =
      Ideal.Quotient.mk _ (b ⊗ₜ[A] 1) := by
  simpa only [map_one] using quotientTensorQuotientEquiv_tmul (A := A) I J b 1

/-- The double-quotient comparison on the right factor inclusion. -/
@[simp]
theorem quotientTensorQuotientEquiv_one_tmul (I : Ideal B) (J : Ideal C) (c : C) :
    quotientTensorQuotientEquiv (A := A) I J (1 ⊗ₜ[A] Ideal.Quotient.mk J c) =
      Ideal.Quotient.mk _ (1 ⊗ₜ[A] c) := by
  simpa only [map_one] using quotientTensorQuotientEquiv_tmul (A := A) I J 1 c

/-- The inverse double-quotient comparison on classes of tensors. -/
@[simp]
theorem quotientTensorQuotientEquiv_symm_tmul (I : Ideal B) (J : Ideal C) (b : B) (c : C) :
    (quotientTensorQuotientEquiv (A := A) I J).symm
      (Ideal.Quotient.mk _ (b ⊗ₜ[A] c)) =
        Ideal.Quotient.mk I b ⊗ₜ[A] Ideal.Quotient.mk J c := by
  apply (quotientTensorQuotientEquiv (A := A) I J).injective
  simp

end Algebra.TensorProduct
