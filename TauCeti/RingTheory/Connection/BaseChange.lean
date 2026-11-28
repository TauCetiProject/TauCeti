/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Connection.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Base change of module connections

Let `A → B` be an algebra with derivations `d : A → Ω` and `d' : B → Ω'`. To pull a connection
back to `B ⊗[A] M`, one needs a map of one-forms `B ⊗[A] Ω → Ω'` taking `1 ⊗ d a` to the
differential of the image of `a`. This makes the product rule on pure tensors balanced over `A`.
The resulting connection is uniquely determined by its
values on the sections `1 ⊗ m`. Horizontal maps pull back, and the canonical identifications
for the identity map and for a tower of algebras are horizontal.

For ordinary Kähler differentials in a commutative square with base map `R → S`, use
`(KaehlerDifferential.map R S A B).liftBaseChange B` as the map of one-forms.
Its compatibility is `KaehlerDifferential.map_D` on the generators `1 ⊗ d a`.

## References

* The Stacks Project, [Remark 60.6.9](https://stacks.math.columbia.edu/tag/07KJ).
-/

public section

open TensorProduct

namespace TauCeti.ModuleConnection

variable {R A S B Ω Ω' M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [CommSemiring S] [CommSemiring B] [Algebra S B] [Algebra A B]
  [AddCommMonoid Ω] [Module A Ω] [Module R Ω] [AddCommMonoid Ω'] [Module B Ω'] [Module S Ω']
  [AddCommMonoid M] [Module A M] {d : Derivation R A Ω}

variable (c : ModuleConnection d M) (d' : Derivation S B Ω') (φ : B ⊗[A] Ω →ₗ[B] Ω')

/-- The two terms obtained by differentiating the section and the scalar in a pure tensor. -/
private def baseChangePair : B →+ M →+ (B ⊗[A] M) ⊗[B] Ω' where
  toFun b :=
    { toFun := fun m ↦
        φ.lTensor _ (AlgebraTensorModule.distribBaseChange A B M Ω (b ⊗ₜ[A] c m)) +
          ((1 : B) ⊗ₜ[A] m) ⊗ₜ[B] d' b
      map_zero' := by simp
      map_add' := fun m n ↦ by simp [tmul_add, add_tmul, add_add_add_comm] }
  map_zero' := by ext m; simp
  map_add' b b' := by ext m; simp [add_tmul, tmul_add, add_add_add_comm]

private theorem baseChangePair_apply (b : B) (m : M) :
    baseChangePair c d' φ b m =
      φ.lTensor _ (AlgebraTensorModule.distribBaseChange A B M Ω (b ⊗ₜ[A] c m)) +
        ((1 : B) ⊗ₜ[A] m) ⊗ₜ[B] d' b := rfl

variable (hφ : ∀ a, φ ((1 : B) ⊗ₜ[A] d a) = d' (algebraMap A B a))

private theorem baseChangePair_balanced (a : A) (ha : φ ((1 : B) ⊗ₜ[A] d a) = d' (algebraMap A B a))
    (b : B) (m : M) :
    baseChangePair c d' φ (a • b) m = baseChangePair c d' φ b (a • m) := by
  simp [baseChangePair_apply, tmul_add, smul_tmul', Algebra.smul_def, ha,
    add_comm, add_left_comm, add_assoc]

/-- Extend a connection to the scalar extension along a compatible map of one-forms. -/
def baseChange : ModuleConnection d' (B ⊗[A] M) where
  toAddMonoidHom := liftAddHom (baseChangePair c d' φ)
    fun a ↦ baseChangePair_balanced c d' φ a (hφ a)
  leibniz' b z := by
    induction z using TensorProduct.inductionOn with
    | tmul t m =>
      rw [smul_tmul']
      simp only [liftAddHom_tmul, baseChangePair_apply, smul_eq_mul, smul_add, Derivation.leibniz,
        tmul_add, ← LinearMap.map_smul, ← LinearEquiv.map_smul, smul_tmul', tmul_smul, mul_one,
        add_assoc]
    | add x y hx hy => simp [smul_add, hx, hy, TensorProduct.add_tmul, add_add_add_comm]

/-- On a pure tensor the pullback differentiates both the original section and its new scalar. -/
@[simp]
theorem baseChange_tmul (b : B) (m : M) :
    c.baseChange d' φ hφ (b ⊗ₜ[A] m) =
      φ.lTensor _ (AlgebraTensorModule.distribBaseChange A B M Ω (b ⊗ₜ[A] c m)) +
        ((1 : B) ⊗ₜ[A] m) ⊗ₜ[B] d' b :=
  (liftAddHom_tmul _ (fun a ↦ baseChangePair_balanced c d' φ a (hφ a)) b m).trans
    (baseChangePair_apply ..)

/-- Two connections on a scalar extension agree if they agree on the original sections. -/
theorem ext_one_tmul {c₁ c₂ : ModuleConnection d' (B ⊗[A] M)}
    (h : ∀ m : M, c₁ ((1 : B) ⊗ₜ[A] m) = c₂ ((1 : B) ⊗ₜ[A] m)) : c₁ = c₂ := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul b m => rw [TensorProduct.tmul_eq_smul_one_tmul, c₁.leibniz, c₂.leibniz, h]
  | add x y hx hy => simp [hx, hy]

/-- The characteristic property of the pullback connection on a scalar extension. -/
theorem eq_baseChange_iff (c' : ModuleConnection d' (B ⊗[A] M)) :
    c' = c.baseChange d' φ hφ ↔ ∀ m : M, c' ((1 : B) ⊗ₜ[A] m) =
      φ.lTensor _ (AlgebraTensorModule.distribBaseChange A B M Ω ((1 : B) ⊗ₜ[A] c m)) := by
  constructor
  · rintro rfl m
    simp
  · intro h
    apply ext_one_tmul
    simpa using h

/-- Horizontality of a map out of a scalar extension can be tested on the original sections. -/
theorem isHorizontal_iff_one_tmul {N : Type*} [AddCommMonoid N] [Module B N]
    (c₁ : ModuleConnection d' (B ⊗[A] M)) (c₂ : ModuleConnection d' N)
    (f : B ⊗[A] M →ₗ[B] N) :
    c₁.IsHorizontal c₂ f ↔ ∀ m : M, c₂ (f ((1 : B) ⊗ₜ[A] m)) =
      f.rTensor Ω' (c₁ ((1 : B) ⊗ₜ[A] m)) := by
  rw [isHorizontal_iff]
  refine ⟨fun h m ↦ h _, fun h z ↦ ?_⟩
  induction z using TensorProduct.inductionOn with
  | tmul b m => simp [tmul_eq_smul_one_tmul b m, h]
  | add x y hx hy => simp [hx, hy]

/-- Extension of scalars sends horizontal maps to horizontal maps. -/
theorem IsHorizontal.baseChange {N : Type*} [AddCommMonoid N] [Module A N]
    {c : ModuleConnection d M} {c' : ModuleConnection d N} {f : M →ₗ[A] N}
    (hf : c.IsHorizontal c' f) :
    (c.baseChange d' φ hφ).IsHorizontal (c'.baseChange d' φ hφ) (f.baseChange B) := by
  rw [isHorizontal_iff] at hf
  apply (isHorizontal_iff_one_tmul ..).2
  intro m
  simp only [LinearMap.baseChange_tmul, baseChange_tmul, hf, Derivation.map_one_eq_zero,
    tmul_zero, add_zero]
  generalize c m = t
  induction t using TensorProduct.inductionOn with
  | tmul x ω => simp
  | add x y hx hy => simp [tmul_add, hx, hy]

/-- The pullback of the scalar connection is the scalar connection for the new derivation,
under the identification `B ⊗[A] A ≃ B`. -/
theorem isHorizontal_rid :
    (d.moduleConnection.baseChange d' φ hφ).IsHorizontal d'.moduleConnection
      (AlgebraTensorModule.rid A B B).toLinearMap := by
  apply (isHorizontal_iff_one_tmul ..).2
  intro a
  simp [hφ, Algebra.smul_def]

/-- The tensor unit isomorphism identifies the identity pullback with the original connection. -/
theorem isHorizontal_lid_symm :
    c.IsHorizontal (c.baseChange d (TensorProduct.lid A Ω).toLinearMap (by simp))
      (TensorProduct.lid A M).symm.toLinearMap := by
  rw [isHorizontal_iff]
  intro m
  simp only [LinearEquiv.coe_coe, lid_symm_apply, baseChange_tmul, Derivation.map_one_eq_zero,
    tmul_zero, add_zero]
  generalize c m = t
  induction t using TensorProduct.inductionOn with
  | tmul x ω => simp
  | add x y hx hy => simp [tmul_add, hx, hy]

section Tower

variable {T C Ω'' : Type*} [CommSemiring T] [CommSemiring C] [Algebra T C]
  [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  [AddCommMonoid Ω''] [Module C Ω''] [Module T Ω'']
  (d'' : Derivation T C Ω'') (ψ : C ⊗[B] Ω' →ₗ[C] Ω'')
  (hψ : ∀ b, ψ ((1 : C) ⊗ₜ[B] d' b) = d'' (algebraMap B C b))

/-- Successive pullbacks of a connection agree with pullback along the composite under the
canonical identification of the two scalar extensions. -/
theorem isHorizontal_cancelBaseChange_symm :
    (c.baseChange d'' (ψ ∘ₗ φ.baseChange C ∘ₗ (AlgebraTensorModule.cancelBaseChange A B C C Ω).symm)
      (fun a ↦ by simp [hφ, hψ, IsScalarTower.algebraMap_apply A B C])).IsHorizontal
      ((c.baseChange d' φ hφ).baseChange d'' ψ hψ)
      (AlgebraTensorModule.cancelBaseChange A B C C M).symm.toLinearMap := by
  apply (isHorizontal_iff_one_tmul ..).2
  intro m
  simp only [LinearEquiv.coe_coe, AlgebraTensorModule.cancelBaseChange_symm_tmul,
    baseChange_tmul, Derivation.map_one_eq_zero, tmul_zero, add_zero]
  generalize c m = t
  induction t using TensorProduct.inductionOn with
  | tmul x ω => simp
  | add x y hx hy => simp [tmul_add, hx, hy]

end Tower

end TauCeti.ModuleConnection
