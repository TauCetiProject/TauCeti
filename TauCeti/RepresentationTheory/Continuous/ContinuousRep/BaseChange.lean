/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Extension of scalars commutes with the operations on continuous representations

For a continuous coefficient map `A → B` and continuous representations on finite `A`-modules,
extension of scalars `M ↦ B ⊗[A] M` (`TauCeti.ContinuousRep.baseChange`) commutes with

* restriction along a continuous monoid homomorphism, as an equality;
* products, through `TensorProduct.prodRight : B ⊗ (M × N) ≃ (B ⊗ M) × (B ⊗ N)`;
* twists by a continuous character `χ`, as an equality, the base-changed twist being by the image
  of `χ` in `Bˣ`;
* tensor products, through
  `TensorProduct.AlgebraTensorModule.distribBaseChange : B ⊗ (M ⊗ N) ≃ (B ⊗ M) ⊗_B (B ⊗ N)`.

The raw reduction `TauCeti.ContinuousRep.reduction` to the residue field is a base change, so it
commutes with these operations through the same identifications.

## Main results

* `TauCeti.ContinuousRep.baseChange_res`: `B ⊗ Res_φ M = Res_φ (B ⊗ M)`.
* `TauCeti.ContinuousRep.baseChangeProdIso`: `B ⊗ (M × N) ≅ (B ⊗ M) × (B ⊗ N)`.
* `TauCeti.ContinuousRep.baseChange_twist`: `B ⊗ M(χ) = (B ⊗ M)(χ_B)`.
* `TauCeti.ContinuousRep.baseChangeTprodIso`: `B ⊗ (M ⊗ N) ≅ (B ⊗ M) ⊗_B (B ⊗ N)`.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti.ContinuousRep

section Semiring

variable {Γ A M N : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommSemiring A] [TopologicalSpace A]
  [AddCommMonoid M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M]
  [AddCommMonoid N] [Module A N] [TopologicalSpace N] [IsModuleTopology A N] [Module.Finite A N]

variable (B : Type*) [Ring B] [TopologicalSpace B] [IsTopologicalSemiring B] [Algebra A B]
  [ContinuousSMul A B] [TopologicalSpace (B ⊗[A] M)] [IsModuleTopology B (B ⊗[A] M)]
  [TopologicalSpace (B ⊗[A] N)] [IsModuleTopology B (B ⊗[A] N)]

/-- **Extension of scalars commutes with restriction**: `B ⊗ Res_φ M = Res_φ (B ⊗ M)`. -/
theorem baseChange_res {Γ' : Type*} [Monoid Γ'] [TopologicalSpace Γ'] (ρ : ContinuousRep Γ A M)
    (φ : Γ' →ₜ* Γ) : (ρ.res φ).baseChange B = (ρ.baseChange B).res φ :=
  ext fun g x ↦ by simp [baseChange_apply]

variable [TopologicalSpace (B ⊗[A] (M × N))] [IsModuleTopology B (B ⊗[A] (M × N))]

/-- **Extension of scalars commutes with products**: `B ⊗ (M × N) ≅ (B ⊗ M) × (B ⊗ N)`, through
`TensorProduct.prodRight`. -/
def baseChangeProdIso (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) :
    Iso ((ρ.prod σ).baseChange B) ((ρ.baseChange B).prod (σ.baseChange B)) :=
  .ofEquiv (.mk (TensorProduct.prodRight A B B M N) fun g ↦ by
    refine TensorProduct.AlgebraTensorModule.ext fun b x ↦ ?_
    simp)

@[simp]
theorem baseChangeProdIso_tmul (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) (b : B)
    (x : M × N) : baseChangeProdIso B ρ σ (b ⊗ₜ x) = (b ⊗ₜ x.1, b ⊗ₜ x.2) := by
  simp [baseChangeProdIso]

@[simp]
theorem baseChangeProdIso_symm_tmul (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) (b : B)
    (x : M) (y : N) : (baseChangeProdIso B ρ σ).symm (b ⊗ₜ x, b ⊗ₜ y) = b ⊗ₜ (x, y) := by
  simp [baseChangeProdIso]

end Semiring

section Twist

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommSemiring A] [TopologicalSpace A]
  [AddCommMonoid M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M]

variable (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalSemiring B] [Algebra A B]
  [ContinuousSMul A B] [TopologicalSpace (B ⊗[A] M)] [IsModuleTopology B (B ⊗[A] M)]

/-- **Extension of scalars commutes with twisting**: `B ⊗ M(χ) = (B ⊗ M)(χ_B)`, where `χ_B` is
the image of `χ` in `Bˣ`. -/
theorem baseChange_twist (ρ : ContinuousRep Γ A M) (χ : Γ →ₜ* Aˣ) :
    haveI := IsModuleTopology.toContinuousSMul A M
    haveI := IsModuleTopology.toContinuousSMul B (B ⊗[A] M)
    (ρ.twist χ).baseChange B = (ρ.baseChange B).twist (unitsMapCharacter B χ) := by
  have := IsModuleTopology.toContinuousSMul A M
  have := IsModuleTopology.toContinuousSMul B (B ⊗[A] M)
  refine ext fun g x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul b x =>
    rw [twist_apply, coe_unitsMapCharacter_apply]
    simp [baseChange_apply, TensorProduct.tmul_smul, Algebra.smul_def, TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add, hx, hy, map_add]

end Twist

section Tensor

variable {Γ A M N : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  [Module.Finite A M] [AddCommGroup N] [Module A N] [TopologicalSpace N] [IsModuleTopology A N]
  [Module.Finite A N] [TopologicalSpace (M ⊗[A] N)] [IsModuleTopology A (M ⊗[A] N)]

variable (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [Algebra A B]
  [ContinuousSMul A B] [TopologicalSpace (B ⊗[A] M)] [IsModuleTopology B (B ⊗[A] M)]
  [TopologicalSpace (B ⊗[A] N)] [IsModuleTopology B (B ⊗[A] N)]
  [TopologicalSpace (B ⊗[A] (M ⊗[A] N))] [IsModuleTopology B (B ⊗[A] (M ⊗[A] N))]
  [TopologicalSpace ((B ⊗[A] M) ⊗[B] (B ⊗[A] N))]
  [IsModuleTopology B ((B ⊗[A] M) ⊗[B] (B ⊗[A] N))]

/-- **Extension of scalars commutes with tensor products**:
`B ⊗ (M ⊗ N) ≅ (B ⊗ M) ⊗_B (B ⊗ N)`, through
`TensorProduct.AlgebraTensorModule.distribBaseChange`. -/
def baseChangeTprodIso (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) :
    Iso ((ρ.tprod σ).baseChange B) ((ρ.baseChange B).tprod (σ.baseChange B)) :=
  .ofEquiv (.mk (TensorProduct.AlgebraTensorModule.distribBaseChange A B M N) fun g ↦ by
    refine TensorProduct.AlgebraTensorModule.ext fun b x ↦ ?_
    induction x using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add] at hx hy ⊢
      rw [hx, hy])

@[simp]
theorem baseChangeTprodIso_tmul (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) (b : B)
    (x : M) (y : N) : baseChangeTprodIso B ρ σ (b ⊗ₜ (x ⊗ₜ y)) = (b ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y) := by
  simp [baseChangeTprodIso]

@[simp]
theorem baseChangeTprodIso_symm_tmul (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N)
    (a b : B) (x : M) (y : N) :
    (baseChangeTprodIso B ρ σ).symm ((a ⊗ₜ x) ⊗ₜ (b ⊗ₜ y)) = (a * b) ⊗ₜ (x ⊗ₜ y) := by
  simp [baseChangeTprodIso]

end Tensor

end TauCeti.ContinuousRep
