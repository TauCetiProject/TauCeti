/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Associator
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Unit

/-!
# Coherence of balanced tensor products

Balanced tensor products compose bimodules over possibly noncommutative algebras. Their
associator is natural in equivariant ground-ring linear maps and satisfies the pentagon;
the action identifications with the regular bimodule satisfy the triangle. Thus changing
parentheses or removing a regular factor gives consistent carrier maps, as needed when
composing DG bimodules.

The associativity results only require semirings acting on ground-ring modules. The unit
results use algebras, so that their actions are ground-ring linear. No grading, differential,
flatness, or finiteness assumption is needed for these carrier identities.

The graded counterparts are `GradedModuleCat.bimoduleTensorAssociator_naturality`,
`GradedModuleCat.bimoduleTensorAssociator_pentagon`,
`GradedModuleCat.bimoduleTensorAssociator_triangle`, and the graded unitor naturality laws in
`GradedModuleCat/BimoduleTensor`. Those results use enveloping-module carriers and a lifted
regular bimodule; these carrier laws also apply without a grading or outer algebra actions.

## References

* B. Keller, *Deriving DG categories*, Section 6.1 (composition by balanced tensor products).
* The ordinary tensor-product counterparts are Mathlib's
  `TensorProduct.map_map_comp_assoc_eq` and `SemimoduleCat.MonoidalCategory.pentagon` and
  `triangle`.
-/

public section

namespace TauCeti.BalancedTensorProduct

open MulOpposite

attribute [local instance 100] leftModule rightModule leftSMulCommClass rightSMulCommClass
  outerSMulCommClass

section Associativity

variable {k B C M N P : Type*} [CommRing k] [Semiring B] [Semiring C]
  [AddCommGroup M] [Module k M] [Module Bᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module B N] [Module Cᵐᵒᵖ N]
  [AddCommGroup P] [Module k P] [Module C P]
  [SMulCommClass B k N] [SMulCommClass Cᵐᵒᵖ k N] [SMulCommClass B Cᵐᵒᵖ N]

section Pentagon

variable {D Q : Type*} [Semiring D]
  [Module Dᵐᵒᵖ P] [SMulCommClass C k P] [SMulCommClass Dᵐᵒᵖ k P]
  [SMulCommClass C Dᵐᵒᵖ P]
  [AddCommGroup Q] [Module k Q] [Module D Q]

/-- The two reassociation paths from `((M ⊗_B N) ⊗_C P) ⊗_D Q` to
`M ⊗_B (N ⊗_C (P ⊗_D Q))` agree. -/
theorem pentagon :
    map LinearMap.id (assoc (k := k) (B := C) (C := D)
        (M := N) (N := P) (P := Q)).toLinearMap
        (fun _ _ ↦ rfl) (fun b z ↦ assoc_smul_left B b z) ∘ₗ
      (assoc (k := k) (B := B) (C := D)
        (M := M) (N := BalancedTensorProduct k C N P) (P := Q)).toLinearMap ∘ₗ
      map (assoc (k := k) (B := B) (C := C) (M := M) (N := N) (P := P)).toLinearMap
        LinearMap.id (fun d z ↦ assoc_smul_right Dᵐᵒᵖ (op d) z) (fun _ _ ↦ rfl) =
    (assoc (k := k) (B := B) (C := C)
        (M := M) (N := N) (P := BalancedTensorProduct k D P Q)).toLinearMap ∘ₗ
      (assoc (k := k) (B := C) (C := D)
        (M := BalancedTensorProduct k B M N) (N := P) (P := Q)).toLinearMap := by
  apply ext_fourfold
  intro m n p q
  simp

end Pentagon

end Associativity

section Units

variable {k A M N : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- Removing the regular middle bimodule directly agrees with reassociating and then
removing it: the triangle identity for balanced tensor products. -/
theorem triangle :
    map LinearMap.id (lid k A N).toLinearMap (fun _ _ ↦ rfl)
        (fun a z ↦ lid_smul_left k A N a z) ∘ₗ
      (assoc (k := k) (B := A) (C := A) (M := M) (N := A) (P := N)).toLinearMap =
      map (rid k A M).toLinearMap LinearMap.id
        (fun a z ↦ rid_smul_right k A M (op a) z) (fun _ _ ↦ rfl) := by
  apply ext_threefold
  intro m a n
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, assoc_tmul, map_tmul,
    LinearMap.id_apply, lid_tmul, rid_tmul]
  exact (balance k A a m n).symm

end Units

end TauCeti.BalancedTensorProduct
