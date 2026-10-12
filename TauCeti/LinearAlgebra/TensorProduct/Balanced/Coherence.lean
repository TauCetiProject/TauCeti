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

omit [SMulCommClass B k N] in
/-- Linear maps out of a left-associated triple balanced tensor product are determined by
their values on nested pure tensors. -/
theorem ext_threefold {Q : Type*} [AddCommGroup Q] [Module k Q]
    {f g : BalancedTensorProduct k C (BalancedTensorProduct k B M N) P →ₗ[k] Q}
    (h : ∀ m n p, f (tmul k C (tmul k B m n) p) = g (tmul k C (tmul k B m n) p)) :
    f = g := by
  apply hom_ext
  intro x p
  induction x using induction_on with
  | ht m n => exact h m n p
  | ha x y hx hy => simp only [add_tmul, map_add, hx, hy]

section Naturality

variable {M' N' P' : Type*}
  [AddCommGroup M'] [Module k M'] [Module Bᵐᵒᵖ M']
  [AddCommGroup N'] [Module k N'] [Module B N'] [Module Cᵐᵒᵖ N']
  [AddCommGroup P'] [Module k P'] [Module C P']
  [SMulCommClass B k N'] [SMulCommClass Cᵐᵒᵖ k N'] [SMulCommClass B Cᵐᵒᵖ N']
  (f : M →ₗ[k] M') (g : N →ₗ[k] N') (h : P →ₗ[k] P')
  (hf : ∀ (b : B) m, f (op b • m) = op b • f m)
  (hgB : ∀ (b : B) n, g (b • n) = b • g n)
  (hgC : ∀ (c : C) n, g (op c • n) = op c • g n)
  (hh : ∀ (c : C) p, h (c • p) = c • h p)

/-- Mapping the three factors commutes with balanced reassociation. -/
theorem map_map_comp_assoc_eq :
    map f (map g h hgC hh) hf
        (fun b z ↦ map_smul_left B g h hgC hh hgB b z) ∘ₗ assoc.toLinearMap =
      assoc.toLinearMap ∘ₗ map (map f g hf hgB) h
        (fun c z ↦ map_smul_right Cᵐᵒᵖ f g hf hgB (fun c n ↦ hgC c.unop n) (op c) z)
        hh := by
  apply ext_threefold
  intro m n p
  simp

end Naturality

section Pentagon

variable {D Q : Type*} [Semiring D]
  [Module Dᵐᵒᵖ P] [SMulCommClass C k P] [SMulCommClass Dᵐᵒᵖ k P]
  [SMulCommClass C Dᵐᵒᵖ P]
  [AddCommGroup Q] [Module k Q] [Module D Q]

omit [SMulCommClass B k N] [SMulCommClass C k P] in
/-- Linear maps out of a left-associated fourfold balanced tensor product are determined by
their values on nested pure tensors. -/
theorem ext_fourfold {T : Type*} [AddCommGroup T] [Module k T]
    {f g : BalancedTensorProduct k D
      (BalancedTensorProduct k C (BalancedTensorProduct k B M N) P) Q →ₗ[k] T}
    (h : ∀ m n p q, f (tmul k D (tmul k C (tmul k B m n) p) q) =
      g (tmul k D (tmul k C (tmul k B m n) p) q)) : f = g := by
  apply ext_threefold
  intro x p q
  induction x using induction_on with
  | ht m n => exact h m n p q
  | ha x y hx hy => simp only [add_tmul, map_add, hx, hy]

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

section Left

variable {N' : Type*} [AddCommGroup N'] [Module k N'] [Module A N']
  [IsScalarTower k A N']

/-- The left action identification is natural in equivariant linear maps. -/
theorem lid_naturality (f : N →ₗ[k] N')
    (hf : ∀ (a : A) n, f (a • n) = a • f n) :
    (lid k A N').toLinearMap ∘ₗ
        map LinearMap.id f (fun _ _ ↦ rfl) hf =
      f ∘ₗ (lid k A N).toLinearMap := by
  apply hom_ext
  intro a n
  simp [hf]

end Left

section Right

variable {M' : Type*} [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M']
  [IsScalarTower k Aᵐᵒᵖ M']

/-- The right action identification is natural in equivariant linear maps. -/
theorem rid_naturality (f : M →ₗ[k] M')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m) :
    (rid k A M').toLinearMap ∘ₗ
        map f LinearMap.id hf (fun _ _ ↦ rfl) =
      f ∘ₗ (rid k A M).toLinearMap := by
  apply hom_ext
  intro m a
  simp [hf]

end Right

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
