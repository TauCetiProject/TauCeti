/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Actions

/-!
# Associativity of balanced tensor products

For a right B-module M, a (B,C)-bimodule N, and a left C-module P, the two
balanced tensor products (M tensor_B N) tensor_C P and M tensor_B (N tensor_C P)
are canonically identified. The map sends a nested pure tensor to the other
parenthesization and preserves the two outer actions. It uses the balanced
quotient universal property at both stages, rather than assuming that either
balancing algebra is commutative. This supplies the carrier associator needed
for graded triple braid products and transfer through supplied bimodules.
-/

public section

namespace TauCeti.BalancedTensorProduct

open MulOpposite

variable {k B C M N P : Type*} [CommRing k] [Semiring B] [Semiring C]
  [AddCommGroup M] [Module k M] [Module Bᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module B N] [Module Cᵐᵒᵖ N]
  [AddCommGroup P] [Module k P] [Module C P]
  [SMulCommClass B k N] [SMulCommClass Cᵐᵒᵖ k N] [SMulCommClass B Cᵐᵒᵖ N]

attribute [local instance 100] leftModule rightModule

local notation "L" => BalancedTensorProduct k C (BalancedTensorProduct k B M N) P
local notation "R" => BalancedTensorProduct k B M (BalancedTensorProduct k C N P)

private def assocTrilinear : M →ₗ[k] N →ₗ[k] P →ₗ[k] R where
  toFun m :=
    { toFun n := (mk k B m).comp (mk k C n)
      map_add' n n' := by ext p; simp [LinearMap.comp_apply, tmul_add]
      map_smul' c n := by ext p; simp [LinearMap.comp_apply] }
  map_add' m m' := by ext n p; simp [LinearMap.comp_apply]
  map_smul' c m := by ext n p; simp [LinearMap.comp_apply]

omit [SMulCommClass Cᵐᵒᵖ k N] in
private theorem assocTrilinear_apply (m : M) (n : N) (p : P) :
    assocTrilinear m n p = tmul k B m (tmul k C n p) := by
  simp [assocTrilinear, LinearMap.comp_apply]

private def assocPre : BalancedTensorProduct k B M N →ₗ[k] P →ₗ[k] R :=
  lift assocTrilinear (by
    intro b m n
    ext p
    rw [assocTrilinear_apply, assocTrilinear_apply, balance, smul_tmul_left])

omit [SMulCommClass Cᵐᵒᵖ k N] in
private theorem assocPre_tmul (m : M) (n : N) (p : P) :
    assocPre (tmul k B m n) p = tmul k B m (tmul k C n p) := by
  simp only [assocPre, lift_tmul, assocTrilinear_apply]

private def assocForward : L →ₗ[k] R :=
  lift assocPre (by
    intro c x p
    induction x using induction_on with
    | ht m n =>
      rw [smul_tmul_right, assocPre_tmul, assocPre_tmul, balance]
    | ha x y hx hy => simp [smul_add, map_add, LinearMap.add_apply, hx, hy])

private theorem assocForward_tmul (m : M) (n : N) (p : P) :
    assocForward (tmul k C (tmul k B m n) p) = tmul k B m (tmul k C n p) := by
  simp only [assocForward, lift_tmul, assocPre_tmul]

private def assocInverseTrilinear : N →ₗ[k] P →ₗ[k] M →ₗ[k] L where
  toFun n :=
    { toFun p :=
        { toFun m := tmul k C (tmul k B m n) p
          map_add' m m' := by simp [add_tmul]
          map_smul' c m := by simp }
      map_add' p p' := by ext m; simp [tmul_add]
      map_smul' c p := by ext m; simp }
  map_add' n n' := by ext p m; simp [tmul_add, add_tmul]
  map_smul' c n := by ext p m; simp

omit [SMulCommClass B k N] in
private theorem assocInverseTrilinear_apply (n : N) (p : P) (m : M) :
    assocInverseTrilinear n p m = tmul k C (tmul k B m n) p := rfl

private def assocInversePre : BalancedTensorProduct k C N P →ₗ[k] M →ₗ[k] L :=
  lift assocInverseTrilinear (by
    intro c n p
    ext m
    rw [assocInverseTrilinear_apply, assocInverseTrilinear_apply,
      ← smul_tmul_right, balance])

omit [SMulCommClass B k N] in
private theorem assocInversePre_tmul (m : M) (n : N) (p : P) :
    assocInversePre (tmul k C n p) m = tmul k C (tmul k B m n) p := by
  rw [assocInversePre, lift_tmul, assocInverseTrilinear_apply]

private def assocBackward : R →ₗ[k] L :=
  lift assocInversePre.flip (by
    intro b m x
    induction x using induction_on with
    | ht n p =>
      rw [smul_tmul_left, LinearMap.flip_apply, LinearMap.flip_apply,
        assocInversePre_tmul, assocInversePre_tmul, balance]
    | ha x y hx hy =>
      simp [smul_add, map_add, LinearMap.flip_apply, hx, hy])

private theorem assocBackward_tmul (m : M) (n : N) (p : P) :
    assocBackward (tmul k B m (tmul k C n p)) = tmul k C (tmul k B m n) p := by
  simp only [assocBackward, lift_tmul, LinearMap.flip_apply, assocInversePre_tmul]

/-- Reassociate a pair of balanced tensor products through the middle bimodule. -/
def assoc : L ≃ₗ[k] R :=
  LinearEquiv.ofLinearMap assocForward assocBackward
    (by
      apply hom_ext
      intro m x
      induction x using induction_on with
      | ht n p => simp [LinearMap.comp_apply, assocForward_tmul, assocBackward_tmul]
      | ha x y hx hy => simp [tmul_add, map_add, LinearMap.comp_apply] at *; simp [hx, hy])
    (by
      apply hom_ext
      intro x p
      induction x using induction_on with
      | ht m n => simp [LinearMap.comp_apply, assocForward_tmul, assocBackward_tmul]
      | ha x y hx hy => simp [add_tmul, map_add, LinearMap.comp_apply] at *; simp [hx, hy])

/-- The balanced associator changes only the parentheses of a pure tensor. -/
@[simp]
theorem assoc_tmul (m : M) (n : N) (p : P) :
    assoc (tmul k C (tmul k B m n) p) = tmul k B m (tmul k C n p) := by
  simp [assoc, assocForward_tmul]

/-- The inverse balanced associator restores the original parentheses. -/
@[simp]
theorem assoc_symm_tmul (m : M) (n : N) (p : P) :
    assoc.symm (tmul k B m (tmul k C n p)) = tmul k C (tmul k B m n) p := by
  simp [assoc, assocBackward_tmul]

section OuterLeft

variable (S : Type*) [Semiring S] [Module S M]
  [SMulCommClass S k M] [SMulCommClass S Bᵐᵒᵖ M]

/-- The balanced associator preserves any commuting action on its first factor. -/
theorem assoc_smul_left (s : S) (x : L) :
    let _ := leftModule (k := k) (A := B) (M := M) (N := N) S
    let _ := leftSMulCommClass (k := k) (A := B) (M := M) (N := N) S
    let _ := outerSMulCommClass (k := k) (A := B) (M := M) (N := N) S Cᵐᵒᵖ
    let _ := leftModule (k := k) (A := C) (M := BalancedTensorProduct k B M N) (N := P) S
    let _ := leftModule (k := k) (A := B) (M := M) (N := BalancedTensorProduct k C N P) S
    assoc (s • x) = s • assoc x := by
  let _ := leftModule (k := k) (A := B) (M := M) (N := N) S
  let _ := leftSMulCommClass (k := k) (A := B) (M := M) (N := N) S
  let _ := outerSMulCommClass (k := k) (A := B) (M := M) (N := N) S Cᵐᵒᵖ
  let _ := leftModule (k := k) (A := C) (M := BalancedTensorProduct k B M N) (N := P) S
  let _ := leftModule (k := k) (A := B) (M := M) (N := BalancedTensorProduct k C N P) S
  induction x using induction_on with
  | ht y p =>
    induction y using induction_on with
    | ht m n => simp [smul_tmul_left]
    | ha y z hy hz =>
      simp only [smul_tmul_left] at hy hz
      simp [smul_add, add_tmul, map_add, hy, hz]
  | ha x y hx hy => simp [smul_add, map_add, hx, hy]

end OuterLeft

section OuterRight

variable (T : Type*) [Semiring T] [Module T P]
  [SMulCommClass T k P] [SMulCommClass C T P]

/-- The balanced associator preserves any commuting action on its last factor. -/
theorem assoc_smul_right (s : T) (x : L) :
    let _ := rightModule (k := k) (A := C) (M := N) (N := P) T
    let _ := rightSMulCommClass (k := k) (A := C) (M := N) (N := P) T
    let _ := outerSMulCommClass (k := k) (A := C) (M := N) (N := P) B T
    let _ := rightModule (k := k) (A := B) (M := M) (N := BalancedTensorProduct k C N P) T
    let _ := rightModule (k := k) (A := C) (M := BalancedTensorProduct k B M N) (N := P) T
    assoc (s • x) = s • assoc x := by
  let _ := rightModule (k := k) (A := C) (M := N) (N := P) T
  let _ := rightSMulCommClass (k := k) (A := C) (M := N) (N := P) T
  let _ := outerSMulCommClass (k := k) (A := C) (M := N) (N := P) B T
  let _ := rightModule (k := k) (A := B) (M := M) (N := BalancedTensorProduct k C N P) T
  let _ := rightModule (k := k) (A := C) (M := BalancedTensorProduct k B M N) (N := P) T
  induction x using induction_on with
  | ht y p =>
    induction y using induction_on with
    | ht m n => simp [smul_tmul_right]
    | ha y z hy hz =>
      simp only [smul_tmul_right] at hy hz
      simp [smul_add, add_tmul, map_add, hy, hz]
  | ha x y hx hy => simp [smul_add, map_add, hx, hy]

end OuterRight

section Naturality

attribute [local instance 100] leftSMulCommClass rightSMulCommClass outerSMulCommClass

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

end TauCeti.BalancedTensorProduct
