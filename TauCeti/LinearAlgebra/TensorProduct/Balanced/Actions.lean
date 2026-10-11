/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Grading

/-!
# Outer actions on balanced tensor products

An action on either factor which commutes with the balancing action descends to the balanced
tensor product. Actions on opposite factors commute. These are the outer actions on the tensor
product of bimodules. They carry no Koszul sign: the left action acts on the first factor and the
right action on the second factor without crossing a tensor factor.

The module structures are explicit definitions rather than global instances, since a scalar
ring acting on both factors can give two different actions on the quotient.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

namespace TauCeti.BalancedTensorProduct

open MulOpposite

variable {k A M N : Type*} [CommRing k] [Semiring A]
  [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module A N]

section Left

variable (S : Type*) [Semiring S] [Module S M]
  [SMulCommClass S k M] [SMulCommClass S Aᵐᵒᵖ M]

private def leftAction (s : S) : Module.End k (BalancedTensorProduct k A M N) :=
  map (DistribSMul.toLinearMap k M s) LinearMap.id (fun a m ↦ smul_comm s (op a) m)
    (fun _ _ ↦ rfl)

private theorem leftAction_tmul (s : S) (m : M) (n : N) :
    leftAction S s (tmul k A m n) = tmul k A (s • m) n := by
  exact map_tmul (DistribSMul.toLinearMap k M s) LinearMap.id
    (fun a m ↦ smul_comm s (op a) m) (fun _ _ ↦ rfl) m n

private def leftActionHom : S →+* Module.End k (BalancedTensorProduct k A M N) where
  toFun := leftAction S
  map_zero' := hom_ext fun m n ↦ by simp [leftAction_tmul]
  map_one' := hom_ext fun m n ↦ by simp [leftAction_tmul]
  map_add' s t := hom_ext fun m n ↦ by simp [leftAction_tmul, add_smul, add_tmul]
  map_mul' s t := hom_ext fun m n ↦ by
    simp [Module.End.mul_apply, leftAction_tmul, mul_smul]

/-- The module structure induced by the outer action on the first factor. -/
@[instance_reducible]
def leftModule : Module S (BalancedTensorProduct k A M N) :=
  Module.compHom _ (leftActionHom (k := k) (A := A) (M := M) (N := N) S)

attribute [local instance 100] leftModule

private theorem smul_eq_leftAction (s : S) (z : BalancedTensorProduct k A M N) :
    s • z = leftAction S s z := (rfl)

/-- An outer left action applies to the first factor of a pure tensor. -/
@[simp]
theorem smul_tmul_left (s : S) (m : M) (n : N) :
    s • tmul k A m n = tmul k A (s • m) n := leftAction_tmul S s m n

/-- The outer left action commutes with the ground-ring action. -/
theorem leftSMulCommClass : SMulCommClass S k (BalancedTensorProduct k A M N) where
  smul_comm s r z := (leftAction S s).map_smul r z

/-- Compatibility of the outer left action with restriction to the ground ring. -/
theorem leftIsScalarTower [SMul k S] [IsScalarTower k S M] :
    IsScalarTower k S (BalancedTensorProduct k A M N) where
  smul_assoc r s z := by
    induction z using induction_on with
    | ht m n => simp [smul_assoc]
    | ha x y hx hy => simp [hx, hy]

section Map

variable {M' N' : Type*}
  [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [Module S M']
  [SMulCommClass S k M'] [SMulCommClass S Aᵐᵒᵖ M']
  [AddCommGroup N'] [Module k N'] [Module A N']

/-- Tensoring a map equivariant for the outer left action remains equivariant. -/
theorem map_smul_left (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n)
    (hfs : ∀ (s : S) m, f (s • m) = s • f m)
    (s : S) (z : BalancedTensorProduct k A M N) :
    map f g hf hg (s • z) = s • map f g hf hg z := by
  induction z using induction_on with
  | ht m n =>
    rw [smul_tmul_left, map_tmul _ _ hf hg, map_tmul _ _ hf hg, hfs, smul_tmul_left]
  | ha x y hx hy => simp only [smul_add, map_add, hx, hy]

end Map

section Lift

variable {P : Type*} [AddCommGroup P] [Module k P] [Module S P]

/-- A balanced bilinear map equivariant in the first factor induces a left-equivariant map. -/
@[simp]
theorem lift_smul_left (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (a : A) m n, f (op a • m) n = f m (a • n))
    (hfs : ∀ (s : S) m n, f (s • m) n = s • f m n)
    (s : S) (z : BalancedTensorProduct k A M N) :
    lift f hf (s • z) = s • lift f hf z := by
  induction z using induction_on with
  | ht m n => simp [hfs]
  | ha x y hx hy => simp only [smul_add, map_add, hx, hy]

end Lift

end Left

section Right

variable (T : Type*) [Semiring T] [Module T N]
  [SMulCommClass T k N] [SMulCommClass A T N]

private def rightAction (t : T) : Module.End k (BalancedTensorProduct k A M N) :=
  map LinearMap.id (DistribSMul.toLinearMap k N t) (fun _ _ ↦ rfl)
    (fun a n ↦ (smul_comm a t n).symm)

private theorem rightAction_tmul (t : T) (m : M) (n : N) :
    rightAction T t (tmul k A m n) = tmul k A m (t • n) := by
  exact map_tmul LinearMap.id (DistribSMul.toLinearMap k N t)
    (fun _ _ ↦ rfl) (fun a n ↦ (smul_comm a t n).symm) m n

private def rightActionHom : T →+* Module.End k (BalancedTensorProduct k A M N) where
  toFun := rightAction T
  map_zero' := hom_ext fun m n ↦ by simp [rightAction_tmul]
  map_one' := hom_ext fun m n ↦ by simp [rightAction_tmul]
  map_add' s t := hom_ext fun m n ↦ by simp [rightAction_tmul, add_smul, tmul_add]
  map_mul' s t := hom_ext fun m n ↦ by
    simp [Module.End.mul_apply, rightAction_tmul, mul_smul]

/-- The module structure induced by the outer action on the second factor. -/
@[instance_reducible]
def rightModule : Module T (BalancedTensorProduct k A M N) :=
  Module.compHom _ (rightActionHom (k := k) (A := A) (M := M) (N := N) T)

attribute [local instance 100] rightModule

private theorem smul_eq_rightAction (t : T) (z : BalancedTensorProduct k A M N) :
    t • z = rightAction T t z := (rfl)

/-- An outer right action applies to the second factor of a pure tensor. -/
@[simp]
theorem smul_tmul_right (t : T) (m : M) (n : N) :
    t • tmul k A m n = tmul k A m (t • n) := rightAction_tmul T t m n

/-- The outer right action commutes with the ground-ring action. -/
theorem rightSMulCommClass : SMulCommClass T k (BalancedTensorProduct k A M N) where
  smul_comm t r z := (rightAction T t).map_smul r z

/-- Compatibility of the outer right action with restriction to the ground ring. -/
theorem rightIsScalarTower [SMul k T] [IsScalarTower k T N] :
    IsScalarTower k T (BalancedTensorProduct k A M N) where
  smul_assoc r t z := by
    induction z using induction_on with
    | ht m n => simp [smul_assoc]
    | ha x y hx hy => simp [hx, hy]

section Map

variable {M' N' : Type*}
  [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M']
  [AddCommGroup N'] [Module k N'] [Module A N'] [Module T N']
  [SMulCommClass T k N'] [SMulCommClass A T N']

/-- Tensoring a map equivariant for the outer right action remains equivariant. -/
theorem map_smul_right (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n)
    (hgt : ∀ (t : T) n, g (t • n) = t • g n)
    (t : T) (z : BalancedTensorProduct k A M N) :
    map f g hf hg (t • z) = t • map f g hf hg z := by
  induction z using induction_on with
  | ht m n =>
    rw [smul_tmul_right, map_tmul _ _ hf hg, map_tmul _ _ hf hg, hgt, smul_tmul_right]
  | ha x y hx hy => simp only [smul_add, map_add, hx, hy]

end Map

section Lift

variable {P : Type*} [AddCommGroup P] [Module k P] [Module T P]

/-- A balanced bilinear map equivariant in the second factor induces a right-equivariant map. -/
@[simp]
theorem lift_smul_right (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (a : A) m n, f (op a • m) n = f m (a • n))
    (hfs : ∀ (s : T) m n, f m (s • n) = s • f m n)
    (s : T) (z : BalancedTensorProduct k A M N) :
    lift f hf (s • z) = s • lift f hf z := by
  induction z using induction_on with
  | ht m n => simp [hfs]
  | ha x y hx hy => simp only [smul_add, map_add, hx, hy]

end Lift

end Right

/-- Actions on different factors of a balanced tensor product commute. -/
theorem outerSMulCommClass (S T : Type*) [Semiring S] [Semiring T]
    [Module S M] [Module T N] [SMulCommClass S k M] [SMulCommClass T k N]
    [SMulCommClass S Aᵐᵒᵖ M] [SMulCommClass A T N] :
    letI := leftModule (k := k) (A := A) (M := M) (N := N) S
    letI := rightModule (k := k) (A := A) (M := M) (N := N) T
    SMulCommClass S T (BalancedTensorProduct k A M N) := by
  let _ := leftModule (k := k) (A := A) (M := M) (N := N) S
  let _ := rightModule (k := k) (A := A) (M := M) (N := N) T
  refine ⟨fun s t z ↦ ?_⟩
  induction z using induction_on with
  | ht m n => simp
  | ha x y hx hy => simp [hx, hy]

section Grading

variable [Algebra k A] {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  (G : InternalGrading k M) (H : InternalGrading k N)
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece G.piece]
  [SetLike.GradedSMul 𝒜 H.piece]

/-- A graded outer action on the first factor adds degrees on the balanced tensor product. -/
theorem gradedSMul_left (S : Type*) [Semiring S] [Module k S] [Module S M]
    [SMulCommClass S k M] [SMulCommClass S Aᵐᵒᵖ M]
    (𝒮 : ℤ → Submodule k S) [SetLike.GradedSMul 𝒮 G.piece] :
    letI := leftModule (k := k) (A := A) (M := M) (N := N) S
    SetLike.GradedSMul 𝒮 (grading (𝒜 := 𝒜) G H).piece := by
  let _ := leftModule (k := k) (A := A) (M := M) (N := N) S
  refine ⟨fun {p q} {s z} hs hz ↦ ?_⟩
  have hf : LinearMap.IsHomogeneous (DistribSMul.toLinearMap k M s) G.piece G.piece p :=
    LinearMap.isHomogeneous_def.2 fun r x hx ↦ by
      simpa only [DistribSMul.toLinearMap_apply, add_comm, vadd_eq_add] using
        SetLike.GradedSMul.smul_mem hs hx
  have h := isHomogeneous_map (𝒜 := 𝒜) G H G H
    (DistribSMul.toLinearMap k M s) LinearMap.id
    (fun a m ↦ smul_comm s (op a) m) (fun _ _ ↦ rfl) hf
    (LinearMap.isHomogeneous_id H.piece)
  simpa only [smul_eq_leftAction, leftAction, add_zero, add_comm, vadd_eq_add]
    using h.map_mem hz

/-- A graded outer action on the second factor adds degrees on the balanced tensor product. -/
theorem gradedSMul_right (T : Type*) [Semiring T] [Module k T] [Module T N]
    [SMulCommClass T k N] [SMulCommClass A T N]
    (𝒯 : ℤ → Submodule k T) [SetLike.GradedSMul 𝒯 H.piece] :
    letI := rightModule (k := k) (A := A) (M := M) (N := N) T
    SetLike.GradedSMul 𝒯 (grading (𝒜 := 𝒜) G H).piece := by
  let _ := rightModule (k := k) (A := A) (M := M) (N := N) T
  refine ⟨fun {p q} {t z} ht hz ↦ ?_⟩
  have hg : LinearMap.IsHomogeneous (DistribSMul.toLinearMap k N t) H.piece H.piece p :=
    LinearMap.isHomogeneous_def.2 fun r x hx ↦ by
      simpa only [DistribSMul.toLinearMap_apply, add_comm, vadd_eq_add] using
        SetLike.GradedSMul.smul_mem ht hx
  have h := isHomogeneous_map (𝒜 := 𝒜) G H G H
    LinearMap.id (DistribSMul.toLinearMap k N t)
    (fun _ _ ↦ rfl) (fun a n ↦ (smul_comm a t n).symm)
    (LinearMap.isHomogeneous_id G.piece) hg
  simpa only [smul_eq_rightAction, rightAction, zero_add, add_zero, add_comm, vadd_eq_add]
    using h.map_mem hz

end Grading

end TauCeti.BalancedTensorProduct
