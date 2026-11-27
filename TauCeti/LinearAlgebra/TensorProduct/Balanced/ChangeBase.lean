/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Actions

/-!
# Changing the ground ring of a balanced tensor product

For an `S`-algebra `A` and a map of commutative ground rings `R → S`, compatible actions on
the factors give two balanced tensor products over `A`. The one formed using `R` is canonically
the restriction of scalars of the one formed using `S`. In particular the underlying abelian group
can be computed with ground ring `ℤ`.

The balancing identity for the image of `s : S` in `A` identifies the two induced `S`-actions on
pure tensors. This makes the pure tensor map over `R` bilinear over `S` once its target takes the
outer action from the first factor.

## References

* S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IX.6, p. 226,
  for the description of the tensor product over an arbitrary ring by additive balancing.
-/

public section

namespace TauCeti.BalancedTensorProduct

open MulOpposite

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  {A M N : Type*} [Semiring A]
  [AddCommGroup M] [Module R M] [Module S M] [Module Aᵐᵒᵖ M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [Module A N] [IsScalarTower R S N]

private def changeBaseForward :
    BalancedTensorProduct R A M N →ₗ[R]
      RestrictScalars R S (BalancedTensorProduct S A M N) := by
  letI := Module.restrictScalars R S (BalancedTensorProduct S A M N)
  letI := IsScalarTower.restrictScalars R S (BalancedTensorProduct S A M N)
  let f : M →ₗ[R] N →ₗ[R] BalancedTensorProduct S A M N :=
    (LinearMap.restrictScalarsₗ R S N (BalancedTensorProduct S A M N) R).comp
      ((mk S A).restrictScalars R)
  let g : BalancedTensorProduct R A M N →ₗ[R] BalancedTensorProduct S A M N :=
    lift f (fun a m n ↦ by simp only [f, LinearMap.comp_apply, LinearMap.restrictScalarsₗ_apply,
      LinearMap.restrictScalars_apply, mk_apply, balance])
  -- The restricted action on the underlying tensor agrees with the instance on the synonym.
  exact g

private theorem changeBaseForward_tmul (m : M) (n : N) :
    changeBaseForward (A := A) R S (tmul R A m n) =
      (RestrictScalars.addEquiv R S _).symm (tmul S A m n) := by
  let := Module.restrictScalars R S (BalancedTensorProduct S A M N)
  simp only [changeBaseForward]
  exact (lift_tmul (P := BalancedTensorProduct S A M N) _ _ m n).trans (mk_apply S A m n)

variable [Algebra S A] [IsScalarTower S Aᵐᵒᵖ M] [IsScalarTower S A N]

omit [Algebra R S] [IsScalarTower R S M] [IsScalarTower R S N] in
private theorem changeBase_balance (s : S) (m : M) (n : N) :
    tmul R A (s • m) n = tmul R A m (s • n) := by
  simpa only [← MulOpposite.algebraMap_apply, algebraMap_smul] using
    balance R A (algebraMap S A s) m n

attribute [local instance] RestrictScalars.moduleOrig in
private def changeBaseInverse :
    RestrictScalars R S (BalancedTensorProduct S A M N) →ₗ[R] BalancedTensorProduct R A M N := by
  letI := leftModule (k := R) (A := A) (M := M) (N := N) S
  letI := leftIsScalarTower (k := R) (A := A) (M := M) (N := N) S
  let f : M →ₗ[S] N →ₗ[S] BalancedTensorProduct R A M N :=
    LinearMap.mk₂ S (tmul R A) (add_tmul R A)
      (fun s m n ↦ (smul_tmul_left S s m n).symm) (tmul_add R A)
      (fun s m n ↦ (changeBase_balance R S s m n).symm.trans (smul_tmul_left S s m n).symm)
  let g : RestrictScalars R S (BalancedTensorProduct S A M N) →ₗ[S]
      BalancedTensorProduct R A M N :=
    lift f (fun a m n ↦ by simp only [f, LinearMap.mk₂_apply, balance])
  exact g.restrictScalars R

omit [IsScalarTower R S N] in
private theorem changeBaseInverse_tmul (m : M) (n : N) :
    changeBaseInverse (A := A) R S ((RestrictScalars.addEquiv R S _).symm (tmul S A m n)) =
      tmul R A m n := by
  let := leftModule (k := R) (A := A) (M := M) (N := N) S
  simp only [changeBaseInverse]
  exact (lift_tmul _ _ m n).trans (LinearMap.mk₂_apply S _ m n)

/-- Changing the ground ring along `R → S` identifies the two balanced tensor products over `A`
by an `R`-linear equivalence. It sends a pure tensor to the pure tensor of the same factors. -/
def changeBaseLinearEquiv : BalancedTensorProduct R A M N ≃ₗ[R]
    RestrictScalars R S (BalancedTensorProduct S A M N) :=
  LinearEquiv.ofLinearMap (changeBaseForward R S) (changeBaseInverse R S) (by
    ext z
    -- The domain is the restricted module, so use induction on the corresponding S-tensor.
    obtain ⟨x, rfl⟩ := (RestrictScalars.addEquiv R S _).symm.surjective z
    induction x using induction_on with
    | ht m n => simp [changeBaseInverse_tmul, changeBaseForward_tmul]
    | ha x y hx hy => simp only [map_add, hx, hy])
    (hom_ext fun m n ↦ by simp [changeBaseForward_tmul, changeBaseInverse_tmul])

/-- The ground-ring comparison preserves pure tensors. -/
@[simp]
theorem changeBaseLinearEquiv_tmul (m : M) (n : N) :
    changeBaseLinearEquiv (A := A) R S (tmul R A m n) =
      (RestrictScalars.addEquiv R S _).symm (tmul S A m n) :=
  changeBaseForward_tmul R S m n

/-- The inverse ground-ring comparison preserves pure tensors. -/
@[simp]
theorem changeBaseLinearEquiv_symm_tmul (m : M) (n : N) :
    (changeBaseLinearEquiv (A := A) R S).symm
      ((RestrictScalars.addEquiv R S _).symm (tmul S A m n)) = tmul R A m n :=
  changeBaseInverse_tmul R S m n

/-- Changing the ground ring along `R → S` preserves the underlying additive group. -/
def changeBaseAddEquiv : BalancedTensorProduct R A M N ≃+ BalancedTensorProduct S A M N :=
  (changeBaseLinearEquiv R S).toAddEquiv.trans (RestrictScalars.addEquiv R S _)

/-- The additive ground-ring comparison preserves pure tensors. -/
@[simp]
theorem changeBaseAddEquiv_tmul (m : M) (n : N) :
    changeBaseAddEquiv (A := A) R S (tmul R A m n) = tmul S A m n := by
  simp [changeBaseAddEquiv]

/-- The inverse additive ground-ring comparison preserves pure tensors. -/
@[simp]
theorem changeBaseAddEquiv_symm_tmul (m : M) (n : N) :
    (changeBaseAddEquiv (A := A) R S).symm (tmul S A m n) = tmul R A m n :=
  (changeBaseAddEquiv R S).symm_apply_eq.mpr (changeBaseAddEquiv_tmul R S m n).symm

section Naturality

variable {M' N' : Type*}
  [AddCommGroup M'] [Module R M'] [Module S M'] [Module Aᵐᵒᵖ M']
  [IsScalarTower R S M'] [IsScalarTower S Aᵐᵒᵖ M']
  [AddCommGroup N'] [Module R N'] [Module S N'] [Module A N']
  [IsScalarTower R S N'] [IsScalarTower S A N']

/-- The additive ground-ring comparison commutes with tensoring equivariant maps. -/
theorem changeBaseAddEquiv_map (f : M →ₗ[S] M') (g : N →ₗ[S] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n) (z : BalancedTensorProduct R A M N) :
    changeBaseAddEquiv R S (map (f.restrictScalars R) (g.restrictScalars R) hf hg z) =
      map f g hf hg (changeBaseAddEquiv R S z) := by
  induction z using induction_on with
  | ht m n =>
    rw [map_tmul (k := R) (f.restrictScalars R) (g.restrictScalars R) hf hg]
    simp only [changeBaseAddEquiv_tmul, LinearMap.restrictScalars_apply, map_tmul]
  | ha x y hx hy => simp only [map_add, hx, hy]

end Naturality

end TauCeti.BalancedTensorProduct
