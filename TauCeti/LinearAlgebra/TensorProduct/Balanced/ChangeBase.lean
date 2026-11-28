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

private def changeBaseRestrictScalars :
    letI := Module.restrictScalars R S (BalancedTensorProduct S A M N)
    RestrictScalars R S (BalancedTensorProduct S A M N) ≃ₗ[R] BalancedTensorProduct S A M N := by
  letI := Module.restrictScalars R S (BalancedTensorProduct S A M N)
  exact { RestrictScalars.addEquiv R S _ with
    map_smul' := RestrictScalars.addEquiv_map_smul R S _ }

omit [Module R M] [IsScalarTower R S M] [Module R N] [IsScalarTower R S N] in
private theorem changeBaseRestrictScalars_apply
    (x : RestrictScalars R S (BalancedTensorProduct S A M N)) :
    changeBaseRestrictScalars R S x = RestrictScalars.addEquiv R S _ x := rfl

omit [Module R M] [IsScalarTower R S M] [Module R N] [IsScalarTower R S N] in
private theorem changeBaseRestrictScalars_symm_apply (x : BalancedTensorProduct S A M N) :
    (changeBaseRestrictScalars R S).symm x = (RestrictScalars.addEquiv R S _).symm x := rfl

private def changeBaseForward :
    BalancedTensorProduct R A M N →ₗ[R]
      RestrictScalars R S (BalancedTensorProduct S A M N) := by
  letI := Module.restrictScalars R S (BalancedTensorProduct S A M N)
  letI := IsScalarTower.restrictScalars R S (BalancedTensorProduct S A M N)
  let f : M →ₗ[R] N →ₗ[R] BalancedTensorProduct S A M N :=
    (LinearMap.restrictScalarsₗ R S N (BalancedTensorProduct S A M N) R).comp
      ((mk S A).restrictScalars R)
  exact (changeBaseRestrictScalars R S).symm.toLinearMap.comp
    (lift f (fun a m n ↦ by simp only [f, LinearMap.comp_apply, LinearMap.restrictScalarsₗ_apply,
      LinearMap.restrictScalars_apply, mk_apply, balance]))

variable [Algebra S A] [IsScalarTower S Aᵐᵒᵖ M] [IsScalarTower S A N]

omit [Algebra R S] [IsScalarTower R S M] [IsScalarTower R S N] in
private theorem changeBase_balance (s : S) (m : M) (n : N) :
    tmul R A (s • m) n = tmul R A m (s • n) := by
  simpa only [← MulOpposite.algebraMap_apply, algebraMap_smul] using
    balance R A (algebraMap S A s) m n

private def changeBaseInverse :
    RestrictScalars R S (BalancedTensorProduct S A M N) →ₗ[R] BalancedTensorProduct R A M N := by
  letI := Module.restrictScalars R S (BalancedTensorProduct S A M N)
  letI := IsScalarTower.restrictScalars R S (BalancedTensorProduct S A M N)
  letI := leftModule (k := R) (A := A) (M := M) (N := N) S
  letI := leftIsScalarTower (k := R) (A := A) (M := M) (N := N) S
  let f : M →ₗ[S] N →ₗ[S] BalancedTensorProduct R A M N :=
    LinearMap.mk₂ S (tmul R A) (add_tmul R A)
      (fun s m n ↦ (smul_tmul_left S s m n).symm) (tmul_add R A)
      (fun s m n ↦ (changeBase_balance R S s m n).symm.trans (smul_tmul_left S s m n).symm)
  let g : BalancedTensorProduct S A M N →ₗ[S] BalancedTensorProduct R A M N :=
    lift f (fun a m n ↦ by simp only [f, LinearMap.mk₂_apply, balance])
  exact (g.restrictScalars R).comp (changeBaseRestrictScalars R S).toLinearMap

/-- Changing the ground ring along `R → S` identifies the two balanced tensor products over `A`
by an `R`-linear equivalence. It sends a pure tensor to the pure tensor of the same factors. -/
def changeBaseLinearEquiv : BalancedTensorProduct R A M N ≃ₗ[R]
    RestrictScalars R S (BalancedTensorProduct S A M N) := by
  letI := leftModule (k := R) (A := A) (M := M) (N := N) S
  letI := Module.restrictScalars R S (BalancedTensorProduct S A M N)
  have inverse_tmul (m : M) (n : N) :
      changeBaseInverse R S ((RestrictScalars.addEquiv R S _).symm (tmul S A m n)) =
        tmul R A m n := by
    simp only [changeBaseInverse, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_coe, changeBaseRestrictScalars_apply, AddEquiv.apply_symm_apply]
    exact (lift_tmul _ _ m n).trans (LinearMap.mk₂_apply S _ m n)
  refine LinearEquiv.ofLinearMap (changeBaseForward R S) (changeBaseInverse R S) ?_ ?_
  · ext z
    -- The domain is the restricted module, so use induction on the corresponding S-tensor.
    obtain ⟨x, rfl⟩ := (RestrictScalars.addEquiv R S _).symm.surjective z
    induction x using induction_on with
    | ht m n =>
      simp [inverse_tmul, changeBaseForward, changeBaseRestrictScalars_symm_apply, mk_apply]
    | ha x y hx hy => simp only [map_add, hx, hy]
  · refine hom_ext fun m n ↦ ?_
    simp [inverse_tmul, changeBaseForward, changeBaseRestrictScalars_symm_apply, mk_apply]

/-- The ground-ring comparison preserves pure tensors. -/
@[simp]
theorem changeBaseLinearEquiv_tmul (m : M) (n : N) :
    changeBaseLinearEquiv (A := A) R S (tmul R A m n) =
      (RestrictScalars.addEquiv R S _).symm (tmul S A m n) := by
  let := Module.restrictScalars R S (BalancedTensorProduct S A M N)
  simp [changeBaseLinearEquiv, changeBaseForward, changeBaseRestrictScalars_symm_apply, mk_apply]

/-- The inverse ground-ring comparison preserves pure tensors. -/
@[simp]
theorem changeBaseLinearEquiv_symm_tmul (m : M) (n : N) :
    (changeBaseLinearEquiv (A := A) R S).symm
      ((RestrictScalars.addEquiv R S _).symm (tmul S A m n)) = tmul R A m n :=
  (changeBaseLinearEquiv R S).symm_apply_eq.mpr (changeBaseLinearEquiv_tmul R S m n).symm

section Naturality

variable {M' N' : Type*}
  [AddCommGroup M'] [Module R M'] [Module S M'] [Module Aᵐᵒᵖ M']
  [IsScalarTower R S M'] [IsScalarTower S Aᵐᵒᵖ M']
  [AddCommGroup N'] [Module R N'] [Module S N'] [Module A N']
  [IsScalarTower R S N'] [IsScalarTower S A N']

/-- The ground-ring comparison commutes with tensoring equivariant maps as an equality of
`R`-linear maps. On the `S`-side the tensor map is restricted to `R`. -/
theorem changeBaseLinearEquiv_map (f : M →ₗ[S] M') (g : N →ₗ[S] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n) :
    letI := RestrictScalars.moduleOrig R S (BalancedTensorProduct S A M N)
    letI := RestrictScalars.moduleOrig R S (BalancedTensorProduct S A M' N')
    let mapS : RestrictScalars R S (BalancedTensorProduct S A M N) →ₗ[S]
        RestrictScalars R S (BalancedTensorProduct S A M' N') := map f g hf hg
    (changeBaseLinearEquiv R S).toLinearMap.comp
        (map (f.restrictScalars R) (g.restrictScalars R) hf hg) =
      (mapS.restrictScalars R).comp (changeBaseLinearEquiv R S).toLinearMap := by
  dsimp only
  refine LinearMap.ext fun z ↦ ?_
  induction z using induction_on with
  | ht m n =>
    -- The scalar restriction uses the same function on the two type synonyms.
    let mapS : RestrictScalars R S (BalancedTensorProduct S A M N) →
        RestrictScalars R S (BalancedTensorProduct S A M' N') := map f g hf hg
    have hR := map_tmul (k := R) (f.restrictScalars R) (g.restrictScalars R) hf hg m n
    calc
      _ = changeBaseLinearEquiv R S (tmul R A (f m) (g n)) :=
        congrArg (changeBaseLinearEquiv R S) hR
      _ = (RestrictScalars.addEquiv R S _).symm (tmul S A (f m) (g n)) :=
        changeBaseLinearEquiv_tmul R S (f m) (g n)
      _ = mapS ((RestrictScalars.addEquiv R S _).symm (tmul S A m n)) :=
        congrArg (RestrictScalars.addEquiv R S _).symm (map_tmul f g hf hg m n).symm
      _ = _ := congrArg mapS (changeBaseLinearEquiv_tmul R S m n).symm
  | ha x y hx hy => simp only [map_add, hx, hy]

/-- On the underlying additive groups the ground-ring comparison commutes with tensoring
equivariant maps. -/
theorem changeBaseAddEquiv_map (f : M →ₗ[S] M') (g : N →ₗ[S] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n) (z : BalancedTensorProduct R A M N) :
    ((changeBaseLinearEquiv R S).toAddEquiv.trans (RestrictScalars.addEquiv R S _))
        (map (f.restrictScalars R) (g.restrictScalars R) hf hg z) =
      map f g hf hg (((changeBaseLinearEquiv R S).toAddEquiv.trans
        (RestrictScalars.addEquiv R S _)) z) := by
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply]
  have h := LinearMap.congr_fun (changeBaseLinearEquiv_map R S f g hf hg) z
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  simpa only [LinearEquiv.coe_toAddEquiv, RestrictScalars.addEquiv, AddEquiv.refl_apply] using!
    congrArg (RestrictScalars.addEquiv R S _) h

end Naturality

end TauCeti.BalancedTensorProduct
