/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Multilinear.Curry
public import TauCeti.RingTheory.HochschildCohomology.Coboundary
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Hochschild cochains with coefficients in the dual bimodule

Let `A` be an algebra over a commutative semiring `R` and `N` an `R`-module. The linear maps
`A →ₗ[R] N` form an `A`-bimodule under `(x • f) y = f (y * x)` and `(op x • f) y = f (x * y)`.
For `N = R` this is the algebraic dual `A*` with `(x φ x') y = φ (x' y x)`. Whenever `N` is
itself an `A`-module, `A →ₗ[R] N` also carries the pointwise action `(x • f) y = x • f y`, so
the dual actions are scoped instances in `TauCeti.DualBimodule`, as for Mathlib's
`TensorProduct.RightActions`.

Currying the first argument (`TauCeti.multilinearCurryFirstEquiv`) identifies the `N`-valued
cochains in `n + 1` arguments, the degree-`n` cochains on which the Hochschild coboundary `b` of
`TauCeti.RingTheory.CyclicCohomology.Cochain` acts, with the `(A →ₗ[R] N)`-valued cochains in `n`
arguments. Under this identification `b` is the coboundary `δ` with coefficients in the dual
bimodule: the face multiplying `a₀ a₁` is the left action of `a₁`, and the cyclic face
`(aₙ₊₁ a₀, a₁, …, aₙ)` is the right action of `aₙ₊₁`. Thus the cochain complex underlying cyclic
cohomology is the Hochschild complex of `A` with coefficients in its dual.

## Main results

* `TauCeti.hochschildBimoduleCoface_multilinearCurryFirstEquiv`: each coface with coefficients
  in the dual bimodule is the corresponding Hochschild coface of the uncurried cochain.
* `TauCeti.multilinearCurryFirstEquiv_hochschildCoboundary`: currying intertwines `b` and `δ`.
* `TauCeti.hochschildCoboundary_multilinearCurryFirstEquiv_symm`: the same comparison read in
  the other direction.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §§1.5, 2.1.
-/

public section

open MulOpposite

namespace TauCeti

namespace DualBimodule

variable {R A N : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid N]
  [Module R N]

/-- The left action `(x • f) y = f (y * x)` of `A` on linear maps out of `A`. -/
scoped instance instSMul : SMul A (A →ₗ[R] N) :=
  ⟨fun x f ↦ f ∘ₗ LinearMap.mulRight R x⟩

/-- The right action `(op x • f) y = f (x * y)` of `A` on linear maps out of `A`. -/
scoped instance instSMulOp : SMul Aᵐᵒᵖ (A →ₗ[R] N) :=
  ⟨fun x f ↦ f ∘ₗ LinearMap.mulLeft R x.unop⟩

/-- The left action of the dual bimodule precomposes with right multiplication. -/
@[simp]
theorem smul_linearMap_apply (x : A) (f : A →ₗ[R] N) (y : A) : (x • f) y = f (y * x) :=
  rfl

/-- The right action of the dual bimodule precomposes with left multiplication. -/
@[simp]
theorem op_smul_linearMap_apply (x : Aᵐᵒᵖ) (f : A →ₗ[R] N) (y : A) :
    (x • f) y = f (x.unop * y) :=
  rfl

/-- Linear maps out of `A` form a left `A`-module under `(x • f) y = f (y * x)`. -/
scoped instance instModule : Module A (A →ₗ[R] N) where
  one_smul f := LinearMap.ext fun y ↦ by simp
  mul_smul x x' f := LinearMap.ext fun y ↦ by simp [mul_assoc]
  smul_zero x := rfl
  smul_add x f g := rfl
  add_smul x x' f := LinearMap.ext fun y ↦ by simp [mul_add]
  zero_smul f := LinearMap.ext fun y ↦ by simp

/-- Linear maps out of `A` form a left `Aᵐᵒᵖ`-module under `(op x • f) y = f (x * y)`. -/
scoped instance instModuleOp : Module Aᵐᵒᵖ (A →ₗ[R] N) where
  one_smul f := LinearMap.ext fun y ↦ by simp
  mul_smul x x' f := LinearMap.ext fun y ↦ by simp [mul_assoc]
  smul_zero x := rfl
  smul_add x f g := rfl
  add_smul x x' f := LinearMap.ext fun y ↦ by simp [add_mul]
  zero_smul f := LinearMap.ext fun y ↦ by simp

/-- The two actions of the dual bimodule commute. -/
scoped instance instSMulCommClass : SMulCommClass A Aᵐᵒᵖ (A →ₗ[R] N) :=
  ⟨fun x x' f ↦ LinearMap.ext fun y ↦ by simp [mul_assoc]⟩

/-- The left action of the dual bimodule is `R`-linear. -/
scoped instance instIsScalarTower : IsScalarTower R A (A →ₗ[R] N) :=
  ⟨fun r x f ↦ LinearMap.ext fun y ↦ by simp⟩

/-- The right action of the dual bimodule is `R`-linear. -/
scoped instance instIsScalarTowerOp : IsScalarTower R Aᵐᵒᵖ (A →ₗ[R] N) :=
  ⟨fun r x f ↦ LinearMap.ext fun y ↦ by simp⟩

end DualBimodule

open DualBimodule

variable {R A N : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [AddCommGroup N]
  [Module R N] {n : ℕ}

/-- Each coface with coefficients in the dual bimodule is the corresponding Hochschild coface of
the uncurried cochain. -/
theorem hochschildBimoduleCoface_multilinearCurryFirstEquiv (i : Fin (n + 2))
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) N) (a : Fin (n + 1) → A) (x : A) :
    hochschildBimoduleCoface R A (A →ₗ[R] N) i
        (multilinearCurryFirstEquiv R (fun _ : Fin (n + 1) ↦ A) N φ) a x =
      φ (hochschildFace i (Fin.cons x a)) := by
  induction i using Fin.cases with
  | zero =>
    rw [hochschildBimoduleCoface_zero_apply, smul_linearMap_apply,
      multilinearCurryFirstEquiv_apply_apply,
      ← Fin.castSucc_zero (n := n + 1), hochschildFace_castSucc, Fin.castSucc_zero (n := n + 1),
      Fin.contractNth_zero_cons]
  | succ i =>
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, hochschildBimoduleCoface_last_apply, op_smul_linearMap_apply, unop_op,
        multilinearCurryFirstEquiv_apply_apply, hochschildFace_last, ← Fin.succ_last,
        Fin.cons_succ, Fin.cons_zero]
      simp only [Fin.init_def, Fin.cons_succ]
    | cast j =>
      rw [hochschildBimoduleCoface_castSucc_succ_apply, multilinearCurryFirstEquiv_apply_apply,
        Fin.succ_castSucc, hochschildFace_castSucc, ← Fin.succ_castSucc,
        Fin.contractNth_succ_cons]

/-- Under currying of the first argument, the Hochschild coboundary `b` of `N`-valued cochains
is the Hochschild coboundary `δ` with coefficients in the dual bimodule `A →ₗ[R] N`. -/
theorem multilinearCurryFirstEquiv_hochschildCoboundary
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) N) :
    multilinearCurryFirstEquiv R (fun _ : Fin (n + 2) ↦ A) N (hochschildCoboundary R A N n φ) =
      hochschildBimoduleCoboundary R A (A →ₗ[R] N) n
        (multilinearCurryFirstEquiv R (fun _ : Fin (n + 1) ↦ A) N φ) := by
  ext a x
  rw [multilinearCurryFirstEquiv_apply_apply, hochschildCoboundary_apply,
    hochschildBimoduleCoboundary_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, hochschildBimoduleCoface_multilinearCurryFirstEquiv]

/-- Uncurrying the first argument turns the Hochschild coboundary `δ` with coefficients in the
dual bimodule into the Hochschild coboundary `b` of `N`-valued cochains. -/
theorem hochschildCoboundary_multilinearCurryFirstEquiv_symm
    (ψ : MultilinearMap R (fun _ : Fin n ↦ A) (A →ₗ[R] N)) :
    hochschildCoboundary R A N n
        ((multilinearCurryFirstEquiv R (fun _ : Fin (n + 1) ↦ A) N).symm ψ) =
      (multilinearCurryFirstEquiv R (fun _ : Fin (n + 2) ↦ A) N).symm
        (hochschildBimoduleCoboundary R A (A →ₗ[R] N) n ψ) := by
  rw [LinearEquiv.eq_symm_apply, multilinearCurryFirstEquiv_hochschildCoboundary,
    LinearEquiv.apply_symm_apply]

end TauCeti
