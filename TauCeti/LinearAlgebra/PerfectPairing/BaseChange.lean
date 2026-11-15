/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-!
# Extension of scalars of a pairing

A bilinear pairing `p : M →ₗ[R] N →ₗ[R] R` extends along an `R`-algebra `S` to an `S`-bilinear
pairing of `S ⊗[R] M` with `S ⊗[R] N`, determined by

```text
(a ⊗ m, b ⊗ n) ↦ a * b * p m n.
```

When one side is finite and free, extension of scalars preserves perfectness. The point is that the
dual of a finite free module commutes with base change (`IsBaseChange.toDualBaseChange`), so the
extended pairing is the base change of the equivalence `M ≃ Dual R N` followed by that
identification. Over a field this is the usual statement that a nondegenerate pairing of
finite-dimensional spaces stays nondegenerate after extending the field; over `ℤ` it makes the
rational scalar extension of a root datum a root pairing over `ℚ`.

When `M = N`, the extended pairing is Mathlib's `LinearMap.BilinForm.baseChange`
(`LinearMap.BilinForm.baseChange_eq_baseChangePairing`); the construction here allows the two
sides to differ, as they do for the weights and coweights of a root pairing.

## Main definitions

* `LinearMap.baseChangePairing`: the extension of scalars of a pairing along an `R`-algebra `S`.

## Main results

* `LinearMap.baseChangePairing_tmul_tmul`: the extended pairing on pure tensors.
* `LinearMap.flip_baseChangePairing`: extending scalars commutes with swapping the two sides.
* `LinearMap.BilinForm.baseChange_eq_baseChangePairing`: for a bilinear form, the extended
  pairing is the base change of the form.
* `LinearMap.bijective_baseChangePairing`: if `p` is bijective onto `Dual R N` and `N` is finite
  and free, then the extended pairing is bijective onto `Dual S (S ⊗[R] N)`.
* `LinearMap.tensorProduct_mk_injective_of_injective`: for a faithful algebra `S`, the map
  `m ↦ 1 ⊗ m` is injective on the nondegenerate side of a pairing.
* `LinearMap.isPerfPair_baseChangePairing`: the extension of a perfect pairing with a finite free
  side is perfect.
-/

public section

open Module TensorProduct

namespace LinearMap

variable {R M N : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The extension of scalars of a pairing `p : M × N → R` along an `R`-algebra `S`: the
`S`-bilinear pairing of `S ⊗[R] M` with `S ⊗[R] N` sending `(a ⊗ m, b ⊗ n)` to `a * b * p m n`. -/
noncomputable def baseChangePairing (p : M →ₗ[R] N →ₗ[R] R) :
    S ⊗[R] M →ₗ[S] S ⊗[R] N →ₗ[S] S :=
  (Dual.baseChange S ∘ₗ p).liftBaseChange S

variable (p : M →ₗ[R] N →ₗ[R] R)

@[simp]
theorem baseChangePairing_tmul_tmul (a b : S) (m : M) (n : N) :
    p.baseChangePairing S (a ⊗ₜ m) (b ⊗ₜ n) = a * b * algebraMap R S (p m n) := by
  simp [baseChangePairing, Algebra.smul_def]
  ring

/-- Extending scalars commutes with swapping the two sides of a pairing. -/
theorem flip_baseChangePairing :
    (p.baseChangePairing S).flip = p.flip.baseChangePairing S := by
  refine TensorProduct.AlgebraTensorModule.ext fun b n ↦ ?_
  refine TensorProduct.AlgebraTensorModule.ext fun a m ↦ ?_
  simp [mul_comm]

/-- If `p` is injective on the left and `algebraMap R S` is injective, then so is `m ↦ 1 ⊗ m`:
the extended pairing sends `(1 ⊗ m, 1 ⊗ n)` to the image of `p m n`. -/
theorem tensorProduct_mk_injective_of_injective [FaithfulSMul R S] (hp : Function.Injective p) :
    Function.Injective (TensorProduct.mk R S M 1) := by
  refine fun m m' h ↦ hp (LinearMap.ext fun n ↦ FaithfulSMul.algebraMap_injective R S ?_)
  simpa using congr($(congrArg (p.baseChangePairing S) h) (1 ⊗ₜ n))

/-- On the `M`-side, the extended pairing is the base change of `p`, viewed as a map into
`Dual R N`, followed by the identification of `S ⊗[R] Dual R N` with `Dual S (S ⊗[R] N)`. -/
theorem baseChangePairing_eq_toDualBaseChange_comp [Free R N] [Module.Finite R N] :
    p.baseChangePairing S =
      ((TensorProduct.isBaseChange R N S).toDualBaseChange.toLinearMap ∘ₗ p.baseChange S) := by
  refine TensorProduct.AlgebraTensorModule.ext fun a m ↦ ?_
  refine (TensorProduct.isBaseChange R N S).algHom_ext _ _ fun n ↦ ?_
  simpa using ((TensorProduct.isBaseChange R N S).toDualBaseChange_tmul a (p m) n).symm

/-- If `p` identifies `M` with `Dual R N` and `N` is finite and free, then the extended pairing
identifies `S ⊗[R] M` with `Dual S (S ⊗[R] N)`. -/
theorem bijective_baseChangePairing [Free R N] [Module.Finite R N]
    (hp : Function.Bijective p) : Function.Bijective (p.baseChangePairing S) := by
  rw [baseChangePairing_eq_toDualBaseChange_comp]
  exact (TensorProduct.isBaseChange R N S).toDualBaseChange.bijective.comp
    ((LinearEquiv.ofBijective p hp).baseChange R S _ _).bijective

/-- **Extension of scalars preserves perfect pairings.** If `p` is perfect and `N` is finite and
free, then the extended pairing of `S ⊗[R] M` with `S ⊗[R] N` is perfect over `S`. (The module `M`
is then finite and free too, being isomorphic to `Dual R N`.) -/
instance isPerfPair_baseChangePairing [p.IsPerfPair] [Free R N] [Module.Finite R N] :
    (p.baseChangePairing S).IsPerfPair := by
  have : Free R M := .of_equiv p.toPerfPair.symm
  have : Module.Finite R M := .equiv p.toPerfPair.symm
  refine ⟨p.bijective_baseChangePairing S (IsPerfPair.bijective_left p), ?_⟩
  rw [flip_baseChangePairing]
  exact p.flip.bijective_baseChangePairing S (IsPerfPair.bijective_right p)

/-- For a bilinear form, the extended pairing is the base change of the form. -/
theorem BilinForm.baseChange_eq_baseChangePairing (B : LinearMap.BilinForm R M) :
    B.baseChange S = B.baseChangePairing S := by
  refine TensorProduct.AlgebraTensorModule.ext fun a m ↦ ?_
  refine TensorProduct.AlgebraTensorModule.ext fun b n ↦ ?_
  simp [Algebra.smul_def, mul_comm]

end LinearMap
