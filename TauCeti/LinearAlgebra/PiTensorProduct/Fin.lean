/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Splitting off the initial factor of a `Fin`-indexed tensor product

A tensor product of `n + 1` modules indexed by `Fin (n + 1)` splits off its initial factor `M 0`
along `Fin.cons` and `Fin.tail`:

```text
⨂ᵢ Mᵢ ≃ M 0 ⊗ (⨂ᵢ M (i.succ)),     ⨂ₜ mᵢ ↦ m 0 ⊗ₜ (⨂ₜ m (i.succ)).
```

This is the `Fin`-indexed counterpart of `PiTensorProduct.optionEquiv`, built directly from
`LinearMap.uncurryLeft` and `MultilinearMap.curryLeft` without auxiliary index reindexings or
decidable-equality assumptions. It supplies the inductive step for tensor products indexed by
ordered lists.

## Main definitions

* `PiTensorProduct.finConsEquiv`: splitting off the factor at `0` of a tensor product indexed by
  `Fin (n + 1)`.

## Main results

* `PiTensorProduct.finConsEquiv_tprod`, `PiTensorProduct.finConsEquiv_tprod_cons`, and
  `PiTensorProduct.finConsEquiv_symm_tmul`: the formula on pure tensors in both directions.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

universe u v

variable {R : Type u} [CommSemiring R] {n : ℕ}

/-- A tensor product indexed by `Fin (n + 1)` is the tensor product of the initial factor `M 0`
with the tensor product of the remaining factors `M i.succ`. -/
noncomputable def finConsEquiv (M : Fin (n + 1) → Type v)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    (⨂[R] i, M i) ≃ₗ[R] M 0 ⊗[R] (⨂[R] i : Fin n, M i.succ) :=
  LinearEquiv.ofLinearMap
    (lift <| LinearMap.uncurryLeft
      { toFun x := (TensorProduct.mk R (M 0) (⨂[R] i : Fin n, M i.succ) x).compMultilinearMap
          (tprod R)
        map_add' x y := by ext; simp
        map_smul' r x := by ext; simp })
    (TensorProduct.lift <| lift.toLinearMap.comp (tprod R (s := M)).curryLeft)
    (TensorProduct.ext <| LinearMap.ext fun x ↦ PiTensorProduct.ext <| MultilinearMap.ext fun m ↦ by
      simp)
    (PiTensorProduct.ext <| MultilinearMap.ext fun m ↦ by
      simp)

/-- Splitting off the initial factor of a pure tensor indexed by `Fin (n + 1)`. -/
@[simp]
theorem finConsEquiv_tprod (M : Fin (n + 1) → Type v)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (m : ∀ i, M i) :
    finConsEquiv M (tprod R m) = m 0 ⊗ₜ[R] tprod R (Fin.tail m) :=
  lift.tprod _

/-- Splitting off the initial factor of a pure tensor given by `Fin.cons`. -/
theorem finConsEquiv_tprod_cons (M : Fin (n + 1) → Type v)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (x : M 0) (m : ∀ i : Fin n, M i.succ) :
    finConsEquiv M (tprod R (Fin.cons x m)) = x ⊗ₜ[R] tprod R m := by
  simp

/-- Prepending a factor at `0` to a pure tensor indexed by `Fin n`. -/
@[simp]
theorem finConsEquiv_symm_tmul (M : Fin (n + 1) → Type v)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (x : M 0) (m : ∀ i : Fin n, M i.succ) :
    (finConsEquiv M).symm (x ⊗ₜ[R] tprod R m) = tprod R (Fin.cons x m) := by
  rw [LinearEquiv.symm_apply_eq, finConsEquiv_tprod_cons]

end PiTensorProduct
