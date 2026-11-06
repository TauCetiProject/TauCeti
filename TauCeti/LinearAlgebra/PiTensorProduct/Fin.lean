/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Prepending an initial factor to a `Fin`-indexed tensor product

Prepending an initial factor `M 0` to a tensor product of `n` modules indexed by `Fin n` gives the
tensor product indexed by `Fin (n + 1)` along `Fin.cons` and `Fin.tail`:

```text
M 0 ⊗ (⨂ᵢ M (i.succ)) ≃ ⨂ᵢ Mᵢ,     x ⊗ₜ (⨂ₜ mᵢ) ↦ ⨂ₜ (Fin.cons x m)ᵢ.
```

This is the `Fin`-indexed counterpart of `PiTensorProduct.optionEquiv`, oriented to match
`Fin.consEquiv` and `Fin.consLinearEquiv` and built directly from `MultilinearMap.curryLeft` and
`LinearMap.uncurryLeft` without auxiliary index reindexings or decidable-equality assumptions. It
supplies the inductive step for tensor products indexed by ordered lists.

## Main definitions

* `PiTensorProduct.finConsEquiv`: prepending a factor at `0` to a tensor product indexed by `Fin n`
  to obtain one indexed by `Fin (n + 1)`.

## Main results

* `PiTensorProduct.finConsEquiv_tmul` and `PiTensorProduct.finConsEquiv_symm_tprod`: the formula on
  pure tensors in both directions.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

universe u v

variable (R : Type u) [CommSemiring R] {n : ℕ}

/-- Prepending an initial factor `M 0` to the tensor product of the remaining factors `M i.succ`
gives the tensor product indexed by `Fin (n + 1)`. -/
noncomputable def finConsEquiv (M : Fin (n + 1) → Type v)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    M 0 ⊗[R] (⨂[R] i : Fin n, M i.succ) ≃ₗ[R] (⨂[R] i, M i) :=
  LinearEquiv.ofLinearMap
    (TensorProduct.lift <| lift.toLinearMap.comp (tprod R (s := M)).curryLeft)
    (lift <| LinearMap.uncurryLeft
      { toFun x := (TensorProduct.mk R (M 0) (⨂[R] i : Fin n, M i.succ) x).compMultilinearMap
          (tprod R)
        map_add' x y := by ext; simp
        map_smul' r x := by ext; simp })
    (PiTensorProduct.ext <| MultilinearMap.ext fun m ↦ by
      simp)
    (TensorProduct.ext <| LinearMap.ext fun x ↦ PiTensorProduct.ext <| MultilinearMap.ext fun m ↦ by
      simp)

/-- Prepending a factor at `0` to a pure tensor indexed by `Fin n`. -/
@[simp]
theorem finConsEquiv_tmul (M : Fin (n + 1) → Type v)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (x : M 0) (m : ∀ i : Fin n, M i.succ) :
    finConsEquiv R M (x ⊗ₜ[R] tprod R m) = tprod R (Fin.cons x m) := by
  simp [finConsEquiv]

/-- Splitting off the initial factor of a pure tensor indexed by `Fin (n + 1)`. -/
@[simp]
theorem finConsEquiv_symm_tprod (M : Fin (n + 1) → Type v)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (m : ∀ i, M i) :
    (finConsEquiv R M).symm (tprod R m) = m 0 ⊗ₜ[R] tprod R (Fin.tail m) :=
  lift.tprod _

end PiTensorProduct
