/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Logic.Equiv.Option

/-!
# Splitting off one factor of an `Option`-indexed tensor product

A tensor product indexed by `Option α` is the tensor product of the factors indexed by `α` with
the factor at `none`:

```text
⨂ₒ Pₒ ≃ (⨂ᵢ P (some i)) ⊗ P none,     ⨂ₜ mₒ ↦ (⨂ₜ m (some i)) ⊗ₜ m none.
```

This is the inductive step in constructions by induction on a finite index type, such as
`PiTensorProduct.sigmaEquiv` and `PiTensorProduct.tensorDistribEquiv`.

## Main definitions

* `PiTensorProduct.optionEquiv`: splitting off the factor at `none` of a tensor product indexed
  by `Option α`.

## Main results

* `PiTensorProduct.optionEquiv_tprod` and `PiTensorProduct.optionEquiv_symm_tmul`: the formula
  on pure tensors in both directions.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

universe u v x

variable {R : Type u} [CommSemiring R]

/-- A tensor product indexed by `Option α` is the tensor product of the factors indexed by `α`
with the factor at `none`. -/
noncomputable def optionEquiv {α : Type x} (P : Option α → Type v)
    [∀ o, AddCommMonoid (P o)] [∀ o, Module R (P o)] :
    (⨂[R] o, P o) ≃ₗ[R] (⨂[R] i : α, P (some i)) ⊗[R] P none :=
  (reindex R P (Equiv.optionEquivSumPUnit.{x, x} α)).trans
    ((tmulEquivDep R (fun z ↦ P ((Equiv.optionEquivSumPUnit.{x, x} α).symm z))).symm.trans
      (TensorProduct.congr (LinearEquiv.refl R _) (subsingletonEquiv PUnit.unit)))

/-- Splitting off the factor at `none` of a pure tensor. -/
@[simp]
theorem optionEquiv_tprod {α : Type x} (P : Option α → Type v)
    [∀ o, AddCommMonoid (P o)] [∀ o, Module R (P o)] (m : ∀ o, P o) :
    optionEquiv P (tprod R m) = tprod R (fun i ↦ m (some i)) ⊗ₜ m none := by
  simp only [optionEquiv, LinearEquiv.trans_apply, reindex_tprod, tmulEquivDep_symm_apply]
  exact (TensorProduct.congr_tmul _ _ _ _).trans
    (congrArg _ (subsingletonEquiv_apply_tprod PUnit.unit _))

/-- Reattaching the factor at `none` to a pure tensor. -/
@[simp]
theorem optionEquiv_symm_tmul {α : Type x} (P : Option α → Type v)
    [∀ o, AddCommMonoid (P o)] [∀ o, Module R (P o)] (m : ∀ o, P o) :
    (optionEquiv P).symm (tprod R (fun i ↦ m (some i)) ⊗ₜ m none) = tprod R m := by
  rw [LinearEquiv.symm_apply_eq, optionEquiv_tprod]

end PiTensorProduct
