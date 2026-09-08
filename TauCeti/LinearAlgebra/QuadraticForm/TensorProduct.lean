/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct.Isometries

/-!
# Tensor products of equivalent quadratic forms

This file shows that tensor products preserve isometric equivalences and equivalence of quadratic
forms. It complements Mathlib's tensor product of quadratic-form isometries.

## Main definitions

* `QuadraticMap.IsometryEquiv.tmul`: the tensor product of two isometric equivalences.
* `QuadraticMap.Equivalent.tmul`: tensor products preserve equivalence of quadratic forms.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Tensor product of isometric equivalences of quadratic forms. -/
noncomputable def _root_.QuadraticMap.IsometryEquiv.tmul
    {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {S₁ : QuadraticForm R N₁} {S₂ : QuadraticForm R N₂}
    (e : Q₁.IsometryEquiv Q₂) (f : S₁.IsometryEquiv S₂) :
    (Q₁.tmul S₁).IsometryEquiv (Q₂.tmul S₂) where
  toLinearEquiv := LinearEquiv.ofBijective
    (TensorProduct.map e.toIsometry.toLinearMap f.toIsometry.toLinearMap)
    (TensorProduct.map_bijective
      (by
        constructor
        · exact e.injective
        · exact e.surjective)
      (by
        constructor
        · exact f.injective
        · exact f.surjective))
  map_app' x := QuadraticForm.tmul_tensorMap_apply e.toIsometry f.toIsometry x

/-- Tensor product preserves equivalence of quadratic forms. -/
theorem _root_.QuadraticMap.Equivalent.tmul
    {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {S₁ : QuadraticForm R N₁} {S₂ : QuadraticForm R N₂}
    (hQ : Q₁.Equivalent Q₂) (hS : S₁.Equivalent S₂) :
    (Q₁.tmul S₁).Equivalent (Q₂.tmul S₂) :=
  Nonempty.map2 QuadraticMap.IsometryEquiv.tmul hQ hS

end TauCeti
