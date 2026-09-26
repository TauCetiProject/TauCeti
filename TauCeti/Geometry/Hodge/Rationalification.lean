/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# Rationalification of an integral module

The **rationalification** of an integral module `V` is the scalar extension `ℚ ⊗[ℤ] V`. Together
with the concrete complexification `ℂ ⊗[ℤ] V` (see `TauCeti.Hodge.Complexification`) and the
realification `ℝ ⊗[ℤ] V`, it is the middle leg of the `ℤ → ℚ → ℂ` tower used by pure and mixed
Hodge structures.

## Main definitions

* `TauCeti.Hodge.Rationalification`: the rational scalar extension of an integral module.
* `TauCeti.Hodge.rationalificationMap`: the canonical map `V → ℚ ⊗[ℤ] V`; it is an inclusion
  exactly when `V` is flat over `ℤ`, equivalently torsion-free.
* `TauCeti.Hodge.isBaseChange_rationalificationMap`: the concrete tensor is the canonical
  rational `IsBaseChange` model.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u

variable {V : Type u} [AddCommGroup V]

/-- The rationalification `ℚ ⊗[ℤ] V` of an integral module. -/
abbrev Rationalification (V : Type u) [AddCommGroup V] :=
  ℚ ⊗[ℤ] V

/-- The canonical map from an integral module to its rationalification. -/
def rationalificationMap : V →ₗ[ℤ] Rationalification V :=
  (TensorProduct.mk ℤ ℚ V) 1

/-- The canonical map to the rationalification sends an integral vector to the corresponding pure
tensor. -/
@[simp]
theorem rationalificationMap_apply (x : V) : rationalificationMap x = 1 ⊗ₜ[ℤ] x :=
  TensorProduct.mk_apply 1 x

/-- The concrete tensor `ℚ ⊗[ℤ] V` is the canonical rational `IsBaseChange` model. -/
theorem isBaseChange_rationalificationMap :
    IsBaseChange ℚ (rationalificationMap (V := V)) :=
  TensorProduct.isBaseChange ℤ V ℚ

end TauCeti.Hodge
