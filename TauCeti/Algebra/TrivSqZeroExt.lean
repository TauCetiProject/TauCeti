/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Module equivalence for trivial square-zero extensions

For a semiring `S` and `S`-modules `R` and `M`, the trivial square-zero extension
`TrivSqZeroExt R M` is isomorphic as an `S`-module to the product `R × M`, sending `x` to
`(x.fst, x.snd)` with inverse `(r, m) ↦ inl r + inr m`.

## Main definitions

* `TrivSqZeroExt.linearEquivProd`: the `S`-linear equivalence `TrivSqZeroExt R M ≃ₗ[S] R × M`.
-/

public section

namespace TrivSqZeroExt

variable (S R M : Type*) [Semiring S] [AddCommMonoid R] [AddCommMonoid M]
  [Module S R] [Module S M]

/-- The `S`-linear equivalence identifying the trivial square-zero extension `TrivSqZeroExt R M`
with the product module `R × M`. -/
def linearEquivProd : TrivSqZeroExt R M ≃ₗ[S] R × M where
  toFun x := (x.fst, x.snd)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  invFun p := inl p.1 + inr p.2
  left_inv x := inl_fst_add_inr_snd_eq x
  right_inv _ := by ext <;> simp

@[simp]
theorem linearEquivProd_apply (x : TrivSqZeroExt R M) :
    linearEquivProd S R M x = (x.fst, x.snd) := (rfl)

@[simp]
theorem linearEquivProd_symm_apply (p : R × M) :
    (linearEquivProd S R M).symm p = inl p.1 + inr p.2 := (rfl)

theorem linearEquivProd_inl (r : R) :
    linearEquivProd S R M (inl r) = (r, 0) := by
  simp

theorem linearEquivProd_inr (m : M) :
    linearEquivProd S R M (inr m) = (0, m) := by
  simp

end TrivSqZeroExt
