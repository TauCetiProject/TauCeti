/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Linear equivalence of a trivial square-zero extension with a product

For a semiring `R` and an `R`-module `M`, the trivial square-zero extension `TrivSqZeroExt R M` is
definitionally the product module `R × M`. This file records the named `R`-linear equivalence
`TrivSqZeroExt.linearEquivProd` identifying `TrivSqZeroExt R M` with `R × M` via `(fst, snd)`.

## Main definitions

* `TrivSqZeroExt.linearEquivProd`: the canonical `R`-linear equivalence
  `TrivSqZeroExt R M ≃ₗ[R] R × M` given by `(fst, snd)`.
-/

public section

namespace TrivSqZeroExt

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

/-- The canonical `R`-linear equivalence identifying `TrivSqZeroExt R M` with `R × M` via
`fst` and `snd`. -/
def linearEquivProd : TrivSqZeroExt R M ≃ₗ[R] R × M :=
  LinearEquiv.refl R (R × M)

variable {R M}

/-- Applying `TrivSqZeroExt.linearEquivProd` returns `(x.fst, x.snd)`. -/
@[simp]
theorem linearEquivProd_apply (x : TrivSqZeroExt R M) :
    linearEquivProd R M x = (x.fst, x.snd) := by
  simp only [linearEquivProd]
  rfl

/-- The inverse of `TrivSqZeroExt.linearEquivProd` sends `(r, m)` to `inl r + inr m`. -/
@[simp]
theorem linearEquivProd_symm_apply (y : R × M) :
    (linearEquivProd R M).symm y = inl y.1 + inr y.2 := by
  simp only [linearEquivProd]
  exact (inl_fst_add_inr_snd_eq y).symm

end TrivSqZeroExt
