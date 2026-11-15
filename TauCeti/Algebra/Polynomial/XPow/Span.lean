/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Spanning a module over a polynomial ring by the powers of `X`

The `R[X]`-span of a family `m` in a module over `R[X]` is, as an `R`-module, the supremum of
the `R`-submodules spanned by the elements `X ^ i • m k` with `k` ranging over the index type.

## Main declarations

* `TauCeti.iSup_span_range_X_pow_smul`: these `R`-submodules have supremum the `R[X]`-span
  of `m`, restricted to `R`.
-/

public section

namespace TauCeti

open Polynomial

/-- The `R`-submodules spanned by `X ^ i • m k`, for `i : ℕ`, have supremum the `R[X]`-span
of `m`, viewed as an `R`-submodule. -/
theorem iSup_span_range_X_pow_smul {R : Type*} [Semiring R]
    {M : Type*} [AddCommMonoid M] [Module R[X] M] [Module R M] [IsScalarTower R R[X] M]
    {ι : Type*} (m : ι → M) :
    ⨆ i, Submodule.span R (Set.range fun k ↦ (X ^ i : R[X]) • m k) =
      (Submodule.span R[X] (Set.range m)).restrictScalars R := by
  have hspan : Submodule.span R (Set.range fun i : ℕ ↦ (X ^ i : R[X])) = ⊤ := by
    simpa [← Polynomial.X_pow_eq_monomial] using (Polynomial.basisMonomials R).span_eq
  rw [← Submodule.span_smul_of_span_eq_top hspan, Set.range_smul_range, Submodule.iSup_span]
  congr 1
  ext x
  simp [Prod.exists, eq_comm]

end TauCeti
