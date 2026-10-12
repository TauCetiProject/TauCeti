/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# Upper transvections

This file records that an upper transvection belongs to the upper-triangular subgroup. This lets
upper transvections be used as elements of the Borel subgroup `B` in the construction of the
standard Tits system of `GLₙ₊₁`: they appear when an element of `B` is factored as a product with
a transvection at a simple root, and, together with their conjugates by permutation matrices, in
the proof that `B` and the permutation matrices generate `GLₙ(k)`.
-/

public section

open Matrix

namespace TauCeti

universe u v

variable (m : Type v) [Fintype m] [LinearOrder m] (R : Type u) [CommRing R]

variable {m R}

/-- A transvection `x_{ij}(c)` with `i < j` is upper triangular. -/
theorem transvectionUnit_mem_upperTriangularGroup {i j : m} (hij : i < j) (c : R) :
    transvectionUnit hij.ne c ∈ upperTriangularGroup m R := by
  rw [UpperTriangularGroup.mem_iff, coe_transvectionUnit]
  exact Matrix.blockTriangular_transvection (le_of_lt hij) c

end TauCeti
