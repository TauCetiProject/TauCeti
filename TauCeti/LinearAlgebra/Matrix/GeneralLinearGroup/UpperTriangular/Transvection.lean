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

This file records that an upper transvection belongs to the upper-triangular subgroup.
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
