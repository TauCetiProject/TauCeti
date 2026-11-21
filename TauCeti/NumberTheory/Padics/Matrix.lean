/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Matrices over the `p`-adic integers lifted from `𝔽_p`

A matrix over `𝔽_p` with nonzero determinant, lifted entrywise to `ℤ_p`, has a unit determinant,
because its reduction modulo `p` has nonzero determinant.

## Main results

* `Matrix.isUnit_det_transpose_map_cast`: the transpose of the entrywise lift to `ℤ_p` of a matrix
  over `𝔽_p` with nonzero determinant has a unit determinant.
-/

public section

variable {p : ℕ} [Fact p.Prime]

namespace Matrix

/-- **The lifted degree-one matrix of a nondegenerate form has unit determinant.** The matrix
over `𝔽_p` with nonzero determinant, lifted entrywise to `ℤ_p` and transposed, has a unit
determinant, since its reduction modulo `p` has nonzero determinant. -/
theorem isUnit_det_transpose_map_cast {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι (ZMod p)) (hB : B.det ≠ 0) :
    IsUnit (B.map (ZMod.cast : ZMod p → ℤ_[p]))ᵀ.det := by
  have h1 : (PadicInt.toZMod (p := p)).mapMatrix (B.map (ZMod.cast : ZMod p → ℤ_[p]))ᵀ = Bᵀ := by
    ext i j
    simp [ZMod.ringHom_map_cast]
  rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, RingHom.map_det,
    h1, Matrix.det_transpose]
  exact hB

end Matrix
