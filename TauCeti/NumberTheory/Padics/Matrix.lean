/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Matrices over the `p`-adic integers and the `p`-adic numbers

A matrix over `𝔽_p` with nonzero determinant, lifted entrywise to `ℤ_p`, has a unit determinant,
because its reduction modulo `p` has nonzero determinant. A matrix over `ℚ_p` becomes integral
after multiplication by a suitable power of `p`.

## Main results

* `Matrix.isUnit_det_transpose_map_cast`: the transpose of the entrywise lift to `ℤ_p` of a matrix
  over `𝔽_p` with nonzero determinant has a unit determinant.
* `Matrix.exists_map_padicInt_eq_pow_smul`: some `p ^ k M` of a matrix `M` over `ℚ_p` has entries
  in `ℤ_p`.
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

/-- **Clearing denominators in a `p`-adic matrix**: some `p ^ k M` is the entrywise image of a
matrix over `ℤ_[p]`. -/
theorem exists_map_padicInt_eq_pow_smul {m n : Type*} [Finite m] [Finite n]
    (M : Matrix m n ℚ_[p]) :
    ∃ (k : ℕ) (A : Matrix m n ℤ_[p]), A.map ((↑) : ℤ_[p] → ℚ_[p]) = (p : ℚ_[p]) ^ k • M := by
  obtain ⟨k, hk⟩ := Padic.exists_forall_norm_pow_mul_le_one fun ij : m × n ↦ M ij.1 ij.2
  exact ⟨k, of fun i j ↦ ⟨_, hk (i, j)⟩, by ext; rfl⟩

end Matrix
