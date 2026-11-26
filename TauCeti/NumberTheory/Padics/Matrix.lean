/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Matrices over the `p`-adic integers and the `p`-adic numbers

A matrix over `𝔽_p` with nonzero determinant, lifted entrywise to `ℤ_p`, has a unit determinant,
because its reduction modulo `p` has nonzero determinant. A matrix over `ℚ_p` becomes integral
after multiplication by a suitable power of `p`. A matrix over `ℤ_p` reduces to `0` modulo `p`
exactly when it is `p` times a matrix over `ℤ_p`.

## Main results

* `Matrix.isUnit_det_transpose_map_cast`: the transpose of the entrywise lift to `ℤ_p` of a matrix
  over `𝔽_p` with nonzero determinant has a unit determinant.
* `Matrix.exists_map_padicInt_eq_pow_smul`: some `p ^ k M` of a matrix `M` over `ℚ_p` has entries
  in `ℤ_p`.
* `Matrix.map_toZMod_nsmul_eq_zero`, `Matrix.exists_eq_nsmul_of_map_toZMod_eq_zero`: a matrix over
  `ℤ_p` reduces to `0` modulo `p` exactly when it is `p` times a matrix over `ℤ_p`.
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

/-- A multiple `m • X` of a matrix over `ℤ_p` with `p ∣ m` reduces to `0` modulo `p`. -/
theorem map_toZMod_nsmul_eq_zero {m n : Type*} {k : ℕ} (hk : p ∣ k) (X : Matrix m n ℤ_[p]) :
    (k • X).map PadicInt.toZMod = 0 := by
  ext i j
  simp [(ZMod.natCast_eq_zero_iff k p).2 hk]

/-- A matrix over `ℤ_p` that reduces to `0` modulo `p` is `p` times a matrix over `ℤ_p`. -/
theorem exists_eq_nsmul_of_map_toZMod_eq_zero {m n : Type*} {X : Matrix m n ℤ_[p]}
    (hX : X.map PadicInt.toZMod = 0) : ∃ Y : Matrix m n ℤ_[p], X = p • Y := by
  have h : ∀ i j, (p : ℤ_[p]) ∣ X i j := fun i j ↦
    (PadicInt.toZMod_eq_zero_iff_dvd _).1 (by simpa using congrFun (congrFun hX i) j)
  choose Y hY using h
  exact ⟨of Y, by ext i j; simp [hY i j, nsmul_eq_mul]⟩

end Matrix
