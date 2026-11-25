/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.Matrix.Determinant.Locus
import TauCeti.LinearAlgebra.Matrix.IdealEntries
import TauCeti.RingTheory.WittVector.Units
import Mathlib.Data.ZMod.Basic

/-!
# Checks for the determinant locus

Over the Witt vectors of a perfect ring, the determinant locus for `p` is the locus where the
Witt coordinates of the determinant satisfy `det₀ = ⋯ = det_{N-1} = 0` with `det_N` a unit, and it
is detected modulo `p ^ h` for every `h > N`. Over `W₂(𝔽₂) = ℤ/4` and `W₃(𝔽₂) = ℤ/8` the small
cases separate the loci for different `N`, and at the excluded depth `h = N = 1` the matrices
`(2)` and `(0)` agree modulo `2` although only the first lies in the locus.
-/

open Ideal Matrix

section WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]
  {n : Type*} [Fintype n] [DecidableEq n] {N h : ℕ}

-- The locus `V_N` over `W(R)` is cut out by the Witt coordinates of the determinant.
example (A : Matrix n n (WittVector p R)) :
    A ∈ detLocus n (p : WittVector p R) N ↔
      (∀ m < N, A.det.coeff m = 0) ∧ IsUnit (A.det.coeff N) :=
  mem_detLocus_iff_associated.trans WittVector.associated_p_pow_iff

-- For `h > N` the locus is detected by the reduction modulo `p ^ h`.
example (hNh : N < h) (A : Matrix n n (WittVector p R)) :
    A.map (Ideal.Quotient.mk (span {(p : WittVector p R) ^ h})) ∈
        detLocus n (Ideal.Quotient.mk (span {(p : WittVector p R) ^ h}) p) N ↔
      A ∈ detLocus n (p : WittVector p R) N :=
  map_mk_mem_detLocus_iff WittVector.p_mem_jacobson hNh

end WittVector

-- Over `ℤ/4` the identity lies in the locus for `N = 0`.
example : (1 : Matrix (Fin 2) (Fin 2) (ZMod 4)) ∈ detLocus (Fin 2) (2 : ZMod 4) 0 := by
  simp

-- Over `ℤ/4` the zero `1 × 1` matrix does not lie in the locus for `N = 0`.
example : !![(0 : ZMod 4)] ∉ detLocus (Fin 1) (2 : ZMod 4) 0 := by
  simp only [detLocus_zero, Set.mem_ofPred_eq, det_fin_one_of, isUnit_zero_iff]
  decide

-- Over `ℤ/8`, `diag(2, 1)` has determinant `2` and lies in the locus for `N = 1`.
example : diagonal ![(2 : ZMod 8), 1] ∈ detLocus (Fin 2) (2 : ZMod 8) 1 :=
  mem_detLocus_iff.mpr ⟨1, by simp⟩

-- It does not lie in the locus for `N = 0`: `2` is not a unit of `ℤ/8`.
example : diagonal ![(2 : ZMod 8), 1] ∉ detLocus (Fin 2) (2 : ZMod 8) 0 := by
  simp only [detLocus_zero, Set.mem_ofPred_eq, det_diagonal, Fin.prod_univ_two]
  decide

-- Nor in the locus for `N = 2`: `2 = 4 u` would give `4 = 8 u = 0`.
example : diagonal ![(2 : ZMod 8), 1] ∉ detLocus (Fin 2) (2 : ZMod 8) 2 := by
  rw [mem_detLocus_iff]
  rintro ⟨u, hu⟩
  have h4 : (4 : ZMod 8) = u * 8 := by
    linear_combination (2 : ZMod 8) * (by simpa using hu : (2 : ZMod 8) = u * 2 ^ 2)
  have h0 : (4 : ZMod 8) = 0 := by rw [h4]; exact mul_eq_zero_of_right _ (by decide)
  exact absurd h0 (by decide)

-- At the excluded depth `h = N = 1`, membership in the locus is not detected modulo `2`: the
-- matrices `(2)` and `(0)` over `ℤ/8` agree modulo `2`, but only `(2)` lies in the locus.
example : ¬ ∀ A : Matrix (Fin 1) (Fin 1) (ZMod 8),
    (A.map (Ideal.Quotient.mk (span {(2 : ZMod 8) ^ 1})) ∈
        detLocus (Fin 1) (Ideal.Quotient.mk (span {(2 : ZMod 8) ^ 1}) 2) 1 ↔
      A ∈ detLocus (Fin 1) (2 : ZMod 8) 1) := by
  intro h
  have h2 : !![(2 : ZMod 8)] ∈ detLocus (Fin 1) (2 : ZMod 8) 1 :=
    mem_detLocus_iff.mpr ⟨1, by simp⟩
  have h0 : !![(0 : ZMod 8)] ∉ detLocus (Fin 1) (2 : ZMod 8) 1 := by
    rw [mem_detLocus_iff]
    rintro ⟨u, hu⟩
    have : (2 : ZMod 8) = 0 := by simpa using congrArg ((↑u⁻¹ : ZMod 8) * ·) hu.symm
    exact absurd this (by decide)
  have hmap : !![(0 : ZMod 8)].map (Ideal.Quotient.mk (span {(2 : ZMod 8) ^ 1})) =
      !![(2 : ZMod 8)].map (Ideal.Quotient.mk (span {(2 : ZMod 8) ^ 1})) :=
    map_mk_eq_map_mk_iff.mpr ⟨!![-1], by ext i j; fin_cases i; fin_cases j; simp⟩
  exact h0 ((h _).mp (hmap ▸ (h _).mpr h2))
