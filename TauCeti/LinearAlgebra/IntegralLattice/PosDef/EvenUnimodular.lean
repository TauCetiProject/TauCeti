/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Milgram
public import TauCeti.LinearAlgebra.IntegralLattice.StandardCoordinates
import TauCeti.LinearAlgebra.Matrix.PosDef.Kronecker
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin

/-!
# Ranks of positive definite even unimodular lattices

An even unimodular positive definite integral lattice exists in rank `n` precisely when eight
divides `n`. The obstruction is Milgram's signature congruence
(`TauCeti.IntegralLattice.eight_dvd_finrank_of_isEven_isUnimodular_isPosDef`). For existence, the
Gram matrix of `k` orthogonal copies of the `E₈` root lattice is the Kronecker product of the
identity matrix of size `k` with the `E₈` Cartan matrix. This construction includes the rank-zero
lattice.

The coordinates on `Fin (8 * k)` are reindexed by `finProdFinEquiv`, so the `E₈` blocks are
explicitly indexed by `Fin k × Fin 8`. The resulting lattice is a concrete witness on `Fin n → ℚ`.

## Main results

* `TauCeti.IntegralLattice.e8PowLattice`: the lattice `E₈^k` of `k` orthogonal `E₈` blocks, with
  its block Gram matrix and standard integral carrier; it is even, unimodular and positive definite.
* `TauCeti.IntegralLattice.exists_isEven_isUnimodular_isPosDef_iff`: a positive definite even
  unimodular lattice on `Fin n → ℚ` exists exactly when `8 ∣ n`.
* `TauCeti.IntegralLattice.eight_dvd_finrank_of_isEven_isUnimodular_isPosDef`: the rank of any
  positive definite even unimodular integral lattice is divisible by eight.

## References

* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4.
-/

public section

open Matrix
open scoped Kronecker

namespace TauCeti.IntegralLattice

/-- The coordinate equivalence identifying `Fin (8 * k)` with `k` blocks of eight coordinates. -/
def e8PowIndexEquiv (k : ℕ) : Fin (8 * k) ≃ Fin k × Fin 8 :=
  (finCongr (Nat.mul_comm 8 k)).trans finProdFinEquiv.symm

/-- The Gram matrix of `k` orthogonal copies of the `E₈` root lattice, indexed by `Fin (8*k)`. -/
private noncomputable def e8PowGram (k : ℕ) : Matrix (Fin (8 * k)) (Fin (8 * k)) ℤ :=
  ((1 : Matrix (Fin k) (Fin k) ℤ) ⊗ₖ CartanMatrix.E 8).submatrix
    (e8PowIndexEquiv k) (e8PowIndexEquiv k)

private theorem e8PowGram_isSymm (k : ℕ) : (e8PowGram k).IsSymm :=
  (isSymm_one.kronecker (CartanMatrix.E_isSymm 8)).submatrix _

private theorem e8PowGram_diag (k : ℕ) (i : Fin (8 * k)) :
    e8PowGram k i i = 2 := by
  simp [e8PowGram, CartanMatrix.E_diag]

private theorem e8PowGram_det (k : ℕ) : (e8PowGram k).det = 1 := by
  rw [e8PowGram, Matrix.det_submatrix_equiv_self,
    Matrix.det_kronecker]
  simp [CartanMatrix.E₈_det]

private theorem e8PowGram_posDef (k : ℕ) :
    ((e8PowGram k).map (Int.cast : ℤ → ℚ)).PosDef := by
  have hcast : (((1 : Matrix (Fin k) (Fin k) ℤ) ⊗ₖ CartanMatrix.E 8).map
      (Int.cast : ℤ → ℚ)) =
      ((1 : Matrix (Fin k) (Fin k) ℚ) ⊗ₖ
        (CartanMatrix.E 8).map (Int.cast : ℤ → ℚ)) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases hij : i = j <;> simp [hij]
  rw [e8PowGram, ← Matrix.submatrix_map, hcast]
  exact posDef_map_intCast_cartanMatrix_E8.one_kronecker.submatrix (e8PowIndexEquiv k).injective

/-- The lattice `E₈^k`: `k` orthogonal copies of the `E₈` root lattice, as an integral lattice of
rank `8 * k` on `Fin (8 * k) → ℚ`. Its Gram matrix is `1 ⊗ₖ E₈` up to reindexing. -/
noncomputable def e8PowLattice (k : ℕ) : IntegralLattice (Fin (8 * k) → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin (8 * k))) (e8PowGram k) (e8PowGram_isSymm k)

/-- The lattice `E₈^k` is even. -/
theorem isEven_e8PowLattice (k : ℕ) : (e8PowLattice k).IsEven := by
  rw [e8PowLattice, isEven_ofGramMatrix_iff]
  intro i
  rw [e8PowGram_diag]
  exact even_two

/-- The lattice `E₈^k` is unimodular. -/
theorem isUnimodular_e8PowLattice (k : ℕ) : (e8PowLattice k).IsUnimodular := by
  have hdet : (e8PowLattice k).determinant = 1 := by
    rw [e8PowLattice, determinant_ofGramMatrix, e8PowGram_det]
  -- `isUnimodular_iff_isUnit_determinant` needs nondegeneracy as an instance.
  have : (e8PowLattice k).IsNondegenerate :=
    ⟨(determinant_ne_zero_iff _).mp (hdet ▸ one_ne_zero)⟩
  rw [isUnimodular_iff_isUnit_determinant, hdet]
  exact isUnit_one

/-- The lattice `E₈^k` is positive definite. -/
theorem isPosDef_e8PowLattice (k : ℕ) : (e8PowLattice k).IsPosDef :=
  (isPosDef_ofGramMatrix_iff _ _ _).mpr (e8PowGram_posDef k)

/-- The Gram matrix of `E₈^k` on the basis indexed by `Fin k × Fin 8` is block diagonal, with
each diagonal block the `E₈` Cartan matrix. -/
@[simp]
theorem form_e8PowLattice_basisFun (k : ℕ) (a b : Fin k) (i j : Fin 8) :
    (e8PowLattice k).form
        (Pi.single ((e8PowIndexEquiv k).symm (a, i)) 1)
        (Pi.single ((e8PowIndexEquiv k).symm (b, j)) 1) =
      if a = b then (((CartanMatrix.E 8) i j : ℤ) : ℚ) else 0 := by
  rw [← Pi.basisFun_apply, ← Pi.basisFun_apply]
  rw [e8PowLattice, form_ofGramMatrix_basisFun_basisFun]
  simp [e8PowGram, one_apply]

/-- The carrier of `E₈^k` is the integral span of its standard basis. -/
theorem e8PowLattice_carrier (k : ℕ) :
    (e8PowLattice k).carrier =
      Submodule.span ℤ (Set.range (Pi.basisFun ℚ (Fin (8 * k)))) := by
  rw [e8PowLattice]
  exact ofGramMatrix_carrier _ _ _

/-- A vector belongs to `E₈^k` exactly when all its standard coordinates are integers. -/
@[simp]
theorem mem_e8PowLattice_carrier_iff (k : ℕ) (x : Fin (8 * k) → ℚ) :
    x ∈ (e8PowLattice k).carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i := by
  rw [e8PowLattice]
  exact mem_ofGramMatrix_basisFun_carrier_iff _ _ x

/-- **Positive definite even unimodular lattices exist exactly in ranks divisible by eight.**
The witness at rank `8 * k` is `e8PowLattice k`. -/
theorem exists_isEven_isUnimodular_isPosDef_iff (n : ℕ) :
    (∃ L : IntegralLattice (Fin n → ℚ), L.IsEven ∧ L.IsUnimodular ∧ L.IsPosDef) ↔
      8 ∣ n := by
  constructor
  · rintro ⟨L, hE, hU, hP⟩
    simpa [Module.finrank_pi_fintype] using
      L.eight_dvd_finrank_of_isEven_isUnimodular_isPosDef hE hU hP
  · rintro ⟨k, rfl⟩
    exact ⟨e8PowLattice k, isEven_e8PowLattice k, isUnimodular_e8PowLattice k,
      isPosDef_e8PowLattice k⟩

end TauCeti.IntegralLattice
