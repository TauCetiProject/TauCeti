/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Milgram
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

The choice of coordinates on `Fin (8 * k)` is immaterial; a finite-type equivalence reindexes
the natural product coordinates. The resulting lattice is a concrete witness on `Fin n → ℚ`.

## Main results

* `TauCeti.IntegralLattice.e8PowLattice`: the lattice `E₈^k` of `k` orthogonal `E₈` blocks, with
  `e8PowLattice_isEven`, `e8PowLattice_isUnimodular` and `e8PowLattice_isPosDef`.
* `TauCeti.IntegralLattice.exists_isEven_isUnimodular_isPosDef_iff`: a positive definite even
  unimodular lattice on `Fin n → ℚ` exists exactly when `8 ∣ n`.

## References

* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4.
-/

public section

open Matrix
open scoped Kronecker

namespace TauCeti.IntegralLattice

private noncomputable def eightBlockEquiv (k : ℕ) : Fin (8 * k) ≃ Fin k × Fin 8 := by
  apply Fintype.equivOfCardEq
  simp [Fintype.card_prod]
  omega

/-- The Gram matrix of `k` orthogonal copies of the `E₈` root lattice, indexed by `Fin (8*k)`. -/
private noncomputable def e8PowGram (k : ℕ) : Matrix (Fin (8 * k)) (Fin (8 * k)) ℤ :=
  ((1 : Matrix (Fin k) (Fin k) ℤ) ⊗ₖ CartanMatrix.E 8).submatrix
    (eightBlockEquiv k) (eightBlockEquiv k)

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
  exact posDef_map_intCast_cartanMatrix_E8.one_kronecker.submatrix (eightBlockEquiv k).injective

/-- The lattice `E₈^k`: `k` orthogonal copies of the `E₈` root lattice, as an integral lattice of
rank `8 * k` on `Fin (8 * k) → ℚ`. Its Gram matrix is `1 ⊗ₖ E₈` up to reindexing. -/
noncomputable def e8PowLattice (k : ℕ) : IntegralLattice (Fin (8 * k) → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin (8 * k))) (e8PowGram k) (e8PowGram_isSymm k)

/-- The lattice `E₈^k` is even. -/
theorem e8PowLattice_isEven (k : ℕ) : (e8PowLattice k).IsEven := by
  rw [e8PowLattice, isEven_ofGramMatrix_iff]
  intro i
  rw [e8PowGram_diag]
  exact even_two

/-- The lattice `E₈^k` is unimodular. -/
theorem e8PowLattice_isUnimodular (k : ℕ) : (e8PowLattice k).IsUnimodular := by
  have hdet : (e8PowLattice k).determinant = 1 := by
    rw [e8PowLattice, determinant_ofGramMatrix, e8PowGram_det]
  -- `isUnimodular_iff_isUnit_determinant` needs nondegeneracy as an instance.
  have : (e8PowLattice k).IsNondegenerate :=
    ⟨(determinant_ne_zero_iff _).mp (hdet ▸ one_ne_zero)⟩
  rw [isUnimodular_iff_isUnit_determinant, hdet]
  exact isUnit_one

/-- The lattice `E₈^k` is positive definite. -/
theorem e8PowLattice_isPosDef (k : ℕ) : (e8PowLattice k).IsPosDef :=
  (isPosDef_ofGramMatrix_iff _ _ _).mpr (e8PowGram_posDef k)

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
    exact ⟨e8PowLattice k, e8PowLattice_isEven k, e8PowLattice_isUnimodular k,
      e8PowLattice_isPosDef k⟩

end TauCeti.IntegralLattice
