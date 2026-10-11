/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Milgram
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE
import Mathlib.LinearAlgebra.Matrix.Kronecker
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin

/-!
# Ranks of positive definite even unimodular lattices

An even unimodular positive definite integral lattice exists in rank `n` precisely when eight
divides `n`. The obstruction is Milgram's signature congruence. For existence, the Gram matrix
of `k` orthogonal copies of the `E₈` root lattice is the Kronecker product of the identity
matrix of size `k` with the `E₈` Cartan matrix. This construction includes the rank-zero lattice.

The choice of coordinates on `Fin (8 * k)` is immaterial; a finite-type equivalence reindexes
the natural product coordinates. The resulting lattice is a concrete witness on `Fin n → ℚ`.

## Main result

* `TauCeti.IntegralLattice.eight_dvd_finrank_of_isEven_isUnimodular_isPosDef`: the rank
  obstruction for any positive definite integral lattice.
* `TauCeti.IntegralLattice.exists_even_unimodular_posDef_iff`: a positive definite even
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
private noncomputable def e8BlockGram (k : ℕ) : Matrix (Fin (8 * k)) (Fin (8 * k)) ℤ :=
  ((1 : Matrix (Fin k) (Fin k) ℤ) ⊗ₖ CartanMatrix.E 8).submatrix
    (eightBlockEquiv k) (eightBlockEquiv k)

private theorem e8BlockGram_isSymm (k : ℕ) : (e8BlockGram k).IsSymm := by
  apply Matrix.IsSymm.submatrix
  apply Matrix.IsSymm.ext
  intro i j
  rw [Matrix.kronecker_apply, Matrix.kronecker_apply,
    Matrix.isSymm_one.apply, (CartanMatrix.E_isSymm 8).apply]

private theorem e8BlockGram_diag (k : ℕ) (i : Fin (8 * k)) :
    e8BlockGram k i i = 2 := by
  simp [e8BlockGram, CartanMatrix.E_diag]

private theorem e8BlockGram_det (k : ℕ) : (e8BlockGram k).det = 1 := by
  rw [e8BlockGram, Matrix.det_submatrix_equiv_self,
    Matrix.det_kronecker]
  simp [CartanMatrix.E₈_det]

private theorem e8Kron_quadratic (k : ℕ) (x : Fin k × Fin 8 → ℚ) :
    x ⬝ᵥ (((1 : Matrix (Fin k) (Fin k) ℚ) ⊗ₖ
      (CartanMatrix.E 8).map (Int.cast : ℤ → ℚ)) *ᵥ x) =
      ∑ i : Fin k, (fun j : Fin 8 => x (i, j)) ⬝ᵥ
        ((CartanMatrix.E 8).map (Int.cast : ℤ → ℚ) *ᵥ
          (fun j : Fin 8 => x (i, j))) := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Matrix.one_apply, ite_mul,
    Finset.sum_ite_eq]

private theorem e8Kron_posDef (k : ℕ) :
    (((1 : Matrix (Fin k) (Fin k) ℚ) ⊗ₖ
      (CartanMatrix.E 8).map (Int.cast : ℤ → ℚ))).PosDef := by
  have hE : ((CartanMatrix.E 8).map (Int.cast : ℤ → ℚ)).PosDef :=
    posDef_map_intCast_cartanMatrix_E8
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.ext
    rintro ⟨i, a⟩ ⟨j, b⟩
    simp only [Matrix.kronecker_apply, Matrix.map_apply]
    rw [Matrix.isSymm_one.apply, (CartanMatrix.E_isSymm 8).apply]
  · intro x hx
    have hrow (i : Fin k) :
        0 ≤ (fun j : Fin 8 => x (i, j)) ⬝ᵥ
          ((CartanMatrix.E 8).map (Int.cast : ℤ → ℚ) *ᵥ
            (fun j : Fin 8 => x (i, j))) := by
      by_cases hi : (fun j : Fin 8 => x (i, j)) = 0
      · simp [hi]
      · exact le_of_lt (by simpa using (Matrix.posDef_iff_dotProduct_mulVec.mp hE).2 hi)
    have hsome : ∃ i : Fin k, (fun j : Fin 8 => x (i, j)) ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext ⟨i, j⟩
      exact congrFun (h i) j
    simp only [star_trivial]
    rw [e8Kron_quadratic]
    apply Finset.sum_pos' (fun i _ => hrow i)
    obtain ⟨i, hi⟩ := hsome
    exact ⟨i, Finset.mem_univ _, by
      simpa using (Matrix.posDef_iff_dotProduct_mulVec.mp hE).2 hi⟩

private theorem e8BlockGram_posDef (k : ℕ) :
    ((e8BlockGram k).map (Int.cast : ℤ → ℚ)).PosDef := by
  have hcast : (((1 : Matrix (Fin k) (Fin k) ℤ) ⊗ₖ CartanMatrix.E 8).map
      (Int.cast : ℤ → ℚ)) =
      ((1 : Matrix (Fin k) (Fin k) ℚ) ⊗ₖ
        (CartanMatrix.E 8).map (Int.cast : ℤ → ℚ)) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases hij : i = j <;> simp [hij]
  rw [e8BlockGram, ← Matrix.submatrix_map, hcast]
  exact (e8Kron_posDef k).submatrix (eightBlockEquiv k).injective

/-- `k` orthogonal `E₈` blocks as an integral lattice of rank `8*k`. -/
private noncomputable def e8BlockLattice (k : ℕ) : IntegralLattice (Fin (8 * k) → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin (8 * k))) (e8BlockGram k) (e8BlockGram_isSymm k)

private theorem e8BlockLattice_isEven (k : ℕ) : (e8BlockLattice k).IsEven := by
  rw [e8BlockLattice, isEven_ofGramMatrix_iff]
  intro i
  rw [e8BlockGram_diag]
  exact even_two

private theorem e8BlockLattice_isUnimodular (k : ℕ) :
    (e8BlockLattice k).IsUnimodular := by
  have hdet : (e8BlockLattice k).determinant = 1 := by
    rw [e8BlockLattice, determinant_ofGramMatrix, e8BlockGram_det]
  have : (e8BlockLattice k).IsNondegenerate := by
    refine ⟨(determinant_ne_zero_iff _).mp ?_⟩
    rw [hdet]
    exact one_ne_zero
  rw [isUnimodular_iff_isUnit_determinant, e8BlockLattice, determinant_ofGramMatrix,
    e8BlockGram_det]
  exact isUnit_one

private theorem e8BlockLattice_isPosDef (k : ℕ) : (e8BlockLattice k).IsPosDef := by
  exact (isPosDef_ofGramMatrix_iff _ _ _).mpr (e8BlockGram_posDef k)

/-- The rank of any positive definite even unimodular integral lattice is divisible by eight. -/
theorem eight_dvd_finrank_of_isEven_isUnimodular_isPosDef {V : Type*} [AddCommGroup V]
    [Module ℚ V] (L : IntegralLattice V) (hE : L.IsEven) (hU : L.IsUnimodular)
    (hP : L.IsPosDef) : 8 ∣ Module.finrank ℚ V := by
  obtain ⟨hNull, hNeg⟩ := L.isPosDef_iff_sigNull_eq_zero_and_sigNeg_eq_zero.mp hP
  have hSig := L.signature_sum_eq_finrank
  have hDiv := L.eight_dvd_sigPos_sub_sigNeg_of_isUnimodular hE hU
  simp only [hNull, hNeg, add_zero, Nat.cast_zero, sub_zero] at hSig hDiv
  rw [← hSig]
  exact_mod_cast hDiv

/-- **Positive definite even unimodular lattices exist exactly in ranks divisible by eight.**
The witness at rank `8*k` has `k` orthogonal `E₈` Gram blocks. -/
theorem exists_even_unimodular_posDef_iff (n : ℕ) :
    (∃ L : IntegralLattice (Fin n → ℚ), L.IsEven ∧ L.IsUnimodular ∧ L.IsPosDef) ↔
      8 ∣ n := by
  constructor
  · rintro ⟨L, hE, hU, hP⟩
    simpa [Module.finrank_pi_fintype] using
      L.eight_dvd_finrank_of_isEven_isUnimodular_isPosDef hE hU hP
  · rintro ⟨k, rfl⟩
    simpa only [mul_comm] using
      (⟨e8BlockLattice k, e8BlockLattice_isEven k,
        e8BlockLattice_isUnimodular k, e8BlockLattice_isPosDef k⟩ :
        ∃ L : IntegralLattice (Fin (8 * k) → ℚ),
          L.IsEven ∧ L.IsUnimodular ∧ L.IsPosDef)

end TauCeti.IntegralLattice
