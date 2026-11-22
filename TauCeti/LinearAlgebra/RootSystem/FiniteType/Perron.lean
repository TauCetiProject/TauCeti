/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Order.Star.Real
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic

/-!
# The Perron eigenvector of a finite-type Cartan matrix

Let `A` be an indecomposable integer matrix of finite type on at least two indices. The matrix
`2 - A` has zero diagonal and nonnegative off-diagonal entries, and its positive entries connect
all indices, so it is irreducible and the Perron–Frobenius theorem gives it an eigenvector `y`
with strictly positive entries, for a strictly positive eigenvalue `r`. Then `A y = κ y` with
`κ = 2 - r < 2`. Positive definiteness of the symmetrization of `A` evaluated at `y` gives
`0 < κ`.

This positive eigenvector is the input of Steinberg's construction of a regular eigenvector of a
bipartite Coxeter element: the colour classes of `y` span the plane on which the Coxeter element
acts as a rotation.

## Main results

* `TauCeti.IsFiniteType.exists_pos_mulVec_eq_smul` and
  `TauCeti.IsFiniteType.exists_pos_vecMul_eq_smul`: an indecomposable finite-type matrix on at
  least two indices has a right and a left eigenvector with strictly positive real entries, for
  an eigenvalue strictly between `0` and `2`.

## References

* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §3.17.
-/

public section

open Matrix Relation

namespace TauCeti

namespace IsFiniteType

variable {B : Type*} {A : Matrix B B ℤ}

/-- The real matrix `2 - A`, with zero diagonal and entries `-A i j` off the diagonal. -/
private noncomputable def offDiagNeg [DecidableEq B] (A : Matrix B B ℤ) : Matrix B B ℝ :=
  of fun i j ↦ if i = j then 0 else -(A i j : ℝ)

private theorem map_intCast_eq_two_smul_one_sub [DecidableEq B] (hdiag : ∀ i, A i i = 2) :
    A.map (Int.cast : ℤ → ℝ) = (2 : ℝ) • (1 : Matrix B B ℝ) - offDiagNeg A := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [offDiagNeg, hdiag]
  · simp [offDiagNeg, hij]

/-- For an indecomposable matrix on at least two indices with nonpositive off-diagonal entries, the
matrix `2 - A` is irreducible. -/
private theorem isIrreducible_offDiagNeg [Finite B] [DecidableEq B] [Nontrivial B]
    (hle : ∀ i j, i ≠ j → A i j ≤ 0) (hA : A.IsIndecomposable) : (offDiagNeg A).IsIrreducible := by
  have hnonneg (i j : B) : 0 ≤ offDiagNeg A i j := by
    by_cases hij : i = j
    · simp [offDiagNeg, hij]
    · simpa [offDiagNeg, hij] using hle i j hij
  refine (isIrreducible_iff_forall_transGen hnonneg).2 ?_
  -- The nonzero entries of `A` connect all indices; off the diagonal they are positive entries
  -- of `2 - A`, and the diagonal steps can be dropped.
  have hrefl (i j : B) : ReflTransGen (fun i j ↦ 0 < offDiagNeg A i j) i j := by
    induction (isIndecomposable_iff_reflTransGen A).1 hA i j with
    | refl => exact .refl
    | @tail k l _ hkl ih =>
      by_cases hkl' : k = l
      · exact hkl' ▸ ih
      · refine ih.tail ?_
        simpa [offDiagNeg, hkl'] using
          lt_of_le_of_ne (hle k l hkl') hkl
  have htrans {i j : B} (hij : i ≠ j) : TransGen (fun i j ↦ 0 < offDiagNeg A i j) i j := by
    rcases (hrefl i j).cases_head with rfl | ⟨k, hik, hkj⟩
    · exact absurd rfl hij
    · exact TransGen.head' hik hkj
  intro i j
  obtain ⟨k, hk⟩ := exists_ne j
  exact TransGen.trans_right (hrefl i j) ((htrans hk.symm).trans (htrans hk))

/-- **The Perron eigenvector of a finite-type Cartan matrix.** An indecomposable integer matrix of
finite type on at least two indices has an eigenvector whose entries are strictly positive reals,
for a real eigenvalue `κ` with `0 < κ < 2`. -/
theorem exists_pos_mulVec_eq_smul [Fintype B] [Nontrivial B] (h : IsFiniteType A)
    (hA : A.IsIndecomposable) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 2 ∧
      ∃ y : B → ℝ, (∀ i, 0 < y i) ∧ A.map (Int.cast : ℤ → ℝ) *ᵥ y = κ • y := by
  classical
  obtain ⟨r, hr, y, hy, hNy⟩ :=
    (isIrreducible_offDiagNeg h.isGeneralizedCartan.offDiag_nonpos hA).exists_mulVec_eq_smul
  have hAy : A.map (Int.cast : ℤ → ℝ) *ᵥ y = (2 - r) • y := by
    rw [map_intCast_eq_two_smul_one_sub h.isGeneralizedCartan.diag, sub_mulVec, smul_mulVec,
      one_mulVec, hNy, sub_smul]
  refine ⟨2 - r, ?_, by linarith, y, hy, hAy⟩
  -- Evaluate the positive definite symmetrization `D A` at `y`: it is `(2 - r) ∑ d i * y i ^ 2`.
  obtain ⟨d, hd, hpd⟩ := h.exists_symmetrizer
  have hpdR := (TauCeti.Matrix.posDef_map_ratCast_iff (K := ℝ)).2 hpd
  obtain ⟨i₀⟩ := (inferInstance : Nonempty B)
  have hy0 : y ≠ 0 := fun h0 ↦ (hy i₀).ne' (by simp [h0])
  have hpos := hpdR.dotProduct_mulVec_pos hy0
  have hS : (of fun i j ↦ d i * (A i j : ℚ)).map (Rat.cast : ℚ → ℝ) =
      diagonal (fun i ↦ (d i : ℝ)) * A.map (Int.cast : ℤ → ℝ) := by
    ext i j
    simp
  rw [hS, ← mulVec_mulVec, hAy, mulVec_smul, dotProduct_smul, star_trivial] at hpos
  have hsum : 0 < y ⬝ᵥ (diagonal (fun i ↦ (d i : ℝ)) *ᵥ y) := by
    simp only [mulVec_diagonal, dotProduct]
    exact Finset.sum_pos (fun i _ ↦ mul_pos (hy i) (mul_pos (by exact_mod_cast hd i) (hy i)))
      Finset.univ_nonempty
  rw [smul_eq_mul] at hpos
  exact pos_of_mul_pos_left hpos hsum.le

/-- **The left Perron eigenvector of a finite-type Cartan matrix.** An indecomposable integer
matrix of finite type on at least two indices has a left eigenvector whose entries are strictly
positive reals, for a real eigenvalue `κ` with `0 < κ < 2`. -/
theorem exists_pos_vecMul_eq_smul [Fintype B] [Nontrivial B] (h : IsFiniteType A)
    (hA : A.IsIndecomposable) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 2 ∧
      ∃ y : B → ℝ, (∀ i, 0 < y i) ∧ y ᵥ* A.map (Int.cast : ℤ → ℝ) = κ • y := by
  obtain ⟨κ, hκ, hκ2, y, hy, hAy⟩ := h.transpose.exists_pos_mulVec_eq_smul hA.transpose
  exact ⟨κ, hκ, hκ2, y, hy, by rwa [← mulVec_transpose, ← transpose_map]⟩

end IsFiniteType

end TauCeti
