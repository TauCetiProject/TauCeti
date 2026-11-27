/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.ComplexAd
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.FinTwo
public import TauCeti.RepresentationTheory.GL2.CompactCartan

/-!
# The action of `O(2)` on the compact Cartan coordinates

Conjugation by a rotation `g ∈ O(2)` of phase `z(g)` fixes the `H_c`-coordinate and the
coordinate along the identity of a matrix, and multiplies its `X_c`- and `Y_c`-coordinates by
`z(g) ^ 2` and `z(g) ^ (-2)`. The reflection `A = diag(1, -1)` of `O(2)` acts on `𝔤𝔩₂(ℂ)` by
conjugation by `TauCeti.compactCartanReflection`, which exchanges the `X_c`- and `Y_c`-coordinates
and negates the `H_c`-coordinate (`TauCeti.compactCoordX_compactCartanReflection_mul_mul` and its
siblings).

## Main results

* `TauCeti.orthogonalAd_eq_of_det_eq_one`: `Ad g M` for a rotation `g = !![a, -b; b, a]`.
* `TauCeti.compactCoordX_orthogonalAd_of_det_eq_one` and its siblings: the compact Cartan
  coordinates of `Ad g M` for a rotation `g`.
* `TauCeti.orthogonalAd_orthogonalDiagonalReflection`: `Ad A M = A M A`.

## References

* A. W. Knapp, *Local Langlands correspondence: the Archimedean case*, in *Motives*, Proc. Sympos.
  Pure Math. 55, part 2, Amer. Math. Soc., 1994, pp. 393–410, §2, pp. 398–400.
-/

public section

noncomputable section

open Complex Matrix

namespace TauCeti

/-- `Ad g M` for a rotation `g = !![a, -b; b, a]`. -/
theorem orthogonalAd_eq_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    orthogonalAd (Fin 2) g M =
      !![((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ), -((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ);
          ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ), ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)] * M *
        !![((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ), ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ);
          -((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ), ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)] := by
  rw [orthogonalAd_apply, orthogonalComplexMatrix_eq_of_det_eq_one hg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Conjugation by a rotation fixes the `H_c`-coordinate. -/
theorem compactCoordH_orthogonalAd_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordH (orthogonalAd (Fin 2) g M) = compactCoordH M := by
  have h₀ := ofReal_sq_add_ofReal_sq_of_mem_orthogonalGroup_fin_two g.property
  rw [orthogonalAd_eq_of_det_eq_one hg, eta_fin_two M]
  simp [compactCoordH_apply]
  grind

/-- Conjugation by a rotation multiplies the `X_c`-coordinate by `z(g) ^ 2`. -/
theorem compactCoordX_orthogonalAd_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordX (orthogonalAd (Fin 2) g M) = orthogonalPhase g ^ 2 * compactCoordX M := by
  have := I_sq
  rw [orthogonalAd_eq_of_det_eq_one hg, eta_fin_two M]
  simp [compactCoordX_apply, orthogonalPhase_def]
  grind

/-- Conjugation by a rotation multiplies the `Y_c`-coordinate by `z(g) ^ (-2)`. -/
theorem compactCoordY_orthogonalAd_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordY (orthogonalAd (Fin 2) g M) = (orthogonalPhase g)⁻¹ ^ 2 * compactCoordY M := by
  have := I_sq
  rw [orthogonalAd_eq_of_det_eq_one hg, eta_fin_two M]
  simp [compactCoordY_apply, inv_orthogonalPhase]
  grind

/-- Conjugation by a rotation fixes the coordinate along the identity. -/
theorem compactCoordOne_orthogonalAd_of_det_eq_one {g : orthogonalGroup (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    compactCoordOne (orthogonalAd (Fin 2) g M) = compactCoordOne M := by
  have h₀ := ofReal_sq_add_ofReal_sq_of_mem_orthogonalGroup_fin_two g.property
  rw [orthogonalAd_eq_of_det_eq_one hg, eta_fin_two M]
  simp [compactCoordOne_apply]
  grind

/-- The complex matrix of the reflection `A = diag(1, -1)` of `O(2)` is
`TauCeti.compactCartanReflection`. -/
@[simp]
theorem orthogonalComplexMatrix_orthogonalDiagonalReflection :
    (orthogonalComplexMatrix (orthogonalDiagonalReflection ℝ (1 : Fin 2)) :
      Matrix (Fin 2) (Fin 2) ℂ) = compactCartanReflection := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [compactCartanReflection_def]

/-- The reflection `A = diag(1, -1)` of `O(2)` acts on `𝔤𝔩₂(ℂ)` by `M ↦ A M A`. -/
theorem orthogonalAd_orthogonalDiagonalReflection (M : Matrix (Fin 2) (Fin 2) ℂ) :
    orthogonalAd (Fin 2) (orthogonalDiagonalReflection ℝ 1) M =
      compactCartanReflection * M * compactCartanReflection := by
  rw [orthogonalAd_apply, orthogonalComplexMatrix_orthogonalDiagonalReflection]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [compactCartanReflection_def]

end TauCeti
