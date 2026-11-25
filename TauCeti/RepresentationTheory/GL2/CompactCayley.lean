/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GL2.CompactCartan
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Cayley change from the split to the compact Cartan basis of `𝔤𝔩₂(ℂ)`

The compact Cartan basis `H_c = -iJ`, `X_c = (A + iB) / 2`, `Y_c = (A - iB) / 2` of `𝔰𝔩₂(ℂ)`
(`TauCeti.compactCartanH` and its siblings), with `J = E₁₂ - E₂₁`, `A = diag(1, -1)` and
`B = E₁₂ + E₂₁`, is conjugate to the split triple `(diag(1, -1), E₁₂, E₂₁)` by the explicit Cayley
matrix `C = [[1, 1], [i, -i]]` (`TauCeti.compactCayley`), whose columns `(1, i)` and `(1, -i)` are
eigenvectors of `H_c` for the eigenvalues `1` and `-1`:

`C diag(1, -1) C⁻¹ = H_c`, `C E₁₂ C⁻¹ = X_c`, `C E₂₁ C⁻¹ = Y_c`.

The compact-basis symbol `H_c` is therefore a different matrix from `diag(1, -1)`, conjugate to
it over `ℂ` but not over `ℝ`.

## Main results

* `TauCeti.compactCayley`: the matrix `C`, with `det C = -2i` (`TauCeti.det_compactCayley`) and
  `C⁻¹ = (1 / 2) [[1, -i], [1, i]]` (`TauCeti.compactCayley_inv`).
* `TauCeti.compactCayley_mul_compactCartanReflection`,
  `TauCeti.compactCayley_mul_single_zero_one`, `TauCeti.compactCayley_mul_single_one_zero`: the
  intertwining relations `C M = M_c C`.
* `TauCeti.compactCayley_conj_compactCartanReflection`,
  `TauCeti.compactCayley_conj_single_zero_one`, `TauCeti.compactCayley_conj_single_one_zero`: the
  conjugation relations `C M C⁻¹ = M_c`.

## References

* A. W. Knapp, *Local Langlands correspondence: the Archimedean case*, in *Motives*, Proc. Sympos.
  Pure Math. 55, part 2, Amer. Math. Soc., 1994, pp. 393–410, §2, pp. 398–400.
-/

public section

noncomputable section

open Complex Matrix

namespace TauCeti

/-- The **Cayley matrix** `C = [[1, 1], [i, -i]]`, whose columns are eigenvectors of `H_c` for the
eigenvalues `1` and `-1`. -/
def compactCayley : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; I, -I]

theorem compactCayley_def : compactCayley = !![1, 1; I, -I] :=
  (rfl)

/-- `det C = -2i`. -/
@[simp]
theorem det_compactCayley : compactCayley.det = -2 * I := by
  rw [compactCayley_def, det_fin_two_of]
  ring

theorem isUnit_det_compactCayley : IsUnit compactCayley.det := by
  rw [det_compactCayley]
  exact (mul_ne_zero (by norm_num) I_ne_zero).isUnit

/-- `C⁻¹ = (1 / 2) [[1, -i], [1, i]]`. -/
theorem compactCayley_inv : compactCayley⁻¹ = (1 / 2 : ℂ) • !![1, -I; 1, I] := by
  refine inv_eq_left_inv ?_
  rw [compactCayley_def]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Complex.ext_iff, mul_apply, Fin.sum_univ_two]

/-- `C diag(1, -1) = H_c C`. -/
theorem compactCayley_mul_compactCartanReflection :
    compactCayley * compactCartanReflection = compactCartanH * compactCayley := by
  rw [compactCayley_def, compactCartanReflection_def, compactCartanH_def]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Complex.ext_iff, mul_apply, Fin.sum_univ_two]

/-- `C E₁₂ = X_c C`. -/
theorem compactCayley_mul_single_zero_one :
    compactCayley * single 0 1 1 = compactCartanX * compactCayley := by
  rw [compactCayley_def, compactCartanX_def]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Complex.ext_iff, mul_apply, Fin.sum_univ_two]

/-- `C E₂₁ = Y_c C`. -/
theorem compactCayley_mul_single_one_zero :
    compactCayley * single 1 0 1 = compactCartanY * compactCayley := by
  rw [compactCayley_def, compactCartanY_def]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Complex.ext_iff, mul_apply, Fin.sum_univ_two]

private theorem conj_of_mul_eq {M M' : Matrix (Fin 2) (Fin 2) ℂ}
    (h : compactCayley * M = M' * compactCayley) : compactCayley * M * compactCayley⁻¹ = M' := by
  rw [h, mul_nonsing_inv_cancel_right _ _ isUnit_det_compactCayley]

/-- `C diag(1, -1) C⁻¹ = H_c`. -/
theorem compactCayley_conj_compactCartanReflection :
    compactCayley * compactCartanReflection * compactCayley⁻¹ = compactCartanH :=
  conj_of_mul_eq compactCayley_mul_compactCartanReflection

/-- `C E₁₂ C⁻¹ = X_c`. -/
theorem compactCayley_conj_single_zero_one :
    compactCayley * single 0 1 1 * compactCayley⁻¹ = compactCartanX :=
  conj_of_mul_eq compactCayley_mul_single_zero_one

/-- `C E₂₁ C⁻¹ = Y_c`. -/
theorem compactCayley_conj_single_one_zero :
    compactCayley * single 1 0 1 * compactCayley⁻¹ = compactCartanY :=
  conj_of_mul_eq compactCayley_mul_single_one_zero

end TauCeti
