/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
public import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.LinearAlgebra.BilinearForm.Characteristic
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Two dyadic phenomena for bilinear forms

The hyperbolic plane over `ℤ_[2]`, obtained from the integer Gram matrix
`!![0, 1; 1, 0]`, has no orthogonal basis. It illustrates why diagonalization of
integral bilinear forms over `ℤ_[p]` requires the prime `p` to be odd.

Odd unimodular forms over `ℤ_[2]` do have orthogonal bases, but unlike at odd primes their rank
and determinant square class do not classify them: the oddity, the trace of a diagonal Gram matrix
modulo `8`, is a further invariant. The forms `⟨1, 1⟩` and `⟨3, 3⟩` are separated by it.

## Main results

* `TauCeti.not_exists_orthogonal_basis_hyperbolic_padicInt_two`: the hyperbolic plane over
  `ℤ_[2]` has no orthogonal basis.
* `TauCeti.not_equivalent_toBilin'_diagonal_one_one_three_three_padicInt_two`: the forms `⟨1, 1⟩`
  and `⟨3, 3⟩` over `ℤ_[2]` are not isometric.
-/

public section

open Module

namespace TauCeti

/-- **The dyadic trap.** The hyperbolic plane over `ℤ_[2]` has no orthogonal basis. -/
theorem not_exists_orthogonal_basis_hyperbolic_padicInt_two :
    ¬ ∃ b : Basis (Fin 2) ℤ_[2] (Fin 2 → ℤ_[2]),
      (Matrix.toBilin' ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).map
        (Int.cast : ℤ → ℤ_[2]))).iIsOrtho b := by
  rintro ⟨b, hb⟩
  have hmat : ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → ℤ_[2])) = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  exact PadicInt.not_isUnit_two
    (LinearMap.BilinForm.isUnit_two_of_iIsOrtho_toBilin'_hyperbolic (b := b)
      (by simpa [hmat] using hb))

/-- **The determinant does not classify odd unimodular forms over `ℤ_[2]`.** The diagonal forms
`⟨1, 1⟩` and `⟨3, 3⟩` have the same rank and the square determinants `1` and `9`, but they are not
isometric: their oddities, the traces `2` and `6` of their Gram matrices, differ modulo `8`. -/
theorem not_equivalent_toBilin'_diagonal_one_one_three_three_padicInt_two :
    ¬ (Matrix.toBilin' (Matrix.diagonal ![(1 : ℤ_[2]), 1])).Equivalent
      (Matrix.toBilin' (Matrix.diagonal ![(3 : ℤ_[2]), 3])) := by
  intro h
  let b := Pi.basisFun ℤ_[2] (Fin 2)
  have hdiag (d : Fin 2 → ℤ_[2]) (i j : Fin 2) :
      Matrix.toBilin' (Matrix.diagonal d) (b i) (b j) = if i = j then d i else 0 := by
    simp [b, Matrix.toBilin'_single, Matrix.diagonal_apply]
  have hortho (d : Fin 2 → ℤ_[2]) : (Matrix.toBilin' (Matrix.diagonal d)).iIsOrtho b :=
    LinearMap.BilinForm.iIsOrtho_def.mpr fun i j hij ↦ by simp [hdiag, hij]
  have : (Matrix.toBilin' (Matrix.diagonal ![(1 : ℤ_[2]), 1])).IsPerfPair :=
    b.isPerfPair_of_apply_eq_ite _ 1 fun i j ↦ by
      fin_cases i <;> fin_cases j <;> simp [hdiag]
  have h8 := h.eight_dvd_sum_apply_self_sub_sum_apply_self PadicInt.two_dvd_sq_sub_self
    (hortho _) (hortho _)
  simp only [hdiag, ↓reduceIte, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h8
  norm_num at h8
  have h8' := map_dvd (PadicInt.toZModPow 3) h8
  simp only [map_ofNat] at h8'
  obtain ⟨k, hk⟩ := h8'
  revert k
  decide

end TauCeti
