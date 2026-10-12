/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
public import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# A dyadic bilinear form without an orthogonal basis

The hyperbolic plane over `ℤ_[2]`, obtained from the integer Gram matrix
`!![0, 1; 1, 0]`, has no orthogonal basis. It illustrates why diagonalization of
integral bilinear forms over `ℤ_[p]` requires the prime `p` to be odd.

## Main result

* `TauCeti.not_exists_orthogonal_basis_hyperbolic_padicInt_two`: the hyperbolic plane over
  `ℤ_[2]` has no orthogonal basis.
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
  have hnon : ¬ IsUnit (2 : ℤ_[2]) := by
    intro h
    have hnorm := PadicInt.isUnit_iff.mp h
    have hc : Nat.Coprime 2 2 :=
      (PadicInt.norm_natCast_eq_one_iff (p := 2) (n := 2)).mp (by simpa using hnorm)
    exact (by decide : ¬ Nat.Coprime 2 2) hc
  have hmat : ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → ℤ_[2])) = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  exact hnon (LinearMap.BilinForm.isUnit_two_of_iIsOrtho_toBilin'_hyperbolic (b := b)
    (by simpa [hmat] using hb))

end TauCeti
