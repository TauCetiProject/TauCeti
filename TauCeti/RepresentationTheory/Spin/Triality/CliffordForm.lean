/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.TrilinearForm

/-!
# The rank-four normalization of the Clifford-multiplication trilinear form

For a polarization whose isotropic summand `W` has a basis `w₁, …, w₄`, the Clifford-multiplication
trilinear form `T (v, s, t) = ⟨c(v) s, t⟩` of
`TauCeti.RepresentationTheory.Spin.TrilinearForm` is evaluated on the vacuum `1` and the product
`w₂ w₃ w₄`. For the top-degree coefficient, `T (w₁, 1, w₂ w₃ w₄) = 1`, and for any functional,
`T (w₂, 1, w₂ w₃ w₄) = 0`. When the polarization also has no line summand (`dim V = 8`), these are
the normalizations of the candidate triality form of `Spin₈` on the vector representation and its
two half-spin representations.

## Main results

* `TauCeti.SpinPolarizationData.spinTrilinearForm_coord_univ_basis_zero_one_ι_mul_ι_mul_ι_eq_one`:
  `T (w₁, 1, w₂ w₃ w₄) = 1` for the top-degree coefficient.
* `TauCeti.SpinPolarizationData.spinTrilinearForm_basis_one_one_ι_mul_ι_mul_ι_eq_zero`:
  `T (w₂, 1, w₂ w₃ w₄) = 0` for any functional.

## References

* J. C. Baez, *The Octonions*, Bull. Amer. Math. Soc. 39 (2002), §2.4.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20, §20.3.
-/

public section

open CliffordAlgebra Module

namespace TauCeti.SpinPolarizationData

universe u v

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {φ : Module.Dual K (ExteriorAlgebra K P.W)}

/-- In rank four, `w₂ w₃ w₄` is the exterior-basis vector of the index set `univ ∖ {0}`. -/
private theorem ι_mul_ι_mul_ι_eq_basis_erase_zero (b : Module.Basis (Fin 4) K P.W) :
    ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2) * ExteriorAlgebra.ι K (b 3) =
      b.ExteriorAlgebra (Finset.univ.erase 0) := by
  rw [mul_assoc, ← ExteriorAlgebra.basis_singleton b 3, ExteriorAlgebra.ι_mul_basis,
    ite_eq_right (by decide), mul_smul_comm, ExteriorAlgebra.ι_mul_basis,
    ite_eq_right (by decide), smul_smul]
  -- Both shuffle signs are `+1`, and the index set `{1, 2, 3}` is `univ ∖ {0}`.
  convert one_smul ℤˣ (b.ExteriorAlgebra (Finset.univ.erase (0 : Fin 4))) using 3
  · simp only [ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt]
    decide
  · decide

/-- **In rank four, the top-degree trilinear form satisfies `T (w₁, 1, w₂ w₃ w₄) = 1`**, for a
basis `w₁, …, w₄` of the isotropic summand and its top-degree coefficient. -/
theorem spinTrilinearForm_coord_univ_basis_zero_one_ι_mul_ι_mul_ι_eq_one
    (b : Module.Basis (Fin 4) K P.W) :
    P.spinTrilinearForm (b.ExteriorAlgebra.coord Finset.univ) (b 0 : V) 1
        (ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2) * ExteriorAlgebra.ι K (b 3)) =
      1 := by
  rw [ι_mul_ι_mul_ι_eq_basis_erase_zero, spinTrilinearForm_coord_univ_basis_erase,
    ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt]
  simp

/-- **In rank four, `T (w₂, 1, w₂ w₃ w₄) = 0` for any functional `φ`**, since
`w₂ ∧ w₂ w₃ w₄ = 0`. -/
theorem spinTrilinearForm_basis_one_one_ι_mul_ι_mul_ι_eq_zero
    (b : Module.Basis (Fin 4) K P.W) :
    P.spinTrilinearForm φ (b 1 : V) 1
        (ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2) * ExteriorAlgebra.ι K (b 3)) =
      0 := by
  rw [ι_mul_ι_mul_ι_eq_basis_erase_zero]
  exact P.spinTrilinearForm_basis_one_basis_eq_zero_of_mem b φ (by decide)

end TauCeti.SpinPolarizationData
