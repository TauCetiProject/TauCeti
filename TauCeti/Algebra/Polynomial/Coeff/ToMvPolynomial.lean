/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Coefficient vectors under variable embeddings

The embedding `Polynomial.toMvPolynomial i` reindexes the native coefficient vector
by sending an exponent `n` to the multivariate exponent `Finsupp.single i n`.
This description lets coefficient constructions commute with placement in one coordinate.
In particular, the partial degree of the placed polynomial in `Xᵢ` is its degree.
-/

public section

namespace Polynomial

variable {R σ : Type*} [CommSemiring R]

/-- Placement in one coordinate reindexes the native coefficient vector by the
corresponding single-coordinate exponent embedding. -/
theorem coeff_toMvPolynomial_eq_embDomain (p : Polynomial R) (i : σ) :
    AddMonoidAlgebra.coeff (p.toMvPolynomial i) =
      p.toFinsupp.coeff.embDomain ⟨Finsupp.single i, Finsupp.single_injective i⟩ := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [_root_.map_add, AddMonoidAlgebra.coeff_add, Polynomial.toFinsupp_add,
      Finsupp.embDomain_add, hp, hq]
  | monomial n c =>
    simp [← Polynomial.C_mul_X_pow_eq_monomial, MvPolynomial.C_mul_X_pow_eq_monomial,
      ← MvPolynomial.single_eq_monomial,
      AddMonoidAlgebra.coeff_single, Finsupp.embDomain_single]

/-- Placement in the coordinate `Xᵢ` turns the degree into the partial degree in `Xᵢ`. -/
@[simp]
theorem degreeOf_toMvPolynomial (p : Polynomial R) (i : σ) :
    (p.toMvPolynomial i).degreeOf i = p.natDegree := by
  rw [toMvPolynomial_eq_rename_comp, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    MvPolynomial.degreeOf_rename_of_injective (f := fun _ : Unit ↦ i) (fun _ _ _ ↦ rfl) ()]
  refine le_antisymm (MvPolynomial.degreeOf_le_iff.2 fun m hm ↦ ?_) ?_
  · rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_uniqueAlgEquiv_symm] at hm
    exact le_natDegree_of_ne_zero hm
  · rcases eq_or_ne p 0 with rfl | hp
    · simp
    · have hm : Finsupp.single () p.natDegree ∈
          ((MvPolynomial.uniqueAlgEquiv R Unit).symm p).support := by
        rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_uniqueAlgEquiv_symm,
          Finsupp.single_eq_same]
        exact leadingCoeff_ne_zero.2 hp
      simpa using MvPolynomial.monomial_le_degreeOf () hm

end Polynomial
