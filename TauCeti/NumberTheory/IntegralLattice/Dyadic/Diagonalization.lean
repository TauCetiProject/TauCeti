/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Odd
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
public import TauCeti.NumberTheory.IntegralLattice.Localization.Ideals
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import Mathlib.LinearAlgebra.Determinant

/-!
# Odd unimodular dyadic lattices are diagonalizable

An integral lattice with unit determinant at `2` has a unit-diagonal orthogonal
basis over `ℤ₂` precisely when it is odd or has rank zero. This separates the odd
unimodular dyadic forms from the even ones, which require binary constituents.
The basis and its unit self-pairings are supplied on the actual integral
localization, not just on its rational quadratic space.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

namespace TauCeti.IntegralLattice

open Module

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- An odd lattice with unit determinant at `2` has an orthogonal basis of its
integral dyadic localization, with every self-pairing a unit. -/
theorem exists_basis_iIsOrtho_isUnit_localIntegralForm_two
    (L : IntegralLattice V) (hdet : IsUnit (L.determinant : ℤ_[2])) (hodd : ¬ L.IsEven) :
    ∃ b : Basis (Fin (finrank ℤ L)) ℤ_[2] (L.LocalCarrier 2),
      (L.localIntegralForm 2).iIsOrtho b ∧
        ∀ i, IsUnit (L.localIntegralForm 2 (b i) (b i)) := by
  classical
  let b := (Module.finBasis ℤ L).baseChange ℤ_[2]
  have hperf : (L.localIntegralForm 2).IsPerfPair :=
    b.isPerfPair_of_isUnit_det _
      (L.det_toMatrix_localIntegralForm 2 (Module.finBasis ℤ L) ▸ hdet)
  exact BilinForm.exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self
    (L.isSymm_localIntegralForm 2) b
    (L.not_isEven_iff_exists_isUnit_localIntegralForm_two.mp hodd)

/-- A lattice unimodular at `2` is diagonalizable over `ℤ₂` exactly when it is odd
or has rank zero. In positive rank this excludes every even unimodular lattice. -/
theorem exists_basis_iIsOrtho_localIntegralForm_two_iff
    (L : IntegralLattice V) (hdet : IsUnit (L.determinant : ℤ_[2])) :
    (∃ b : Basis (Fin (finrank ℤ L)) ℤ_[2] (L.LocalCarrier 2),
      (L.localIntegralForm 2).iIsOrtho b) ↔ finrank ℤ L = 0 ∨ ¬ L.IsEven := by
  classical
  constructor
  · rintro ⟨b, hb⟩
    by_cases hn : finrank ℤ L = 0
    · exact Or.inl hn
    have hdet' : IsUnit ((L.localIntegralForm 2).toMatrix b).det := by
      rw [LinearMap.BilinForm.det_toMatrix_eq_det_sq_mul_det
        ((Module.finBasis ℤ L).baseChange ℤ_[2]) b,
        L.det_toMatrix_localIntegralForm 2 (Module.finBasis ℤ L)]
      exact (((Module.finBasis ℤ L).baseChange ℤ_[2]).isUnit_det b).pow 2 |>.mul hdet
    rw [hb.toMatrix_eq_diagonal, Matrix.det_diagonal] at hdet'
    let i : Fin (finrank ℤ L) := ⟨0, Nat.pos_of_ne_zero hn⟩
    refine Or.inr (L.not_isEven_iff_exists_isUnit_localIntegralForm_two.mpr ⟨b i, ?_⟩)
    exact isUnit_of_dvd_unit
      (Finset.dvd_prod_of_mem (fun j ↦ L.localIntegralForm 2 (b j) (b j))
        (Finset.mem_univ i)) hdet'
  · rintro (hn | hodd)
    · refine ⟨(Module.finBasis ℤ L).baseChange ℤ_[2], ?_⟩
      intro i
      exact Fin.elim0 (Fin.cast hn i)
    · obtain ⟨b, hb, -⟩ := L.exists_basis_iIsOrtho_isUnit_localIntegralForm_two hdet hodd
      exact ⟨b, hb⟩

end TauCeti.IntegralLattice

end
