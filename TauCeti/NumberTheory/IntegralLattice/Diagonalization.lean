/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.ValuationRing
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Diagonalizing an integral lattice at an odd prime

Let `L` be an integral lattice and `p` an odd prime. Since `ℤ_p` is a valuation ring in which `2`
is a unit, the localized integral form on `L_p = ℤ_p ⊗[ℤ] L` has an orthogonal basis
(`TauCeti.IntegralLattice.exists_basis_iIsOrtho_localIntegralForm`). When `L` is nondegenerate
every diagonal entry is nonzero, hence of the form `u · p^k` with `u` a unit of `ℤ_p`
(`TauCeti.IntegralLattice.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow`). These are the
Jordan data at an odd prime in diagonal form: the basis vectors with exponent `k` span a
`p^k`-modular orthogonal summand, so grouping them by `k` gives the Jordan splitting, and the rank
and the unit determinant of each constituent are read off the diagonal.

## Main results

* `TauCeti.IntegralLattice.exists_basis_iIsOrtho_localIntegralForm`: at an odd prime the
  localized integral form of a lattice has an orthogonal basis.
* `TauCeti.IntegralLattice.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow`: for a
  nondegenerate lattice the diagonal entries are units times powers of `p`.
## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §91C and 92:1.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

open Module

namespace TauCeti

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

namespace IntegralLattice

variable (L : IntegralLattice V) {p : ℕ} [Fact p.Prime]

/-- **Diagonalization at an odd prime.** For an odd prime `p` the localized integral form of an
integral lattice has an orthogonal basis over `ℤ_p`. -/
theorem exists_basis_iIsOrtho_localIntegralForm (hp : p ≠ 2) :
    ∃ b : Basis (Fin (finrank ℤ_[p] (L.LocalCarrier p))) ℤ_[p] (L.LocalCarrier p),
      (L.localIntegralForm p).iIsOrtho b :=
  (L.isSymm_localIntegralForm p).exists_orthogonal_basis_of_isUnit_two (PadicInt.isUnit_two hp)

/-- **Diagonal Jordan form at an odd prime.** For an odd prime `p` and a nondegenerate integral
lattice, the localized integral form has an orthogonal basis whose diagonal entries are units of
`ℤ_p` times powers of `p`. -/
theorem exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow (hp : p ≠ 2)
    (hL : L.form.Nondegenerate) :
    ∃ (b : Basis (Fin (finrank ℤ_[p] (L.LocalCarrier p))) ℤ_[p] (L.LocalCarrier p))
      (u : Fin (finrank ℤ_[p] (L.LocalCarrier p)) → ℤ_[p]ˣ)
      (k : Fin (finrank ℤ_[p] (L.LocalCarrier p)) → ℕ),
      (L.localIntegralForm p).iIsOrtho b ∧
        ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i := by
  obtain ⟨b, hb⟩ := L.exists_basis_iIsOrtho_localIntegralForm hp
  have hne i : L.localIntegralForm p (b i) (b i) ≠ 0 :=
    hb.not_isOrtho_basis_self_of_nondegenerate ((L.nondegenerate_localIntegralForm_iff p).mpr hL) i
  exact ⟨b, fun i ↦ _root_.PadicInt.unitCoeff (hne i),
    fun i ↦ (L.localIntegralForm p (b i) (b i)).valuation, hb,
    fun i ↦ _root_.PadicInt.unitCoeff_spec (hne i)⟩

end IntegralLattice

end TauCeti
