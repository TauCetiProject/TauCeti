/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.ValuationRing
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Matrix.BilinearForm
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
* `TauCeti.IntegralLattice.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow`: the same
  diagonal Jordan form indexed by `Fin n` whenever `finrank ℤ L = n`.
* `TauCeti.IntegralLattice.exists_unit_sq_mul_determinant_eq_prod_localIntegralForm`: for any
  orthogonal basis of `L_p` (at any prime `p`), the product of its diagonal entries equals a unit
  square times the signed determinant of `L`.
* `TauCeti.IntegralLattice.exists_unit_sq_mul_determinant_eq_prod_mul_pow`: in a diagonal Jordan
  basis with entries `uᵢ · p^{kᵢ}`, the product `(∏ᵢ uᵢ) · p^{∑ᵢ kᵢ}` equals a unit square times
  the signed determinant of `L`.

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

/-- **Diagonal Jordan form indexed by `Fin n`.** For an odd prime `p` and a nondegenerate integral
lattice of rank `n`, the localized integral form has an orthogonal `Fin n`-indexed basis whose
diagonal entries are units of `ℤ_p` times powers of `p`. -/
theorem exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow (hp : p ≠ 2)
    (hL : L.form.Nondegenerate) {n : ℕ} (hn : finrank ℤ L = n) :
    ∃ (b : Basis (Fin n) ℤ_[p] (L.LocalCarrier p)) (u : Fin n → ℤ_[p]ˣ) (k : Fin n → ℕ),
      (L.localIntegralForm p).iIsOrtho b ∧
        ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i := by
  have hnL : finrank ℤ_[p] (L.LocalCarrier p) = n := by
    rw [Module.finrank_eq_card_basis ((Module.finBasis ℤ L).baseChange ℤ_[p]), Fintype.card_fin, hn]
  obtain ⟨b', u', k', hb', hbu'⟩ :=
    L.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp hL
  refine ⟨b'.reindex (finCongr hnL), fun i ↦ u' ((finCongr hnL).symm i),
    fun i ↦ k' ((finCongr hnL).symm i), hb'.reindex (finCongr hnL), fun i ↦ ?_⟩
  simpa [Basis.reindex_apply] using hbu' ((finCongr hnL).symm i)

/-- **Local determinant in an orthogonal basis.** At any prime `p`, the product of the diagonal
entries of an orthogonal basis `b` of `L_p` equals the signed determinant of `L` up to the square
of a `p`-adic unit. -/
theorem exists_unit_sq_mul_determinant_eq_prod_localIntegralForm {ι : Type*} [Fintype ι]
    {b : Basis ι ℤ_[p] (L.LocalCarrier p)} (hb : (L.localIntegralForm p).iIsOrtho b) :
    ∃ d : ℤ_[p]ˣ, (d : ℤ_[p]) ^ 2 * (L.determinant : ℤ_[p]) =
      ∏ i, L.localIntegralForm p (b i) (b i) := by
  classical
  let b₀ := (Module.finBasis ℤ L).baseChange ℤ_[p]
  let e : Fin (finrank ℤ L) ≃ ι := b₀.indexEquiv b
  have hdet₀ : ((L.localIntegralForm p).toMatrix b₀).det = (L.determinant : ℤ_[p]) :=
    L.det_toMatrix_localIntegralForm p _
  have hdet_b : ((L.localIntegralForm p).toMatrix (b.reindex e.symm)).det =
      ∏ i, L.localIntegralForm p (b i) (b i) := by
    rw [LinearMap.BilinForm.det_toMatrix_reindex, hb.det_toMatrix]
  have hchg := LinearMap.BilinForm.det_toMatrix_eq_det_sq_mul_det b₀ (b.reindex e.symm)
    (L.localIntegralForm p)
  have hu_chg : IsUnit (b₀.toMatrix (b.reindex e.symm)).det := b₀.isUnit_det _
  refine ⟨hu_chg.unit, ?_⟩
  rw [IsUnit.unit_spec, ← hdet₀, ← hchg, hdet_b]

/-- **Local determinant in a diagonal Jordan basis.** At any prime `p`, if `b` is an orthogonal
basis of `L_p` with diagonal entries `uᵢ · p^{kᵢ}`, then `(∏ᵢ uᵢ) · p^{∑ᵢ kᵢ}` equals the signed
determinant of `L` up to the square of a `p`-adic unit. -/
theorem exists_unit_sq_mul_determinant_eq_prod_mul_pow {ι : Type*} [Fintype ι]
    {b : Basis ι ℤ_[p] (L.LocalCarrier p)} {u : ι → ℤ_[p]ˣ} {k : ι → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) :
    ∃ d : ℤ_[p]ˣ, (d : ℤ_[p]) ^ 2 * (L.determinant : ℤ_[p]) =
      (∏ i, (u i : ℤ_[p])) * (p : ℤ_[p]) ^ (∑ i, k i) := by
  obtain ⟨d, hd⟩ := L.exists_unit_sq_mul_determinant_eq_prod_localIntegralForm hb
  exact ⟨d, by simpa only [hbu, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] using hd⟩

end IntegralLattice

end TauCeti
