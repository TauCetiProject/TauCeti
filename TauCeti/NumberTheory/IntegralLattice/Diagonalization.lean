/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fintype.Fiber
public import TauCeti.LinearAlgebra.BilinearForm.ValuationRing
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
import TauCeti.LinearAlgebra.BilinearForm.Henselian
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Henselian.Basic

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
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_forall_occCount_eq_and_isSquare`: two
  diagonal Jordan forms at an odd prime are integrally isometric if and only if they have the same
  rank and the same unit determinant square class at every scale `p^m`, `m ≥ 0`.
* `TauCeti.IntegralLattice.exists_unit_determinant_eq_sq_mul_prod`: relation between the signed
  determinant in `ℤ_p` and the diagonal Jordan entries.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §91C and 92:1.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

open Function Module

namespace TauCeti

universe u v

namespace IntegralLattice

section

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
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

/-- The signed determinant of `L` in `ℤ_p` differs from the diagonal Jordan Gram determinant
`(∏ i, u i) · p ^ (∑ i, k i)` by the square of the change-of-basis unit. -/
theorem exists_unit_determinant_eq_sq_mul_prod
    {ι : Type*} [Fintype ι]
    {b : Basis ι ℤ_[p] (L.LocalCarrier p)} {u : ι → ℤ_[p]ˣ} {k : ι → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) :
    ∃ d : ℤ_[p]ˣ,
      (L.determinant : ℤ_[p]) =
        (d : ℤ_[p]) ^ 2 * ((∏ i, (u i : ℤ_[p])) * (p : ℤ_[p]) ^ ∑ i, k i) := by
  classical
  have hcard : Fintype.card ι = finrank ℤ L := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_baseChange]
  let b₀ := ((Module.finBasis ℤ L).baseChange ℤ_[p]).reindex (Fintype.equivFinOfCardEq hcard).symm
  obtain ⟨d, hd⟩ := (LinearMap.BilinForm.Equivalent.refl _).exists_det_eq_unit_sq_mul_det b₀ b
  rw [LinearMap.BilinForm.det_toMatrix_reindex, L.det_toMatrix_localIntegralForm,
    hb.det_toMatrix] at hd
  simp_rw [hbu, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] at hd
  exact ⟨d, hd⟩

end

/-- **Classification of diagonal Jordan forms at an odd prime.** Let `p` be an odd prime and let
`b` and `c` be orthogonal bases of the localizations `L_p` and `M_p` of two integral lattices, with
`B(bᵢ, bᵢ) = uᵢ pᵏⁱ` and `B(cⱼ, cⱼ) = vⱼ pˡʲ` for units `uᵢ, vⱼ ∈ ℤ_pˣ`. Then `L_p` and `M_p` are
integrally isometric if and only if, at every scale `m ≥ 0` (including the unimodular scale
`m = 0`), they have the same number of summands of scale `p^m` and the products of the unit parts at
scale `p^m` agree modulo squares in `ℤ_pˣ`. -/
theorem localIntegralForm_equivalent_iff_forall_occCount_eq_and_isSquare
    {V : Type u} {W : Type v} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    {L : IntegralLattice V} {M : IntegralLattice W}
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {ι κ : Type*} [Fintype ι] [Fintype κ]
    {b : Basis ι ℤ_[p] (L.LocalCarrier p)} {c : Basis κ ℤ_[p] (M.LocalCarrier p)}
    {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {k : ι → ℕ} {l : κ → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hc : (M.localIntegralForm p).iIsOrtho c)
    (hcv : ∀ j, M.localIntegralForm p (c j) (c j) = v j * (p : ℤ_[p]) ^ l j) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      ∀ m : ℕ, occCount k m = occCount l m ∧
        IsSquare ((∏ i : {i // k i = m}, u i) * ∏ j : {j // l j = m}, v j) :=
  hb.equivalent_iff_forall_occCount_eq_and_isSquare hc (PadicInt.isUnit_two hp)
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    (PadicInt.not_isUnit_iff_dvd.mpr dvd_rfl) hbu hcv

end IntegralLattice

end TauCeti
