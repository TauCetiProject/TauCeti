/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.LinearAlgebra.Matrix.InvariantFactor
import TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Basic

/-!
# `p`-adic Smith normal form over `ℤ_p`

Every nonsingular matrix `A ∈ M_n(ℤ_p)` (`det A ≠ 0`) is `GL_n(ℤ_p)`-equivalent to a diagonal
matrix `diag(p ^ e₁, …, p ^ eₙ)` for a uniquely determined monotone exponent tuple
`e : Fin n → ℕ`.

## Main statements

* `Matrix.exists_padic_smith_normal_form`: existence of monotone `p`-power diagonalization in
  `M_n(ℤ_p)` under `GL_n(ℤ_p)` multiplication on both sides.
* `Matrix.padic_smith_normal_form_unique`: uniqueness of the monotone `p`-power exponent tuple via
  leading-minor divisibility.
-/

public section

namespace Matrix

variable (n p : ℕ) [Fact p.Prime]

/-- **`p`-adic Smith normal form (existence)**: every matrix `A ∈ M_n(ℤ_p)` with `det A ≠ 0` is
`GL_n(ℤ_p)`-equivalent to `diag(p ^ e₁, …, p ^ eₙ)` for a monotone tuple `e : Fin n → ℕ`. -/
theorem exists_padic_smith_normal_form (A : Matrix (Fin n) (Fin n) ℤ_[p]) (hA : A.det ≠ 0) :
    ∃ (U₁ U₂ : GL (Fin n) ℤ_[p]) (e : Fin n → ℕ),
      Monotone e ∧
        (↑U₁ : Matrix (Fin n) (Fin n) ℤ_[p]) * A * (↑U₂ : Matrix (Fin n) (Fin n) ℤ_[p]) =
          Matrix.diagonal fun i ↦ (p : ℤ_[p]) ^ e i := by
  obtain ⟨L, Q, s, hL, hQ, hs_dvd, hLAQ⟩ :=
    Matrix.exists_smith_normal_form_of_isDiscreteValuationRing A
  have hs_ne : ∀ i, s i ≠ 0 := by
    intro i hi
    have hdet : (Matrix.diagonal s).det = 0 := by
      rw [Matrix.det_diagonal]; exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [← hLAQ, Matrix.det_mul, Matrix.det_mul] at hdet
    exact mul_ne_zero (mul_ne_zero hL.ne_zero hA) hQ.ne_zero hdet
  let u : Fin n → ℤ_[p]ˣ := fun i ↦ PadicInt.unitCoeff (hs_ne i)
  let e : Fin n → ℕ := fun i ↦ (s i).valuation
  have he_mono : Monotone e := by
    intro i j hij
    obtain ⟨c, hc⟩ := hs_dvd hij
    rw [← pow_dvd_pow_iff (PadicInt.irreducible_p (p := p)).ne_zero
      (PadicInt.irreducible_p (p := p)).not_isUnit]
    refine ⟨↑(u i) * c * ↑((u j)⁻¹), ?_⟩
    calc (p : ℤ_[p]) ^ e j
        = ↑((u j)⁻¹) * (↑(u j) * (p : ℤ_[p]) ^ e j) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ↑((u j)⁻¹) * s j := by rw [← PadicInt.unitCoeff_spec (hs_ne j)]
      _ = ↑((u j)⁻¹) * (↑(u i) * (p : ℤ_[p]) ^ e i * c) := by
          rw [hc, PadicInt.unitCoeff_spec (hs_ne i)]
      _ = (p : ℤ_[p]) ^ e i * (↑(u i) * c * ↑((u j)⁻¹)) := by ring
  let UL : GL (Fin n) ℤ_[p] := Matrix.GeneralLinearGroup.mk'' L hL
  let UD : GL (Fin n) ℤ_[p] := TauCeti.diagGL fun i ↦ (u i)⁻¹
  let UQ : GL (Fin n) ℤ_[p] := Matrix.GeneralLinearGroup.mk'' Q hQ * UD
  refine ⟨UL, UQ, e, he_mono, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_mk'', Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.val_mk'', ← Matrix.mul_assoc, hLAQ, TauCeti.diagGL_coe,
    Matrix.diagonal_mul_diagonal]
  congr 1; funext i
  rw [PadicInt.unitCoeff_spec (hs_ne i), mul_right_comm, Units.mul_inv, one_mul]

/-- **`p`-adic Smith normal form (uniqueness)**: the monotone `p`-power exponent tuple of a matrix
in `M_n(ℤ_p)` is uniquely determined by its `GL_n(ℤ_p)` double coset. -/
theorem padic_smith_normal_form_unique {e₁ e₂ : Fin n → ℕ} (he₁ : Monotone e₁) (he₂ : Monotone e₂)
    (U₁ U₂ : GL (Fin n) ℤ_[p])
    (h : (↑U₁ : Matrix (Fin n) (Fin n) ℤ_[p]) * (Matrix.diagonal fun i ↦ (p : ℤ_[p]) ^ e₁ i) *
        (↑U₂ : Matrix (Fin n) (Fin n) ℤ_[p]) = Matrix.diagonal fun i ↦ (p : ℤ_[p]) ^ e₂ i) :
    e₁ = e₂ := by
  let d₁ : Fin n → ℤ_[p] := fun i ↦ (p : ℤ_[p]) ^ e₁ i
  let d₂ : Fin n → ℤ_[p] := fun i ↦ (p : ℤ_[p]) ^ e₂ i
  have hc₁ : ∀ ⦃i j : Fin n⦄, i ≤ j → d₁ i ∣ d₁ j := fun _ _ hij ↦ pow_dvd_pow _ (he₁ hij)
  have hc₂ : ∀ ⦃i j : Fin n⦄, i ≤ j → d₂ i ∣ d₂ j := fun _ _ hij ↦ pow_dvd_pow _ (he₂ hij)
  have hU₁ : IsUnit (↑U₁ : Matrix (Fin n) (Fin n) ℤ_[p]).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp U₁.isUnit
  have hU₂ : IsUnit (↑U₂ : Matrix (Fin n) (Fin n) ℤ_[p]).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp U₂.isUnit
  have h1 : IsUnit (1 : Matrix (Fin n) (Fin n) ℤ_[p]).det := by
    rw [Matrix.det_one]; exact isUnit_one
  have hid : (1 : Matrix (Fin n) (Fin n) ℤ_[p]) * Matrix.diagonal d₁ * 1 = Matrix.diagonal d₁ := by
    rw [Matrix.one_mul, Matrix.mul_one]
  have hp_dvd := fun {a b : ℕ} ↦ pow_dvd_pow_iff (n := a) (m := b)
    (PadicInt.irreducible_p (p := p)).ne_zero (PadicInt.irreducible_p (p := p)).not_isUnit
  have hsum : ∀ (k : ℕ) (hk : k ≤ n),
      ∑ j : Fin k, e₁ (Fin.castLE hk j) = ∑ j : Fin k, e₂ (Fin.castLE hk j) := by
    intro k hk
    have hdvd₁ : (∏ j : Fin k, d₁ (Fin.castLE hk j)) ∣ ∏ j : Fin k, d₂ (Fin.castLE hk j) :=
      Matrix.dvd_prod_of_mul_mul_eq_diagonal h hk fun f g ↦
        Matrix.prod_dvd_det_submatrix_of_mul_mul_eq_diagonal h1 h1 hc₁ hid hk f g
    have hdvd₂ : (∏ j : Fin k, d₂ (Fin.castLE hk j)) ∣ ∏ j : Fin k, d₁ (Fin.castLE hk j) := by
      rw [← Matrix.det_submatrix_diagonal d₁ (Fin.castLE_injective hk)]
      exact Matrix.prod_dvd_det_submatrix_of_mul_mul_eq_diagonal hU₁ hU₂ hc₂ h hk _ _
    simp only [d₁, d₂, Finset.prod_pow_eq_pow_sum] at hdvd₁ hdvd₂
    exact le_antisymm (hp_dvd.mp hdvd₁) (hp_dvd.mp hdvd₂)
  refine TauCeti.eq_of_forall_prefixSum_eq fun k ↦ ?_
  rw [← TauCeti.prefixSum_min k e₁, ← TauCeti.prefixSum_min k e₂,
    TauCeti.prefixSum_eq_sum_castLE (min_le_right k n),
    TauCeti.prefixSum_eq_sum_castLE (min_le_right k n)]
  exact hsum (min k n) (min_le_right k n)

end Matrix
