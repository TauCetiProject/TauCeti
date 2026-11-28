/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Sym.Basic
public import TauCeti.LinearAlgebra.End.JordanChain.Shift
public import TauCeti.LinearAlgebra.SymmetricPower.Derivation

/-!
# The monomial basis of `Sym^m (R²)`

Write `e₀, e₁` for the standard basis of `R²` over a commutative semiring `R`. The monomials
`e₀ ^ (m - j) e₁ ^ j` (`TauCeti.symFinTwoMonomial`) for `j = 0, …, m` are the basis of
`Sym^m (R²)` induced by the standard basis (`TauCeti.symFinTwoMonomial_eq_symmetricPower`), so
they are nonzero over a nontrivial semiring (`TauCeti.symFinTwoMonomial_ne_zero`), and their
images in the symmetric algebra are the products `x ^ (m - j) * y ^ j`
(`TauCeti.toSymmetricAlgebra_symFinTwoMonomial`).

Over a commutative ring, the differential of the shift `e₀ ↦ e₁ ↦ 0` (`TauCeti.finShift R 2`)
sends the `j`-th monomial to `(m - j)` times the `(j + 1)`-st
(`TauCeti.differential_finShift_symFinTwoMonomial`), by the Leibniz rule in the symmetric algebra,
and kills the top monomial `e₁ ^ m` (`TauCeti.differential_finShift_symFinTwoMonomial_self`).

## Main definitions

* `TauCeti.symFinTwoMonomial`: the monomial `e₀ ^ (m - j) e₁ ^ j` in `Sym^m (R²)`.
-/

public section

noncomputable section

namespace TauCeti

open Module SymmetricPower Finset TensorProduct

/-- The factor pattern of the monomial `e₀ ^ (m - j) e₁ ^ j`: the `i`-th factor is `e₀` for
`i < m - j` and `e₁` otherwise. -/
private def symFinTwoIndex (m j : ℕ) (i : Fin m) : Fin 2 :=
  if (i : ℕ) < m - j then 0 else 1

section CommSemiring

variable {R : Type*} [CommSemiring R]

variable (R) in
/-- The monomial `e₀ ^ (m - j) e₁ ^ j` in the symmetric power `Sym^m (R²)`. -/
def symFinTwoMonomial (m j : ℕ) : Sym[R]^m (Fin 2 → R) :=
  ⨂ₛ[R] i, (Pi.single (symFinTwoIndex m j i) 1 : Fin 2 → R)

/-- The monomial `e₀ ^ (m - j) e₁ ^ j` is the vector of the basis of `Sym^m (R²)` induced by the
standard basis indexed by the unordered tuple with `m - j` entries `0`. For `j ≥ m` it is the top
monomial `e₁ ^ m`. -/
theorem symFinTwoMonomial_eq_symmetricPower (m j : ℕ) :
    symFinTwoMonomial R m j = (Pi.basisFun R (Fin 2)).symmetricPower m
      ((symFinTwoEquiv m).symm ⟨m - j, by omega⟩) := by
  rw [Basis.symmetricPower_apply, symFinTwoMonomial]
  have : Sym.ofFn (symFinTwoIndex m j) = (symFinTwoEquiv m).symm ⟨m - j, by omega⟩ := by
    rw [Equiv.eq_symm_apply, Fin.ext_iff, coe_symFinTwoEquiv_apply, Sym.count_coe_ofFn]
    simp only [symFinTwoIndex, ite_eq_left_iff, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
      imp_false, not_not]
    rw [Fin.card_filter_val_lt, min_eq_right (Nat.sub_le m j)]
  rw [← this, tprodOfSym_ofFn]
  simp

/-- The monomial `e₀ ^ (m - j) e₁ ^ j` is nonzero over a nontrivial semiring: it is a basis
vector. -/
theorem symFinTwoMonomial_ne_zero [Nontrivial R] (m j : ℕ) : symFinTwoMonomial R m j ≠ 0 := by
  rw [symFinTwoMonomial_eq_symmetricPower]
  exact Basis.ne_zero _ _

/-- The image of the monomial `e₀ ^ (m - j) e₁ ^ j` in the symmetric algebra is the product
`x ^ (m - j) * y ^ j` of the images of `e₀` and `e₁`. -/
theorem toSymmetricAlgebra_symFinTwoMonomial {m j : ℕ} (hj : j ≤ m) :
    toSymmetricAlgebra R (Fin 2 → R) m (symFinTwoMonomial R m j) =
      SymmetricAlgebra.ι R (Fin 2 → R) (Pi.single 0 1) ^ (m - j) *
        SymmetricAlgebra.ι R (Fin 2 → R) (Pi.single 1 1) ^ j := by
  rw [symFinTwoMonomial, toSymmetricAlgebra_tprod]
  simp only [symFinTwoIndex, apply_ite (fun k : Fin 2 ↦ SymmetricAlgebra.ι R (Fin 2 → R)
    (Pi.single k 1)), prod_ite, prod_const, Fin.card_filter_val_lt, filter_not,
    card_sdiff_of_subset (filter_subset _ _), card_univ, Fintype.card_fin]
  congr 2 <;> omega

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- **The Leibniz rule on the monomials**: the differential of the shift `e₀ ↦ e₁ ↦ 0` sends
`e₀ ^ (m - j) e₁ ^ j` to `(m - j) e₀ ^ (m - j - 1) e₁ ^ (j + 1)`. -/
theorem differential_finShift_symFinTwoMonomial {m j : ℕ} (hj : j < m) :
    differential R (Fin 2 → R) m (finShift R 2) (symFinTwoMonomial R m j) =
      ((m - j : ℕ) : R) • symFinTwoMonomial R m (j + 1) := by
  apply toSymmetricAlgebra_injective m
  obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
  rw [toSymmetricAlgebra_differential, map_smul, toSymmetricAlgebra_symFinTwoMonomial hj.le,
    toSymmetricAlgebra_symFinTwoMonomial hj, hk, show m - (j + 1) = k by omega]
  simp [Derivation.leibniz, Derivation.leibniz_pow, finShift_single_eq_dite,
    Algebra.smul_def]
  ring

/-- The differential of the shift `e₀ ↦ e₁ ↦ 0` kills the top monomial `e₁ ^ m`. -/
@[simp]
theorem differential_finShift_symFinTwoMonomial_self (m : ℕ) :
    differential R (Fin 2 → R) m (finShift R 2) (symFinTwoMonomial R m m) = 0 := by
  apply toSymmetricAlgebra_injective m
  simp [toSymmetricAlgebra_differential, toSymmetricAlgebra_symFinTwoMonomial le_rfl,
    Derivation.leibniz_pow, finShift_single_eq_dite]

end CommRing

end TauCeti
