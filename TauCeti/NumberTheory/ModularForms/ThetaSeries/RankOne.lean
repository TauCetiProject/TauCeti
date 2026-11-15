/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.DiscriminantGroup
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Functoriality
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Cusp

/-!
# Rank-one lattice theta series and the non-integral lattice `½ ℤ`

The theta series of `ℤ ∙ 1 ⊆ ℝ` is Mathlib's `jacobiTheta`, with exponent `π i n² τ`.
More generally, for `c ≠ 0` the theta series of `c ℤ ⊆ ℝ` is `jacobiTheta (c² τ)`
(`ZLattice.thetaSeries_span_singleton`), so `Θ_{√2 ℤ}(τ) = jacobiTheta (2 τ)`,
`Θ_{2 ℤ}(τ) = jacobiTheta (4 τ)`, and `Θ_{½ ℤ}(τ) = jacobiTheta (τ / 4)`.
The period-two expansion of `Θ_ℤ` has constant coefficient one, coefficient two at each positive
square, and zero elsewhere; the coefficient two counts the two signs of a nonzero integer, as in
Mathlib's `hasSum_nat_jacobiTheta`.

For the non-integral lattice `L = ½ ℤ ⊆ ℝ`, the dual lattice `L^∨ = 2 ℤ` is strictly contained in
`L` (`ZLattice.dual_span_inv_two`, `ZLattice.span_two_lt_span_inv_two`), so the discriminant group
`A_L = L^∨ ⧸ (L ∩ L^∨)` is trivial (`ZLattice.instUniqueDiscriminantGroupSpanInvTwo`), even though
`level (½ ℤ) = 1` (`ZLattice.level_span_inv_two`). On the imaginary axis
`Θ_{2 ℤ}(τ).re < Θ_{½ ℤ}(τ).re` (`ZLattice.re_thetaSeries_span_two_lt_span_inv_two`); in particular
`Θ_{2 ℤ}(i) ≠ Θ_{½ ℤ}(i)` (`ZLattice.thetaSeries_span_two_ne_thetaSeries_span_inv_two_I`), so the
dual coset decomposition `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ` fails at `τ = i` for `L = ½ ℤ`
(`ZLattice.thetaSeries_dual_span_inv_two_ne_sum_I`), showing that `ZLattice.IsIntegral` is
essential in `ZLattice.IsIntegral.thetaSeries_dual_eq_sum`.

The comparison reindexes by `LinearEquiv.toSpanNonzeroSingleton`; the analytic series and its
positive-square summation formula are Mathlib's `jacobiTheta` and `hasSum_nat_jacobiTheta`.

## Main statements

* `ZLattice.thetaSeries_span_one`, `ZLattice.thetaSeries_span_singleton`,
  `ZLattice.thetaSeries_sqrt_two_smul_span_one`, `ZLattice.thetaSeries_span_two`,
  `ZLattice.thetaSeries_span_inv_two`: comparison of `Θ_{c ℤ}` with `jacobiTheta (c² τ)`.
* `ZLattice.qExpansion_two_thetaSeries_span_one_coeff`,
  `ZLattice.hasSum_thetaSeries_span_one_qParam`: the period-two `q`-expansion of `Θ_ℤ`.
* `ZLattice.re_thetaSeries_span_two_lt_span_inv_two`,
  `ZLattice.thetaSeries_span_two_ne_thetaSeries_span_inv_two_I`,
  `ZLattice.thetaSeries_dual_span_inv_two_ne_sum_I`: strict inequality `Θ_{2ℤ} < Θ_{½ℤ}` on the
  imaginary axis and failure of `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ` at `τ = i` for `L = ½ ℤ`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, Ch. 2.
-/

public section

open Complex Function Submodule
open UpperHalfPlane (qExpansion)
open scoped Real UpperHalfPlane Pointwise

namespace ZLattice

/-- The theta series of the integer lattice, with exponent `π i n² τ`, is Jacobi's theta
function. -/
theorem thetaSeries_span_one (τ : ℍ) :
    thetaSeries (span ℤ {1} : Submodule ℤ ℝ) τ = jacobiTheta τ := by
  rw [thetaSeries_apply, jacobiTheta,
    ← (LinearEquiv.toSpanNonzeroSingleton ℤ ℝ 1 one_ne_zero).toEquiv.tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp [Real.norm_eq_abs, sq_abs]

/-- For a nonzero real number `c`, the theta series of `c ℤ ⊆ ℝ` is Jacobi's theta function at
`c² τ`. -/
theorem thetaSeries_span_singleton {c : ℝ} (hc : c ≠ 0) (τ : ℍ) :
    thetaSeries (span ℤ {c} : Submodule ℤ ℝ) τ = jacobiTheta ((c ^ 2 : ℝ) * (τ : ℂ)) := by
  have hsmul : c • (span ℤ {(1 : ℝ)} : Submodule ℤ ℝ) = span ℤ {c} := by
    rw [Submodule.smul_span, Set.smul_set_singleton, smul_eq_mul, mul_one]
  rw [← hsmul, thetaSeries_smul _ hc, thetaSeries_span_one]
  congr 1

/-- Scaling the integer lattice by `√2` gives Jacobi's theta function at `2τ`. -/
theorem thetaSeries_sqrt_two_smul_span_one (τ : ℍ) :
    thetaSeries (Real.sqrt 2 • (span ℤ {1} : Submodule ℤ ℝ)) τ = jacobiTheta (2 * (τ : ℂ)) := by
  rw [thetaSeries_smul _ (Real.sqrt_ne_zero'.mpr two_pos), thetaSeries_span_one]
  congr 1
  simp [Complex.real_smul]

/-- The theta series of `2 ℤ ⊆ ℝ` is Jacobi's theta function at `4τ`. -/
theorem thetaSeries_span_two (τ : ℍ) :
    thetaSeries (span ℤ {(2 : ℝ)} : Submodule ℤ ℝ) τ = jacobiTheta (4 * (τ : ℂ)) := by
  rw [thetaSeries_span_singleton two_ne_zero]
  norm_num

/-- The theta series of `½ ℤ ⊆ ℝ` is Jacobi's theta function at `τ / 4`. -/
theorem thetaSeries_span_inv_two (τ : ℍ) :
    thetaSeries (span ℤ {(2 : ℝ)⁻¹} : Submodule ℤ ℝ) τ = jacobiTheta ((τ : ℂ) / 4) := by
  rw [thetaSeries_span_singleton (inv_ne_zero two_ne_zero)]
  congr 1
  push_cast
  ring

/-- The period-two coefficients of the rank-one lattice theta series, explicitly supported at
the squares. -/
theorem qExpansion_two_thetaSeries_span_one_coeff (m : ℕ) :
    (qExpansion 2 (thetaSeries (span ℤ {1} : Submodule ℤ ℝ))).coeff m =
      if m = 0 then 1 else if IsSquare m then 2 else 0 := by
  rw [isUnimodular_span_one.isIntegral.qExpansion_two_thetaSeries_coeff,
    representationNumber_span_one]
  split_ifs <;> norm_num

/-- The lattice theta series has the period-two square-supported power series, so its terms
have exactly the same multiplicities as Jacobi's positive-square expansion. -/
theorem hasSum_thetaSeries_span_one_qParam (τ : ℍ) :
    HasSum (fun m : ℕ ↦
      (if m = 0 then 1 else if IsSquare m then 2 else 0 : ℂ) * Periodic.qParam 2 τ ^ m)
      (thetaSeries (span ℤ {1} : Submodule ℤ ℝ) τ) := by
  classical
  simpa only [representationNumber_span_one, smul_eq_mul, Nat.cast_ite, Nat.cast_one,
    Nat.cast_ofNat, Nat.cast_zero] using
    isUnimodular_span_one.isIntegral.hasSum_thetaSeries_qParam_two τ

/-! ### The non-integral lattice `½ ℤ` -/

/-- On the imaginary axis, `Θ_{2ℤ}(τ).re < Θ_{½ℤ}(τ).re`: `2ℤ` is a proper sublattice of `½ ℤ`. -/
theorem re_thetaSeries_span_two_lt_span_inv_two {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries (span ℤ {(2 : ℝ)} : Submodule ℤ ℝ) τ).re <
      (thetaSeries (span ℤ {(2 : ℝ)⁻¹} : Submodule ℤ ℝ) τ).re :=
  re_thetaSeries_lt_of_lt span_two_lt_span_inv_two hτ

/-- At `τ = i`, `Θ_{2ℤ}(i) ≠ Θ_{½ℤ}(i)`. -/
theorem thetaSeries_span_two_ne_thetaSeries_span_inv_two_I :
    thetaSeries (span ℤ {(2 : ℝ)} : Submodule ℤ ℝ) UpperHalfPlane.I ≠
      thetaSeries (span ℤ {(2 : ℝ)⁻¹} : Submodule ℤ ℝ) UpperHalfPlane.I :=
  thetaSeries_ne_of_lt_of_re_eq_zero span_two_lt_span_inv_two UpperHalfPlane.I_re

/-- For the non-integral lattice `L = ½ ℤ ⊆ ℝ` (`L^∨ = 2ℤ ⊂ L`), the dual theta-series
decomposition `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ` fails at `τ = i`: the discriminant group `A_L` is
trivial, so the right-hand side is `Θ_{½ℤ}(i)` while the left-hand side is `Θ_{2ℤ}(i)`. -/
theorem thetaSeries_dual_span_inv_two_ne_sum_I :
    thetaSeries (dual (span ℤ {(2 : ℝ)⁻¹} : Submodule ℤ ℝ)) UpperHalfPlane.I ≠
      ∑ γ : DiscriminantGroup (span ℤ {(2 : ℝ)⁻¹} : Submodule ℤ ℝ),
        thetaCosetClass (span ℤ {(2 : ℝ)⁻¹} : Submodule ℤ ℝ) γ UpperHalfPlane.I :=
  thetaSeries_dual_ne_sum_of_dual_lt (dual_span_inv_two.trans_lt span_two_lt_span_inv_two)
    UpperHalfPlane.I_re

end ZLattice
