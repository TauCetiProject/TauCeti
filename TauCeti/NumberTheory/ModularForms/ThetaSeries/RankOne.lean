/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Rank-one lattice theta series

For any nonzero vector `v` in a real normed space `E`, the theta series of the rank-one lattice
`ℤ v` is Mathlib's `jacobiTheta` evaluated at `‖v‖² τ` (`ZLattice.thetaSeries_span_singleton`).
In particular, the theta series of `ℤ ∙ 1 ⊆ ℝ` is `jacobiTheta τ`, and the theta series of
`√2 ℤ` is `jacobiTheta (2 τ)`. The period-two expansion of `Θ_ℤ` has constant coefficient one,
coefficient two at each positive square, and zero elsewhere. The coefficient two counts the two
signs of a nonzero integer, as in Mathlib's `hasSum_nat_jacobiTheta`.

For the non-integral lattice `L = ½ ℤ`, the dual lattice `L^∨ = 2 ℤ` is strictly contained in `L`
(`ZLattice.dual_span_inv_two_lt`) and the discriminant group `L^∨ ⧸ (L ∩ L^∨)` is trivial
(`ZLattice.instSubsingletonDiscriminantGroupSpanInvTwo`). On the imaginary axis
`Θ_{2ℤ}(τ) < Θ_{½ℤ}(τ)` (`ZLattice.re_thetaSeries_span_two_lt_span_inv_two`), so
`Θ_{2ℤ}(i) ≠ Θ_{½ℤ}(i)` (`ZLattice.thetaSeries_span_two_I_ne_span_inv_two`) and the dual coset
decomposition `Θ_{L^∨} = ∑_{γ ∈ A_L} θ_γ` fails at `τ = i`
(`ZLattice.thetaSeries_dual_span_inv_two_I_ne_sum`).

The comparison reindexes by `LinearEquiv.toSpanNonzeroSingleton`; the analytic series and its
positive-square summation formula are Mathlib's `jacobiTheta` and `hasSum_nat_jacobiTheta`.
For the lattice theta-series convention see Serre, *A Course in Arithmetic*, Ch. VII §6,
and Ebeling, *Lattices and Codes*, Ch. 2.
-/

public section

open Complex Function Submodule
open UpperHalfPlane (qExpansion)
open scoped Real UpperHalfPlane Pointwise

namespace ZLattice

/-- The theta series of the rank-one lattice `ℤ v` (`v ≠ 0`) in a real normed space is Jacobi's
theta function at `‖v‖² τ`. -/
theorem thetaSeries_span_singleton {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : E} (hv : v ≠ 0) (τ : ℍ) :
    thetaSeries (span ℤ {v}) τ = jacobiTheta ((‖v‖ ^ 2 : ℝ) * (τ : ℂ)) := by
  have : Module.IsTorsionFree ℤ E := Module.IsTorsionFree.trans ℝ
  rw [thetaSeries_apply, jacobiTheta,
    ← (LinearEquiv.toSpanNonzeroSingleton ℤ E v hv).toEquiv.tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp only [LinearEquiv.coe_toEquiv, LinearEquiv.toSpanNonzeroSingleton_apply, norm_zsmul ℝ,
    Real.norm_eq_abs, mul_pow, sq_abs]
  congr 1
  push_cast
  ring

/-- The theta series of the integer lattice, with exponent `π i n² τ`, is Jacobi's theta
function. -/
theorem thetaSeries_span_one (τ : ℍ) :
    thetaSeries (span ℤ {1} : Submodule ℤ ℝ) τ = jacobiTheta τ := by
  simpa using thetaSeries_span_singleton (one_ne_zero (α := ℝ)) τ

/-- Scaling the integer lattice by `√2` gives Jacobi's theta function at `2τ`. -/
theorem thetaSeries_sqrt_two_smul_span_one (τ : ℍ) :
    thetaSeries (Real.sqrt 2 • (span ℤ {1} : Submodule ℤ ℝ)) τ = jacobiTheta (2 * (τ : ℂ)) := by
  have hspan : Real.sqrt 2 • (span ℤ {1} : Submodule ℤ ℝ) = span ℤ {Real.sqrt 2} := by
    simp [smul_span]
  rw [hspan, thetaSeries_span_singleton (Real.sqrt_ne_zero'.mpr two_pos)]
  simp

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

/-! ### Failure of dual coset decomposition for `½ ℤ` -/

/-- On the imaginary axis, `Θ_{2ℤ}(τ) < Θ_{½ℤ}(τ)` because `2 ℤ` is a proper sublattice of
`½ ℤ`. -/
theorem re_thetaSeries_span_two_lt_span_inv_two {τ : ℍ} (hτ : τ.re = 0) :
    (thetaSeries (span ℤ {(2 : ℝ)} : Submodule ℤ ℝ) τ).re <
      (thetaSeries (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) τ).re :=
  re_thetaSeries_lt_of_lt (dual_span_inv_two ▸ dual_span_inv_two_lt) hτ

/-- At `τ = i`, the theta series of `2 ℤ` and `½ ℤ` differ: `Θ_{2ℤ}(i) ≠ Θ_{½ℤ}(i)`. -/
theorem thetaSeries_span_two_I_ne_span_inv_two :
    thetaSeries (span ℤ {(2 : ℝ)} : Submodule ℤ ℝ) UpperHalfPlane.I ≠
      thetaSeries (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) UpperHalfPlane.I :=
  fun h ↦ (re_thetaSeries_span_two_lt_span_inv_two UpperHalfPlane.I_re).ne (congrArg re h)

/-- Because the discriminant group of `½ ℤ` is trivial, the sum of its coset theta series is simply
`Θ_{½ℤ}`. -/
theorem sum_thetaCosetClass_span_inv_two :
    ∑ γ : DiscriminantGroup (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ),
      thetaCosetClass (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) γ =
        thetaSeries (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) :=
  sum_thetaCosetClass_of_subsingleton _

/-- For the non-integral lattice `L = ½ ℤ`, `Θ_{L^∨}(i) ≠ ∑_{γ ∈ A_L} θ_γ(i)`: `L^∨ = 2 ℤ`, `A_L`
is trivial, and `Θ_{2ℤ}(i) ≠ Θ_{½ℤ}(i)`. This witnesses why `IsIntegral.thetaSeries_dual_eq_sum`
requires `IsIntegral L`. -/
theorem thetaSeries_dual_span_inv_two_I_ne_sum :
    thetaSeries (dual (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ)) UpperHalfPlane.I ≠
      ∑ γ : DiscriminantGroup (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ),
        thetaCosetClass (span ℤ {(2⁻¹ : ℝ)} : Submodule ℤ ℝ) γ UpperHalfPlane.I :=
  (thetaSeries_dual_apply_eq_sum_iff_isIntegral UpperHalfPlane.I_re).not.mpr
    not_isIntegral_span_inv_two

end ZLattice
