/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Inversion
import TauCeti.Analysis.Normed.Ring.InfiniteSum

/-!
# Theta series of cubic lattices

Let `b` be an orthonormal basis of a real inner product space `E` of dimension `n`, and let
`ℤ b = span ℤ (range b)` be the cubic lattice it spans, a copy of `ℤⁿ`. A vector
`v = ∑ i, m i • b i` of `ℤ b` has `‖v‖² = ∑ i, (m i)²`, so the terms of its theta series factor
over the coordinates, and
```text
Θ_{ℤ b}(τ) = jacobiTheta(τ) ^ n,
```
the `n`-th power of Jacobi's theta function `θ(τ) = ∑_{m ∈ ℤ} exp (π i m² τ)`
(`ZLattice.thetaSeries_span_orthonormalBasis`). For `n = 1` this is
`ZLattice.thetaSeries_span_one`.

The cubic lattice is unimodular with covolume one, so in even dimension `n = 2k` the inversion
law of theta series reads `Θ_{ℤ b}(-1/τ) = (-i τ)^k Θ_{ℤ b}(τ)`
(`ZLattice.thetaSeries_span_orthonormalBasis_S_smul`). Mathlib's inversion law of Jacobi's theta
function, `jacobiTheta_S_smul`, is a half-integral weight statement carrying the principal branch
of `(-i τ)^{1/2}`; its square is integral weight. In rank two the two laws compare directly:
`jacobiTheta(-1/τ)² = -i τ jacobiTheta(τ)²` follows from the lattice inversion law, which is
proved by Poisson summation over the lattice (`jacobiTheta_S_smul_sq`). This
checks the exponent `π i ‖v‖² τ` and the constant `(covol L)⁻¹ (-i)^k τ^k` of the lattice
inversion law against the classical rank-one formula.

## Main statements

* `ZLattice.thetaSeries_span_orthonormalBasis`: `Θ_{ℤ b} = jacobiTheta ^ n`.
* `ZLattice.thetaSeries_span_orthonormalBasis_S_smul`: in dimension `2k`,
  `Θ_{ℤ b}(-1/τ) = (-i τ)^k Θ_{ℤ b}(τ)`.
* `jacobiTheta_S_smul_sq`: `jacobiTheta(-1/τ)² = -i τ jacobiTheta(τ)²`, from the
  lattice inversion law in rank two.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, Ch. 2.
-/

public section

open Complex Module Submodule
open scoped Real RealInnerProductSpace UpperHalfPlane

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι]
  (b : OrthonormalBasis ι ℝ E)

/-- **The theta series of a cubic lattice is a power of Jacobi's theta function**: for an
orthonormal basis `b` indexed by `ι`, `Θ_{ℤ b}(τ) = jacobiTheta(τ) ^ |ι|`. -/
theorem thetaSeries_span_orthonormalBasis (τ : ℍ) :
    thetaSeries (span ℤ (Set.range b)) τ = jacobiTheta τ ^ Fintype.card ι := by
  have hs : Summable fun m : ℤ ↦ ‖cexp (π * I * (m : ℂ) ^ 2 * τ)‖ := by
    simpa [jacobiTheta₂_term] using
      summable_norm_iff.mpr ((summable_jacobiTheta₂_term_iff 0 τ).mpr τ.im_pos)
  have hpow : jacobiTheta τ ^ Fintype.card ι = ∏ _ : ι, jacobiTheta τ := by simp
  rw [hpow, jacobiTheta, TauCeti.prod_tsum_of_summable_norm fun _ ↦ hs, thetaSeries_apply,
    ← b.coe_toBasis, ← (b.toBasis.restrictScalars ℤ).equivFun.symm.toEquiv.tsum_eq]
  refine tsum_congr fun m ↦ ?_
  -- The lattice vector with coordinates `m` is `∑ i, (m i : ℝ) • b i`, of squared norm
  -- `∑ i, (m i)²` by orthonormality.
  have hv : ((b.toBasis.restrictScalars ℤ).equivFun.symm m : E) = ∑ i, (m i : ℝ) • b i := by
    rw [Basis.equivFun_symm_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    -- The `ℤ`-action on the span is the one of `Basis.restrictScalars`, so `coe_smul` only
    -- matches up to instances.
    erw [Submodule.coe_smul]
    rw [Basis.restrictScalars_apply, b.coe_toBasis, Int.cast_smul_eq_zsmul]
  have hn : ‖((b.toBasis.restrictScalars ℤ).equivFun.symm m : E)‖ ^ 2 = ∑ i, (m i : ℝ) ^ 2 := by
    rw [hv]
    simpa using b.orthonormal.orthogonalFamily.norm_sum (fun i ↦ (m i : ℝ)) Finset.univ
  rw [LinearEquiv.coe_toEquiv, hn, ← Complex.exp_sum]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]

variable {k : ℕ}

/-- **The inversion law of a cubic lattice**: if `b` is an orthonormal basis of a space of
dimension `2k`, then `Θ_{ℤ b}(-1/τ) = (-i τ)^k Θ_{ℤ b}(τ)`. -/
theorem thetaSeries_span_orthonormalBasis_S_smul (hk : Fintype.card ι = 2 * k) (τ : ℍ) :
    thetaSeries (span ℤ (Set.range b)) (ModularGroup.S • τ) =
      (-I * τ) ^ k * thetaSeries (span ℤ (Set.range b)) τ := by
  have := b.toBasis.finiteDimensional_of_finite
  borelize E
  rw [← b.coe_toBasis]
  have hU := isUnimodular_span_orthonormalBasis b
  rw [← b.coe_toBasis] at hU
  rw [thetaSeries_S_smul _ ((finrank_eq_card_basis b.toBasis).trans hk), hU.covolume_eq_one,
    hU.dual_eq, ofReal_one, inv_one, one_mul, mul_pow]

/-- **The square of the inversion law of Jacobi's theta function**,
`jacobiTheta(-1/τ)² = -i τ jacobiTheta(τ)²`. This is the square of Mathlib's half-integral weight
law `jacobiTheta_S_smul`. -/
theorem _root_.jacobiTheta_S_smul_sq (τ : ℍ) :
    jacobiTheta (ModularGroup.S • τ : ℍ) ^ 2 = -I * τ * jacobiTheta τ ^ 2 := by
  have h := thetaSeries_span_orthonormalBasis_S_smul (EuclideanSpace.basisFun (Fin 2) ℝ)
    (k := 1) (by simp) τ
  simpa only [thetaSeries_span_orthonormalBasis, Fintype.card_fin, pow_one] using h

end ZLattice
