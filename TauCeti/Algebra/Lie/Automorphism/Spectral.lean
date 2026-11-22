/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis
import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Real powers and logarithms of positively diagonalizable Lie automorphisms

Let `P : L ≃ₗ⁅ℝ⁆ L` be a Lie algebra automorphism diagonalized by a basis `B` with strictly
positive eigenvalues `lam : ι → ℝ`. Scaling the `i`-th basis vector by `lam i ^ s` defines a
one-parameter family of Lie automorphisms `P ^ s` (`LieEquiv.rpowLieEquiv`), and scaling it by
`Real.log (lam i)` defines a Lie derivation `log P` (`LieEquiv.logLieDerivation`). The Leibniz
rule and bracket preservation follow directly from the multiplicative property of eigenvalues on
brackets `[B i, B j]` via bilinear basis extensionality (`LinearMap.ext_basis`). On any
`μ`-eigenvector of `s • log P`, the power `P ^ s` acts as `Real.exp μ`
(`LieEquiv.rpowLieEquiv_apply_of_log_eq_smul`).

## Main definitions

* `LieEquiv.rpowLieEquiv`: real power `P ^ s` of a positively diagonalizable Lie automorphism as
  a Lie algebra automorphism.
* `LieEquiv.logLieDerivation`: logarithmic derivation `log P` of a positively diagonalizable Lie
  automorphism.

## Main results

* `LieEquiv.diagEnd_rpow_comp`, `LieEquiv.diagEnd_rpow_map_lie`: composition law and bracket
  preservation for diagonal real powers.
* `LieEquiv.rpowLieEquiv_apply`, `LieEquiv.rpowLieEquiv_symm_apply`, `LieEquiv.rpowLieEquiv_one`,
  `LieEquiv.rpowLieEquiv_add`: evaluation and group-homomorphism properties of `s ↦ P ^ s`.
* `LieEquiv.diagEnd_log_leibniz`: the diagonal logarithm satisfies the Leibniz rule.
* `LieEquiv.rpowLieEquiv_apply_of_log_eq_smul`: `P ^ s` acts by `Real.exp μ` on any
  `μ`-eigenvector of `s • log P`.
-/

public section

open LieAlgebra Module

namespace LieEquiv

section Diagonal

variable {ι R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The bracket of two eigenvectors of a Lie automorphism is an eigenvector with the product
eigenvalue. -/
private theorem apply_lie_basis_of_apply_basis (B : Basis ι R L) {lam : ι → R} {P : L ≃ₗ⁅R⁆ L}
    (hB : ∀ i, P (B i) = lam i • B i) (i j : ι) :
    P ⁅B i, B j⁆ = (lam i * lam j) • ⁅B i, B j⁆ := by
  rw [P.map_lie, hB i, hB j, smul_lie, lie_smul, smul_smul]

end Diagonal

section Real

variable {ι L : Type*} [LieRing L] [LieAlgebra ℝ L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Composing diagonal real powers `lam ^ s` and `lam ^ t` yields `lam ^ (s + t)`. -/
theorem diagEnd_rpow_comp (B : Basis ι ℝ L) {lam : ι → ℝ}
    (hlam : ∀ i, 0 < lam i) (s t : ℝ) :
    (B.diagEnd (fun i ↦ lam i ^ s)).comp (B.diagEnd (fun i ↦ lam i ^ t)) =
      B.diagEnd (fun i ↦ lam i ^ (s + t)) := by
  rw [B.diagEnd_comp]
  congr 1
  ext i
  rw [← Real.rpow_add (hlam i)]

/-- Diagonal real powers of a positively diagonalizable Lie automorphism preserve the bracket. -/
theorem diagEnd_rpow_map_lie (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hlam : ∀ i, 0 < lam i)
    (hB : ∀ i, P (B i) = lam i • B i) (s : ℝ) (x y : L) :
    B.diagEnd (fun i ↦ lam i ^ s) ⁅x, y⁆ =
      ⁅B.diagEnd (fun i ↦ lam i ^ s) x, B.diagEnd (fun i ↦ lam i ^ s) y⁆ := by
  let ds := B.diagEnd (fun k ↦ lam k ^ s)
  let adL : L →ₗ[ℝ] L →ₗ[ℝ] L := (LieAlgebra.ad ℝ L : L →ₗ⁅ℝ⁆ Module.End ℝ L).toLinearMap
  have hbilin : adL.compr₂ ds = adL.compl₁₂ ds ds := by
    refine LinearMap.ext_basis B B fun i j ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LieHom.coe_toLinearMap, ad_apply,
      adL, ds]
    rw [B.diagEnd_comp_apply_of_eigenvector (f := (P : L →ₗ[ℝ] L)) hB (· ^ s)
        (apply_lie_basis_of_apply_basis B hB i j),
      B.diagEnd_apply_self, B.diagEnd_apply_self, smul_lie, lie_smul, smul_smul,
      Real.mul_rpow (hlam i).le (hlam j).le]
  simpa only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LieHom.coe_toLinearMap, ad_apply,
    adL, ds] using LinearMap.congr_fun₂ hbilin x y

/-- Real power `P ^ s` of a positively diagonalizable Lie automorphism as a Lie automorphism. -/
noncomputable def rpowLieEquiv (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hlam : ∀ i, 0 < lam i)
    (hB : ∀ i, P (B i) = lam i • B i) (s : ℝ) : L ≃ₗ⁅ℝ⁆ L where
  __ := B.diagEnd (fun i ↦ lam i ^ s)
  invFun := B.diagEnd (fun i ↦ lam i ^ (-s))
  left_inv y := by
    have h := LinearMap.congr_fun (diagEnd_rpow_comp B hlam (-s) s) y
    have hone : (fun i : ι ↦ lam i ^ (-s + s)) = 1 := by ext i; simp
    simpa only [LinearMap.toFun_eq_coe, LinearMap.comp_apply, hone, B.diagEnd_one,
      LinearMap.id_apply] using h
  right_inv y := by
    have h := LinearMap.congr_fun (diagEnd_rpow_comp B hlam s (-s)) y
    have hone : (fun i : ι ↦ lam i ^ (s + -s)) = 1 := by ext i; simp
    simpa only [LinearMap.toFun_eq_coe, LinearMap.comp_apply, hone, B.diagEnd_one,
      LinearMap.id_apply] using h
  map_lie' := diagEnd_rpow_map_lie B hlam hB s _ _

/-- Evaluating `rpowLieEquiv B hlam hB s` gives the diagonal power endomorphism. -/
theorem rpowLieEquiv_apply (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hlam : ∀ i, 0 < lam i)
    (hB : ∀ i, P (B i) = lam i • B i) (s : ℝ) (y : L) :
    rpowLieEquiv B hlam hB s y = B.diagEnd (fun i ↦ lam i ^ s) y := by
  rfl

/-- Evaluating the inverse of `rpowLieEquiv B hlam hB s` agrees with
`rpowLieEquiv B hlam hB (-s)`. -/
theorem rpowLieEquiv_symm_apply (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hlam : ∀ i, 0 < lam i)
    (hB : ∀ i, P (B i) = lam i • B i) (s : ℝ) (y : L) :
    (rpowLieEquiv B hlam hB s).symm y = rpowLieEquiv B hlam hB (-s) y := by
  rfl

/-- `P ^ 1` equals `P`. -/
theorem rpowLieEquiv_one (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hlam : ∀ i, 0 < lam i)
    (hB : ∀ i, P (B i) = lam i • B i) (y : L) :
    rpowLieEquiv B hlam hB 1 y = P y := by
  suffices h : B.diagEnd (fun i ↦ lam i ^ (1 : ℝ)) = (P : L →ₗ[ℝ] L) from congr($h y)
  exact B.ext fun i ↦ by simp [hB]

/-- `P ^ s (P ^ t y) = P ^ (s + t) y`. -/
theorem rpowLieEquiv_add (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hlam : ∀ i, 0 < lam i)
    (hB : ∀ i, P (B i) = lam i • B i) (s t : ℝ) (y : L) :
    rpowLieEquiv B hlam hB s (rpowLieEquiv B hlam hB t y) =
      rpowLieEquiv B hlam hB (s + t) y :=
  LinearMap.congr_fun (diagEnd_rpow_comp B hlam s t) y

/-- The diagonal logarithm of a positively diagonalizable Lie automorphism satisfies the Leibniz
rule. -/
theorem diagEnd_log_leibniz (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hlam : ∀ i, 0 < lam i)
    (hB : ∀ i, P (B i) = lam i • B i) (x y : L) :
    B.diagEnd (fun i ↦ Real.log (lam i)) ⁅x, y⁆ =
      ⁅x, B.diagEnd (fun i ↦ Real.log (lam i)) y⁆ -
        ⁅y, B.diagEnd (fun i ↦ Real.log (lam i)) x⁆ := by
  let D := B.diagEnd (fun k ↦ Real.log (lam k))
  let adL : L →ₗ[ℝ] L →ₗ[ℝ] L := (LieAlgebra.ad ℝ L : L →ₗ⁅ℝ⁆ Module.End ℝ L).toLinearMap
  have hbilin : adL.compr₂ D = adL.compl₁₂ LinearMap.id D + adL.compl₁₂ D LinearMap.id := by
    refine LinearMap.ext_basis B B fun i j ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.add_apply, LinearMap.compl₁₂_apply,
      LinearMap.id_apply, LieHom.coe_toLinearMap, ad_apply, adL, D]
    rw [B.diagEnd_comp_apply_of_eigenvector (f := (P : L →ₗ[ℝ] L)) hB Real.log
        (apply_lie_basis_of_apply_basis B hB i j),
      B.diagEnd_apply_self, B.diagEnd_apply_self,
      Real.log_mul (hlam i).ne' (hlam j).ne', add_smul, lie_smul, smul_lie, add_comm]
  have h := LinearMap.congr_fun₂ hbilin x y
  simp only [LinearMap.compr₂_apply, LinearMap.add_apply, LinearMap.compl₁₂_apply,
    LinearMap.id_apply, LieHom.coe_toLinearMap, ad_apply, adL, D] at h
  rw [h, ← lie_skew y (D x), sub_neg_eq_add]

/-- Logarithmic derivation `log P` of a positively diagonalizable Lie automorphism. -/
noncomputable def logLieDerivation (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hlam : ∀ i, 0 < lam i)
    (hB : ∀ i, P (B i) = lam i • B i) : LieDerivation ℝ L L where
  toLinearMap := B.diagEnd (fun i ↦ Real.log (lam i))
  leibniz' := diagEnd_log_leibniz B hlam hB

/-- Evaluating `logLieDerivation` gives the diagonal logarithm endomorphism. -/
theorem logLieDerivation_apply (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hlam : ∀ i, 0 < lam i)
    (hB : ∀ i, P (B i) = lam i • B i) (y : L) :
    logLieDerivation B hlam hB y = B.diagEnd (fun i ↦ Real.log (lam i)) y := by
  rfl

/-- On any `μ`-eigenvector of `s • log P`, the power `P ^ s` acts by `Real.exp μ`. -/
theorem rpowLieEquiv_apply_of_log_eq_smul (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hlam : ∀ i, 0 < lam i)
    (hB : ∀ i, P (B i) = lam i • B i) {s μ : ℝ} {y : L}
    (hy : s • logLieDerivation B hlam hB y = μ • y) :
    rpowLieEquiv B hlam hB s y = Real.exp μ • y := by
  have hlin : B.diagEnd (fun i ↦ s * Real.log (lam i)) y = μ • y := by
    have heq : B.diagEnd (fun i ↦ s * Real.log (lam i)) =
        s • B.diagEnd (fun i ↦ Real.log (lam i)) :=
      B.ext fun i ↦ by simp [mul_smul]
    simpa [heq, logLieDerivation_apply] using hy
  exact B.apply_eq_smul_of_apply_basis (B.diagEnd_apply_self _) (B.diagEnd_apply_self _)
    hlin fun i hi ↦ by rw [Real.rpow_def_of_pos (hlam i), mul_comm, hi]

end Real

end LieEquiv
