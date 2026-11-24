/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis
import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Real powers and logarithms of diagonalizable Lie automorphisms

Let `P : L ≃ₗ⁅ℝ⁆ L` be a Lie algebra automorphism diagonalized by a finite basis `B` with
eigenvalues `lam : ι → ℝ` (automatically nonzero since `P` is injective,
`LieEquiv.eigenvalue_ne_zero_of_apply_basis`). Scaling the `i`-th basis vector by
`Real.log (lam i)` defines a Lie derivation `log P` (`LieEquiv.logLieDerivation`). When all
eigenvalues are strictly positive, scaling the `i`-th basis vector by `lam i ^ s` defines a
one-parameter family of Lie automorphisms `P ^ s` (`LieEquiv.rpowLieEquiv`). The Leibniz rule and
bracket preservation follow directly from the multiplicative property of eigenvalues on brackets
`[B i, B j]` via bilinear basis extensionality (`LinearMap.ext_basis`). On any `μ`-eigenvector of
`s • log P`, the power `P ^ s` acts as `Real.exp μ` (`LieEquiv.rpowLieEquiv_apply_of_log_eq_smul`).

## Main definitions

* `LieEquiv.rpowLieEquiv`: real power `P ^ s` of a positively diagonalizable Lie automorphism as
  a Lie algebra automorphism.
* `LieEquiv.logLieDerivation`: logarithmic derivation `log P` of a real diagonalizable Lie
  automorphism.

## Main results

* `LieEquiv.eigenvalue_ne_zero_of_apply_basis`: eigenvalues of a Lie algebra automorphism on a
  basis vector are nonzero.
* `Matrix.toLin_diagonal_rpow_comp`: composition law for diagonal real powers on a real module.
* `LieEquiv.toLin_diagonal_rpow_map_lie`: bracket preservation for diagonal real powers.
* `LieEquiv.rpowLieEquiv_apply`, `LieEquiv.rpowLieEquiv_symm_apply`, `LieEquiv.rpowLieEquiv_one`,
  `LieEquiv.rpowLieEquiv_add`: evaluation and group-homomorphism properties of `s ↦ P ^ s`.
* `LieEquiv.toLin_diagonal_log_leibniz`: the diagonal logarithm satisfies the Leibniz rule.
* `LieEquiv.rpowLieEquiv_apply_of_log_eq_smul`: `P ^ s` acts by `Real.exp μ` on any
  `μ`-eigenvector of `s • log P`.
-/

public section

open LieAlgebra Module

section DiagonalRpow

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid V] [Module ℝ V]

/-- Composing diagonal real powers `lam ^ s` and `lam ^ t` yields `lam ^ (s + t)`. -/
theorem _root_.Matrix.toLin_diagonal_rpow_comp (B : Basis ι ℝ V) {lam : ι → ℝ}
    (hlam : ∀ i, 0 < lam i) (s t : ℝ) :
    (Matrix.toLin B B (Matrix.diagonal (fun i ↦ lam i ^ s))).comp
      (Matrix.toLin B B (Matrix.diagonal (fun i ↦ lam i ^ t))) =
      Matrix.toLin B B (Matrix.diagonal (fun i ↦ lam i ^ (s + t))) := by
  rw [← Matrix.toLin_mul B B B, Matrix.diagonal_mul_diagonal]
  congr 2
  ext i
  exact (Real.rpow_add (hlam i) s t).symm

end DiagonalRpow

namespace LieEquiv

section Diagonal

variable {ι R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- An eigenvalue of a Lie algebra automorphism on a basis vector is nonzero. -/
theorem eigenvalue_ne_zero_of_apply_basis [Nontrivial R] (B : Basis ι R L)
    {P : L ≃ₗ⁅R⁆ L} {c : R} {i : ι} (hB : P (B i) = c • B i) : c ≠ 0 :=
  fun hc ↦ B.ne_zero i (P.injective (by simpa [hc] using hB))

/-- The bracket of two eigenvectors of a Lie automorphism is an eigenvector with the product
eigenvalue. -/
private theorem apply_lie_basis_of_apply_basis (B : Basis ι R L) {lam : ι → R} {P : L ≃ₗ⁅R⁆ L}
    (hB : ∀ i, P (B i) = lam i • B i) (i j : ι) :
    P ⁅B i, B j⁆ = (lam i * lam j) • ⁅B i, B j⁆ := by
  rw [P.map_lie, hB i, hB j, smul_lie, lie_smul, smul_smul]

/-- Bracket-specific bilinear basis extensionality against a sum of two bracket terms. -/
private theorem ext_basis_lie (B : Basis ι R L) (D₁ D₂ D₃ D₄ D₅ : Module.End R L)
    (h : ∀ i j, D₁ ⁅B i, B j⁆ = ⁅D₂ (B i), D₃ (B j)⁆ + ⁅D₄ (B i), D₅ (B j)⁆) (x y : L) :
    D₁ ⁅x, y⁆ = ⁅D₂ x, D₃ y⁆ + ⁅D₄ x, D₅ y⁆ := by
  let adL : L →ₗ[R] L →ₗ[R] L := (LieAlgebra.ad R L : L →ₗ⁅R⁆ Module.End R L).toLinearMap
  have hbilin : adL.compr₂ D₁ = adL.compl₁₂ D₂ D₃ + adL.compl₁₂ D₄ D₅ := by
    refine LinearMap.ext_basis B B fun i j ↦ ?_
    simpa [adL] using h i j
  simpa [adL] using LinearMap.congr_fun₂ hbilin x y

end Diagonal

section Real

variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [LieRing L] [LieAlgebra ℝ L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Evaluating `Matrix.toLin B B (Matrix.diagonal (g ∘ lam))` on a bracket of basis eigenvectors
of `P`. -/
private theorem toLin_diagonal_comp_lie_basis (B : Basis ι ℝ L) {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L}
    (hB : ∀ i, P (B i) = lam i • B i) (g : ℝ → ℝ) (i j : ι) :
    Matrix.toLin B B (Matrix.diagonal (fun k ↦ g (lam k))) ⁅B i, B j⁆ =
      g (lam i * lam j) • ⁅B i, B j⁆ :=
  B.apply_eq_smul_of_apply_basis (f := (P : L →ₗ[ℝ] L)) hB
    (fun k ↦ by simp [Matrix.diagonal_apply]) (apply_lie_basis_of_apply_basis B hB i j)
    fun _ hk ↦ congrArg g hk

/-- Diagonal real powers of a positively diagonalizable Lie automorphism preserve the bracket. -/
theorem toLin_diagonal_rpow_map_lie (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hlam : ∀ i, 0 < lam i)
    (hB : ∀ i, P (B i) = lam i • B i) (s : ℝ) (x y : L) :
    Matrix.toLin B B (Matrix.diagonal (fun i ↦ lam i ^ s)) ⁅x, y⁆ =
      ⁅Matrix.toLin B B (Matrix.diagonal (fun i ↦ lam i ^ s)) x,
        Matrix.toLin B B (Matrix.diagonal (fun i ↦ lam i ^ s)) y⁆ := by
  have h := ext_basis_lie B (Matrix.toLin B B (Matrix.diagonal (fun i ↦ lam i ^ s)))
    (Matrix.toLin B B (Matrix.diagonal (fun i ↦ lam i ^ s)))
    (Matrix.toLin B B (Matrix.diagonal (fun i ↦ lam i ^ s))) 0 0 (fun i j ↦ by
      rw [toLin_diagonal_comp_lie_basis B hB (· ^ s),
        show Matrix.toLin B B (Matrix.diagonal (fun i ↦ lam i ^ s)) (B i) = lam i ^ s • B i by
          simp [Matrix.diagonal_apply],
        show Matrix.toLin B B (Matrix.diagonal (fun i ↦ lam i ^ s)) (B j) = lam j ^ s • B j by
          simp [Matrix.diagonal_apply],
        LinearMap.zero_apply, LinearMap.zero_apply, lie_zero, add_zero, smul_lie, lie_smul,
        smul_smul, Real.mul_rpow (hlam i).le (hlam j).le]) x y
  simpa using h

/-- Real power `P ^ s` of a positively diagonalizable Lie automorphism as a Lie automorphism. -/
noncomputable def rpowLieEquiv (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hlam : ∀ i, 0 < lam i)
    (hB : ∀ i, P (B i) = lam i • B i) (s : ℝ) : L ≃ₗ⁅ℝ⁆ L where
  __ := Matrix.toLin B B (Matrix.diagonal (fun i ↦ lam i ^ s))
  invFun := Matrix.toLin B B (Matrix.diagonal (fun i ↦ lam i ^ (-s)))
  left_inv y := by
    have h := LinearMap.congr_fun (Matrix.toLin_diagonal_rpow_comp B hlam (-s) s) y
    have hone : (fun i : ι ↦ lam i ^ (-s + s)) = 1 := by ext i; simp
    simpa only [LinearMap.toFun_eq_coe, LinearMap.comp_apply, hone, Matrix.diagonal_one',
      Matrix.toLin_one, LinearMap.id_apply] using h
  right_inv y := by
    have h := LinearMap.congr_fun (Matrix.toLin_diagonal_rpow_comp B hlam s (-s)) y
    have hone : (fun i : ι ↦ lam i ^ (s + -s)) = 1 := by ext i; simp
    simpa only [LinearMap.toFun_eq_coe, LinearMap.comp_apply, hone, Matrix.diagonal_one',
      Matrix.toLin_one, LinearMap.id_apply] using h
  map_lie' := toLin_diagonal_rpow_map_lie B hlam hB s _ _

/-- Evaluating `rpowLieEquiv B hlam hB s` gives the diagonal power endomorphism. -/
theorem rpowLieEquiv_apply (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hlam : ∀ i, 0 < lam i)
    (hB : ∀ i, P (B i) = lam i • B i) (s : ℝ) (y : L) :
    rpowLieEquiv B hlam hB s y =
      Matrix.toLin B B (Matrix.diagonal (fun i ↦ lam i ^ s)) y := by
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
  suffices h : Matrix.toLin B B (Matrix.diagonal (fun i ↦ lam i ^ (1 : ℝ))) = (P : L →ₗ[ℝ] L) from
    congr($h y)
  exact B.ext fun i ↦ by simp [Matrix.diagonal_apply, hB]

/-- `P ^ s (P ^ t y) = P ^ (s + t) y`. -/
theorem rpowLieEquiv_add (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hlam : ∀ i, 0 < lam i)
    (hB : ∀ i, P (B i) = lam i • B i) (s t : ℝ) (y : L) :
    rpowLieEquiv B hlam hB s (rpowLieEquiv B hlam hB t y) =
      rpowLieEquiv B hlam hB (s + t) y :=
  LinearMap.congr_fun (Matrix.toLin_diagonal_rpow_comp B hlam s t) y

/-- The diagonal logarithm of a real diagonalizable Lie automorphism satisfies the Leibniz
rule. -/
theorem toLin_diagonal_log_leibniz (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hB : ∀ i, P (B i) = lam i • B i) (x y : L) :
    Matrix.toLin B B (Matrix.diagonal (Real.log ∘ lam)) ⁅x, y⁆ =
      ⁅x, Matrix.toLin B B (Matrix.diagonal (Real.log ∘ lam)) y⁆ -
        ⁅y, Matrix.toLin B B (Matrix.diagonal (Real.log ∘ lam)) x⁆ := by
  have h := ext_basis_lie B (Matrix.toLin B B (Matrix.diagonal (Real.log ∘ lam)))
    LinearMap.id (Matrix.toLin B B (Matrix.diagonal (Real.log ∘ lam)))
    (Matrix.toLin B B (Matrix.diagonal (Real.log ∘ lam))) LinearMap.id (fun i j ↦ by
      dsimp only [Function.comp_def]
      rw [toLin_diagonal_comp_lie_basis B hB Real.log,
        show Matrix.toLin B B (Matrix.diagonal (fun k ↦ Real.log (lam k))) (B i) =
          Real.log (lam i) • B i by simp [Matrix.diagonal_apply],
        show Matrix.toLin B B (Matrix.diagonal (fun k ↦ Real.log (lam k))) (B j) =
          Real.log (lam j) • B j by simp [Matrix.diagonal_apply],
        LinearMap.id_apply, LinearMap.id_apply,
        Real.log_mul (eigenvalue_ne_zero_of_apply_basis B (hB i))
          (eigenvalue_ne_zero_of_apply_basis B (hB j)),
        add_smul, lie_smul, smul_lie, add_comm]) x y
  rw [h, LinearMap.id_apply, LinearMap.id_apply, sub_eq_add_neg, lie_skew]

/-- Logarithmic derivation `log P` of a real diagonalizable Lie automorphism. -/
noncomputable def logLieDerivation (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hB : ∀ i, P (B i) = lam i • B i) : LieDerivation ℝ L L where
  toLinearMap := Matrix.toLin B B (Matrix.diagonal (Real.log ∘ lam))
  leibniz' := toLin_diagonal_log_leibniz B hB

/-- Evaluating `logLieDerivation` gives the diagonal logarithm endomorphism. -/
theorem logLieDerivation_apply (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hB : ∀ i, P (B i) = lam i • B i) (y : L) :
    logLieDerivation B hB y = Matrix.toLin B B (Matrix.diagonal (Real.log ∘ lam)) y := by
  rfl

/-- On any `μ`-eigenvector of `s • log P`, the power `P ^ s` acts by `Real.exp μ`. -/
theorem rpowLieEquiv_apply_of_log_eq_smul (B : Basis ι ℝ L)
    {lam : ι → ℝ} {P : L ≃ₗ⁅ℝ⁆ L} (hlam : ∀ i, 0 < lam i)
    (hB : ∀ i, P (B i) = lam i • B i) {s μ : ℝ} {y : L}
    (hy : s • logLieDerivation B hB y = μ • y) :
    rpowLieEquiv B hlam hB s y = Real.exp μ • y := by
  have hlin : Matrix.toLin B B (Matrix.diagonal (fun i ↦ s * Real.log (lam i))) y = μ • y := by
    have heq : Matrix.toLin B B (Matrix.diagonal (fun i ↦ s * Real.log (lam i))) =
        s • Matrix.toLin B B (Matrix.diagonal (Real.log ∘ lam)) := by
      rw [← map_smul, ← Matrix.diagonal_smul]
      rfl
    simpa [heq, logLieDerivation_apply] using hy
  exact B.apply_eq_smul_of_apply_basis
    (a := fun i ↦ s * Real.log (lam i)) (c := fun i ↦ lam i ^ s)
    (fun i ↦ by simp [Matrix.diagonal_apply])
    (fun i ↦ by simp [rpowLieEquiv_apply, Matrix.diagonal_apply]) hlin fun i hi ↦ by
      rw [Real.rpow_def_of_pos (hlam i), mul_comm, hi]

end Real

end LieEquiv
