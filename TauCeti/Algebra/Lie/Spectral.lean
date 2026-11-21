/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis

/-!
# Real powers and logarithm of a positive-eigenbasis Lie automorphism

For a Lie algebra automorphism `P : L ≃ₗ⁅ℝ⁆ L` diagonal in a finite basis `b` with strictly
positive eigenvalues `lam i > 0`, extending `lam i ^ s` and `Real.log (lam i)` linearly defines a
one-parameter group of Lie automorphisms (`LieEquiv.rpow`) and a Lie derivation
(`LieEquiv.logDerivation`) satisfying `(log P) (σ y) = -σ ((log P) y)` whenever `σ` conjugates `P`
to `P⁻¹`.

## Main definitions and results

* `LieEquiv.rpow`, `LieEquiv.rpow_apply_basis`, `LieEquiv.rpow_apply_of_eigenvector`,
  `LieEquiv.rpow_zero`, `LieEquiv.rpow_one`, `LieEquiv.rpow_trans`, `LieEquiv.rpow_symm`.
* `LieEquiv.logDerivation`, `LieEquiv.logDerivation_apply_basis`,
  `LieEquiv.logDerivation_apply_of_eigenvector`, `LieEquiv.logDerivation_apply_conj`.
-/

public section

namespace LieEquiv

open LieAlgebra

variable {ι L : Type*} [LieRing L] [LieAlgebra ℝ L]

private noncomputable def rpowLin (b : Module.Basis ι ℝ L) (lam : ι → ℝ) (s : ℝ) : L →ₗ[ℝ] L :=
  b.constr ℝ fun i ↦ lam i ^ s • b i

private theorem rpowLin_comp (b : Module.Basis ι ℝ L) {lam : ι → ℝ} (hlam : ∀ i, 0 < lam i)
    (s t : ℝ) : (rpowLin b lam t).comp (rpowLin b lam s) = rpowLin b lam (s + t) :=
  b.ext fun i ↦ by
    simp only [LinearMap.comp_apply, rpowLin, b.constr_basis, map_smul, smul_smul,
      ← Real.rpow_add (hlam i), add_comm s t]

private theorem rpowLin_zero (b : Module.Basis ι ℝ L) (lam : ι → ℝ) :
    rpowLin b lam 0 = LinearMap.id :=
  b.ext fun i ↦ by simp [rpowLin]

section Finite

variable [Finite ι]

/-- **Real power of a positive-eigenbasis Lie automorphism**: if `P : L ≃ₗ⁅ℝ⁆ L` acts on a basis
`b` by strictly positive eigenvalues `lam i > 0`, then extending `b i ↦ lam i ^ s • b i` linearly
yields a Lie algebra automorphism `P.rpow b hb hlam s`. -/
noncomputable def rpow (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) (s : ℝ) : L ≃ₗ⁅ℝ⁆ L :=
  letI := Fintype.ofFinite ι
  have hbasis (i : ι) : rpowLin b lam s (b i) = lam i ^ s • b i := b.constr_basis ℝ _ i
  have heig {v : L} {μ : ℝ} (hv : P v = μ • v) : rpowLin b lam s v = μ ^ s • v :=
    b.apply_eq_smul_of_apply_eq_smul (f := (P : L →ₗ[ℝ] L)) hb (fun i hi ↦ by rw [hbasis, hi]) hv
  have hinv (s t : ℝ) (h : s + t = 0) (x : L) : rpowLin b lam t (rpowLin b lam s x) = x := by
    simpa [h, rpowLin_zero] using LinearMap.congr_fun (rpowLin_comp b hlam s t) x
  { toFun := rpowLin b lam s
    invFun := rpowLin b lam (-s)
    left_inv := hinv s (-s) (add_neg_cancel s)
    right_inv := hinv (-s) s (neg_add_cancel s)
    map_add' := (rpowLin b lam s).map_add
    map_smul' := (rpowLin b lam s).map_smul
    map_lie' := fun {x y} ↦ by
      have hlie_b (i j : ι) :
          rpowLin b lam s ⁅b i, b j⁆ = ⁅rpowLin b lam s (b i), rpowLin b lam s (b j)⁆ := by
        have hP : P ⁅b i, b j⁆ = (lam i * lam j) • ⁅b i, b j⁆ := by
          rw [map_lie, hb i, hb j, smul_lie, lie_smul, smul_smul]
        rw [heig hP, Real.mul_rpow (hlam i).le (hlam j).le, hbasis, hbasis, smul_lie, lie_smul,
          smul_smul]
      conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
      conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
      simp only [sum_lie_sum, map_sum, map_smul, smul_lie, lie_smul, hlie_b] }

/-- On each eigenbasis vector `b i`, `P.rpow b hb hlam s` acts by `lam i ^ s`. -/
@[simp]
theorem rpow_apply_basis (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) (s : ℝ) (i : ι) :
    P.rpow b hb hlam s (b i) = lam i ^ s • b i := b.constr_basis ℝ _ i

/-- On every `μ`-eigenvector of `P`, `P.rpow b hb hlam s` acts by `μ ^ s`. -/
theorem rpow_apply_of_eigenvector (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) (s : ℝ)
    {v : L} {μ : ℝ} (hv : P v = μ • v) : P.rpow b hb hlam s v = μ ^ s • v :=
  b.apply_eq_smul_of_apply_eq_smul (f := (P : L →ₗ[ℝ] L)) (g := (P.rpow b hb hlam s : L →ₗ[ℝ] L))
    hb (fun i hi ↦ by rw [LinearEquiv.coe_coe, coe_toLinearEquiv, rpow_apply_basis, hi]) hv

/-- The zeroth power `P^0` is the identity automorphism. -/
@[simp]
theorem rpow_zero (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) :
    P.rpow b hb hlam 0 = LieEquiv.refl :=
  LieEquiv.ext fun x ↦ LinearMap.congr_fun (rpowLin_zero b lam) x

/-- The first power `P^1` is `P` itself. -/
@[simp]
theorem rpow_one (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) :
    P.rpow b hb hlam 1 = P :=
  LieEquiv.ext (LinearMap.congr_fun (b.ext fun i ↦ by simp [hb i]))

/-- Real powers of `P` satisfy `(P^s).trans (P^t) = P^(s + t)`. -/
theorem rpow_trans (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) (s t : ℝ) :
    (P.rpow b hb hlam s).trans (P.rpow b hb hlam t) = P.rpow b hb hlam (s + t) :=
  LieEquiv.ext fun x ↦ LinearMap.congr_fun (rpowLin_comp b hlam s t) x

/-- The inverse of `P^s` is `P^(-s)`. -/
@[simp]
theorem rpow_symm (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) (s : ℝ) :
    (P.rpow b hb hlam s).symm = P.rpow b hb hlam (-s) := by
  ext x; rw [symm_apply_eq]; simp [← trans_apply, rpow_trans]

/-- **Spectral logarithm of a positive-eigenbasis Lie automorphism**: extending
`b i ↦ Real.log (lam i) • b i` linearly defines a Lie derivation of `L`. -/
noncomputable def logDerivation (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) : LieDerivation ℝ L L :=
  letI := Fintype.ofFinite ι
  let Dlin : L →ₗ[ℝ] L := b.constr ℝ fun i ↦ Real.log (lam i) • b i
  have hbasis (i : ι) : Dlin (b i) = Real.log (lam i) • b i := b.constr_basis ℝ _ i
  have heig {v : L} {μ : ℝ} (hv : P v = μ • v) : Dlin v = Real.log μ • v :=
    b.apply_eq_smul_of_apply_eq_smul (f := (P : L →ₗ[ℝ] L)) hb (fun i hi ↦ by rw [hbasis, hi]) hv
  have hlie_b (i j : ι) : Dlin ⁅b i, b j⁆ = ⁅Dlin (b i), b j⁆ + ⁅b i, Dlin (b j)⁆ := by
    have hP : P ⁅b i, b j⁆ = (lam i * lam j) • ⁅b i, b j⁆ := by
      rw [map_lie, hb i, hb j, smul_lie, lie_smul, smul_smul]
    rw [heig hP, Real.log_mul (hlam i).ne' (hlam j).ne', add_smul, hbasis, hbasis, smul_lie,
      lie_smul]
  { toLinearMap := Dlin
    leibniz' := fun x y ↦ by
      rw [← lie_skew y (Dlin x), sub_neg_eq_add, add_comm]
      conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
      conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
      simp only [sum_lie_sum, map_sum, map_smul, smul_lie, lie_smul, hlie_b, smul_add,
        Finset.sum_add_distrib] }

/-- On each eigenbasis vector `b i`, `P.logDerivation b hb hlam` scales by `Real.log (lam i)`. -/
@[simp]
theorem logDerivation_apply_basis (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) (i : ι) :
    P.logDerivation b hb hlam (b i) = Real.log (lam i) • b i := b.constr_basis ℝ _ i

/-- On every `μ`-eigenvector of `P`, `P.logDerivation b hb hlam` scales by `Real.log μ`. -/
theorem logDerivation_apply_of_eigenvector (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i)
    {v : L} {μ : ℝ} (hv : P v = μ • v) : P.logDerivation b hb hlam v = Real.log μ • v :=
  b.apply_eq_smul_of_apply_eq_smul (f := (P : L →ₗ[ℝ] L))
    (g := (P.logDerivation b hb hlam : L →ₗ[ℝ] L)) hb
    (fun i hi ↦ by change P.logDerivation b hb hlam (b i) = _; simp [hi]) hv

/-- If a linear map `σ` conjugates `P` to `P⁻¹` (`σ (P x) = P.symm (σ x)`), then `log P`
anticommutes with `σ`. -/
theorem logDerivation_apply_conj (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i)
    (σ : L →ₗ[ℝ] L) (hσ : ∀ x, σ (P x) = P.symm (σ x)) (y : L) :
    P.logDerivation b hb hlam (σ y) = -σ (P.logDerivation b hb hlam y) := by
  have hlin : (P.logDerivation b hb hlam : L →ₗ[ℝ] L).comp σ =
      -(σ.comp (P.logDerivation b hb hlam : L →ₗ[ℝ] L)) := b.ext fun i ↦ by
    have hPi := P.toLinearEquiv.apply_eq_inv_smul_of_conj σ hσ (hlam i).ne' (hb i)
    change P.logDerivation b hb hlam (σ (b i)) = -σ (P.logDerivation b hb hlam (b i))
    rw [logDerivation_apply_of_eigenvector P b hb hlam hPi, Real.log_inv,
      logDerivation_apply_basis, map_smul, neg_smul]
  simpa using LinearMap.congr_fun hlin y

end Finite

end LieEquiv
