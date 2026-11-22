/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Basis.Bilinear
import TauCeti.Algebra.Lie.Hom

/-!
# Real powers and logarithm of a positive-eigenbasis Lie automorphism

For a Lie algebra automorphism `P : L ≃ₗ⁅ℝ⁆ L` diagonal in a basis `b` with strictly positive
eigenvalues `lam i > 0`, extending `lam i ^ s` and `Real.log (lam i)` linearly via
`Module.Basis.diagMap` defines a one-parameter group of Lie automorphisms (`LieEquiv.rpow`) and a
Lie derivation (`LieEquiv.logDerivation`) independent of the eigenbasis and satisfying
`(log P) (σ y) = -σ ((log P) y)` whenever `σ` conjugates `P` to `P⁻¹`.

## Main definitions and results

* `Module.Basis.diagMap_rpow_comp`: composing real-power diagonal endomorphisms adds exponents.
* `LieEquiv.rpow`, `LieEquiv.rpow_apply_basis`, `LieEquiv.rpow_apply_of_eigenvector`,
  `LieEquiv.rpow_eq_of_basis`, `LieEquiv.rpow_zero`, `LieEquiv.rpow_one`,
  `LieEquiv.rpow_trans`, `LieEquiv.rpow_symm`.
* `LieEquiv.logDerivation`, `LieEquiv.logDerivation_apply_basis`,
  `LieEquiv.logDerivation_apply_of_eigenvector`, `LieEquiv.logDerivation_eq_of_basis`,
  `LieEquiv.logDerivation_apply_conj`.
-/

public section

section RealDiagMap

/-- Composing two real-power diagonal endomorphisms adds their exponents. -/
theorem Module.Basis.diagMap_rpow_comp {ι V : Type*} [AddCommMonoid V] [Module ℝ V]
    (b : Module.Basis ι ℝ V) {lam : ι → ℝ} (hlam : ∀ i, 0 < lam i) (s t : ℝ) :
    (b.diagMap fun i ↦ lam i ^ t).comp (b.diagMap fun i ↦ lam i ^ s) =
      b.diagMap fun i ↦ lam i ^ (s + t) := by
  rw [b.diagMap_comp]; congr 1; ext i; rw [← Real.rpow_add (hlam i), add_comm]

end RealDiagMap

namespace LieEquiv

attribute [local instance 100] LieRing.ofAssociativeRing

open LieAlgebra

variable {ι L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- **Real power of a positive-eigenbasis Lie automorphism**: if `P : L ≃ₗ⁅ℝ⁆ L` acts on a basis
`b` by strictly positive eigenvalues `lam i > 0`, then extending `b i ↦ lam i ^ s • b i` linearly
yields a Lie algebra automorphism `P.rpow b hb hlam s`. -/
noncomputable def rpow (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) (s : ℝ) : L ≃ₗ⁅ℝ⁆ L :=
  let f : ℝ → L →ₗ[ℝ] L := fun t ↦ b.diagMap fun i ↦ lam i ^ t
  have hinv (u v : ℝ) (h : u + v = 0) (x : L) : f v (f u x) = x := by
    rw [← LinearMap.comp_apply]; dsimp only [f]
    rw [b.diagMap_rpow_comp hlam u v, h]; simp [Real.rpow_zero, ← Pi.one_def]
  { toFun := f s, invFun := f (-s)
    left_inv := hinv s (-s) (add_neg_cancel s), right_inv := hinv (-s) s (neg_add_cancel s)
    map_add' := (f s).map_add, map_smul' := (f s).map_smul
    map_lie' := fun {x y} ↦ by
      have hbil : (LinearMap.llcomp ℝ L L L (f s)).comp (LieAlgebra.ad ℝ L).toLinearMap =
          ((LieAlgebra.ad ℝ L).toLinearMap.compl₂ (f s)).comp (f s) := by
        refine LinearMap.ext_basis b b fun i j ↦ ?_
        have heig_ij : f s ⁅b i, b j⁆ = (lam i * lam j) ^ s • ⁅b i, b j⁆ :=
          b.apply_eq_smul_of_apply_eq_smul (f := (P : L →ₗ[ℝ] L)) hb
            (fun k hk ↦ by simp [f, hk]) (P.toLieHom.map_lie_of_apply_eq_smul (hb i) (hb j))
        simp only [LinearMap.comp_apply, LinearMap.llcomp_apply, LinearMap.compl₂_apply,
          LieHom.coe_toLinearMap, ad_apply, f, b.diagMap_apply_basis, heig_ij,
          Real.mul_rpow (hlam i).le (hlam j).le, smul_lie, lie_smul, smul_smul]
        rw [mul_comm (lam i ^ s)]
      exact LinearMap.congr_fun (LinearMap.congr_fun hbil x) y }

/-- On each eigenbasis vector `b i`, `P.rpow b hb hlam s` acts by `lam i ^ s`. -/
@[simp]
theorem rpow_apply_basis (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) (s : ℝ) (i : ι) :
    P.rpow b hb hlam s (b i) = lam i ^ s • b i := b.diagMap_apply_basis (fun j ↦ lam j ^ s) i

/-- On every `μ`-eigenvector of `P`, `P.rpow b hb hlam s` acts by `μ ^ s`. -/
theorem rpow_apply_of_eigenvector (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) (s : ℝ)
    {v : L} {μ : ℝ} (hv : P v = μ • v) : P.rpow b hb hlam s v = μ ^ s • v :=
  b.apply_eq_smul_of_apply_eq_smul (f := (P : L →ₗ[ℝ] L)) (g := (P.rpow b hb hlam s : L →ₗ[ℝ] L))
    hb (fun i hi ↦ by rw [LinearEquiv.coe_coe, coe_toLinearEquiv, rpow_apply_basis, hi]) hv

/-- `P.rpow` does not depend on the choice of positive eigenbasis. -/
theorem rpow_eq_of_basis {ι₁ ι₂ : Type*} (P : L ≃ₗ⁅ℝ⁆ L)
    (b₁ : Module.Basis ι₁ ℝ L) {lam₁ : ι₁ → ℝ} (hb₁ : ∀ i, P (b₁ i) = lam₁ i • b₁ i)
    (hlam₁ : ∀ i, 0 < lam₁ i) (b₂ : Module.Basis ι₂ ℝ L) {lam₂ : ι₂ → ℝ}
    (hb₂ : ∀ i, P (b₂ i) = lam₂ i • b₂ i) (hlam₂ : ∀ i, 0 < lam₂ i) (s : ℝ) :
    P.rpow b₁ hb₁ hlam₁ s = P.rpow b₂ hb₂ hlam₂ s :=
  LieEquiv.ext (LinearMap.congr_fun (b₁.ext fun i ↦ by
    simp [rpow_apply_of_eigenvector P b₂ hb₂ hlam₂ s (hb₁ i)]))

/-- The zeroth power `P^0` is the identity automorphism. -/
@[simp]
theorem rpow_zero (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) :
    P.rpow b hb hlam 0 = LieEquiv.refl :=
  LieEquiv.ext (LinearMap.congr_fun (b.ext fun i ↦ by simp))

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
  LieEquiv.ext fun x ↦ LinearMap.congr_fun (b.diagMap_rpow_comp hlam s t) x

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
  let Dlin : L →ₗ[ℝ] L := b.diagMap fun i ↦ Real.log (lam i)
  { toLinearMap := Dlin
    leibniz' := fun x y ↦ by
      rw [← lie_skew y (Dlin x), sub_neg_eq_add, add_comm]
      have hbil : (LinearMap.llcomp ℝ L L L Dlin).comp (LieAlgebra.ad ℝ L).toLinearMap =
          (LieAlgebra.ad ℝ L).toLinearMap.comp Dlin +
            (LieAlgebra.ad ℝ L).toLinearMap.compl₂ Dlin := by
        refine LinearMap.ext_basis b b fun i j ↦ ?_
        have heig_ij : Dlin ⁅b i, b j⁆ = Real.log (lam i * lam j) • ⁅b i, b j⁆ :=
          b.apply_eq_smul_of_apply_eq_smul (f := (P : L →ₗ[ℝ] L)) hb
            (fun k hk ↦ by simp [Dlin, hk]) (P.toLieHom.map_lie_of_apply_eq_smul (hb i) (hb j))
        simp only [LinearMap.comp_apply, LinearMap.llcomp_apply, LinearMap.add_apply,
          LinearMap.compl₂_apply, LieHom.coe_toLinearMap, ad_apply, Dlin, b.diagMap_apply_basis,
          heig_ij, Real.log_mul (hlam i).ne' (hlam j).ne', add_smul, smul_lie, lie_smul]
      exact LinearMap.congr_fun (LinearMap.congr_fun hbil x) y }

/-- On each eigenbasis vector `b i`, `P.logDerivation b hb hlam` scales by `Real.log (lam i)`. -/
@[simp]
theorem logDerivation_apply_basis (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i) (i : ι) :
    P.logDerivation b hb hlam (b i) = Real.log (lam i) • b i :=
  b.diagMap_apply_basis (fun j ↦ Real.log (lam j)) i

/-- On every `μ`-eigenvector of `P`, `P.logDerivation b hb hlam` scales by `Real.log μ`. -/
theorem logDerivation_apply_of_eigenvector (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i)
    {v : L} {μ : ℝ} (hv : P v = μ • v) : P.logDerivation b hb hlam v = Real.log μ • v :=
  b.apply_eq_smul_of_apply_eq_smul (f := (P : L →ₗ[ℝ] L))
    (g := (P.logDerivation b hb hlam : L →ₗ[ℝ] L)) hb
    (fun i hi ↦ by rw [LieDerivation.coeFn_coe, logDerivation_apply_basis, hi]) hv

/-- `P.logDerivation` does not depend on the choice of positive eigenbasis. -/
theorem logDerivation_eq_of_basis {ι₁ ι₂ : Type*} (P : L ≃ₗ⁅ℝ⁆ L)
    (b₁ : Module.Basis ι₁ ℝ L) {lam₁ : ι₁ → ℝ} (hb₁ : ∀ i, P (b₁ i) = lam₁ i • b₁ i)
    (hlam₁ : ∀ i, 0 < lam₁ i) (b₂ : Module.Basis ι₂ ℝ L) {lam₂ : ι₂ → ℝ}
    (hb₂ : ∀ i, P (b₂ i) = lam₂ i • b₂ i) (hlam₂ : ∀ i, 0 < lam₂ i) :
    P.logDerivation b₁ hb₁ hlam₁ = P.logDerivation b₂ hb₂ hlam₂ :=
  LieDerivation.ext (LinearMap.congr_fun (b₁.ext fun i ↦ by
    simp [LieDerivation.coeFn_coe, logDerivation_apply_of_eigenvector P b₂ hb₂ hlam₂ (hb₁ i)]))

/-- If a linear map `σ` conjugates `P` to `P⁻¹` (`σ (P x) = P.symm (σ x)`), then `log P`
anticommutes with `σ`. -/
theorem logDerivation_apply_conj (P : L ≃ₗ⁅ℝ⁆ L) (b : Module.Basis ι ℝ L) {lam : ι → ℝ}
    (hb : ∀ i, P (b i) = lam i • b i) (hlam : ∀ i, 0 < lam i)
    (σ : L →ₗ[ℝ] L) (hσ : ∀ x, σ (P x) = P.symm (σ x)) (y : L) :
    P.logDerivation b hb hlam (σ y) = -σ (P.logDerivation b hb hlam y) := by
  have hlin : (P.logDerivation b hb hlam : L →ₗ[ℝ] L).comp σ =
      -(σ.comp (P.logDerivation b hb hlam : L →ₗ[ℝ] L)) := b.ext fun i ↦ by
    have hPi := P.toLinearEquiv.apply_eq_inv_smul_of_conj σ hσ (hlam i).ne' (hb i)
    rw [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.comp_apply,
      LieDerivation.coeFn_coe, logDerivation_apply_of_eigenvector P b hb hlam hPi, Real.log_inv,
      logDerivation_apply_basis, map_smul, neg_smul]
  simpa using LinearMap.congr_fun hlin y

end LieEquiv
