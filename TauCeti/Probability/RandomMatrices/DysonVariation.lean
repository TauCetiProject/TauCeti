/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.Derivative
public import TauCeti.Probability.RandomMatrices.GaussianEnsemble
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Matrix.Eigenvalues.Basic

/-!
# Coordinate variation of sorted eigenvalues for Gaussian ensembles

This file combines Hadamard's first and second eigenvalue variation formulas
(`TauCeti.Analysis.Matrix.Eigenvalues.Derivative`) with the coordinate parameterization and
quadratic Casimir / trace inner-product identities of `gaussianEnsemble β n`
(`TauCeti.Probability.RandomMatrices.GaussianEnsemble`) to compute deterministic multivariable
Fréchet and 1D coordinate-ray derivatives at simple sorted eigenvalues of
`A + gaussianEnsemble β n g` (hence on the open simple-spectrum locus).

These deterministic coordinate-gradient inner-product and coordinate half-Laplacian identities
supply the `(2 / (β n)) δₖₘ` diffusion bracket and `n⁻¹ ∑_{j ≠ k} (λₖ - λⱼ)⁻¹` repulsion drift
coefficients when applying Itô's formula to simple eigenvalues of GOE (`β = 1`, symmetric `A`) and
GUE (`β = 2`, Hermitian `A`) matrix Brownian motions (Anderson–Guionnet–Zeitouni Theorem 4.3.2).

To state or use the normed Fréchet and directional calculus declarations in this file,
`open scoped Matrix.Norms.L2Operator` and enable
`attribute [local instance] Matrix.l2OpNormedAlgebraReal`.

## Main results

* `TauCeti.Probability.contDiffAt_eigenvalues₀_add_gaussianEnsemble`,
  `TauCeti.Probability.hasStrictFDerivAt_eigenvalues₀_add_gaussianEnsemble`,
  `TauCeti.Probability.fderiv_eigenvalues₀_add_gaussianEnsemble_apply`, and
  `TauCeti.Probability.fderiv_fderiv_eigenvalues₀_add_gaussianEnsemble_apply`: smoothness and
  first/second Fréchet derivatives on `Fin n × Fin n → ℝ`.
* `TauCeti.Probability.sum_fderiv_eigenvalues₀_add_gaussianEnsemble_single_mul_of_ne_one`,
  `TauCeti.Probability.sum_fderiv_eigenvalues₀_add_gaussianEnsemble_single_mul_of_eq_one`,
  `TauCeti.Probability.sum_fderiv_eigenvalues₀_add_gaussianEnsemble_single_mul`, and
  `TauCeti.Probability.half_sum_fderiv_fderiv_eigenvalues₀_add_gaussianEnsemble_single`:
  deterministic coordinate-gradient inner-product and coordinate half-Laplacian identities in
  Fréchet form.
* `TauCeti.Probability.hasDerivAt_eigenvalues₀_add_gaussianEnsemble`,
  `TauCeti.Probability.iteratedDeriv_two_eigenvalues₀_add_gaussianEnsemble`,
  `TauCeti.Probability.sum_deriv_eigenvalues₀_add_gaussianEnsemble_mul_of_ne_one`,
  `TauCeti.Probability.sum_deriv_eigenvalues₀_add_gaussianEnsemble_mul_of_eq_one`,
  `TauCeti.Probability.sum_deriv_eigenvalues₀_add_gaussianEnsemble_mul`, and
  `TauCeti.Probability.half_sum_iteratedDeriv_two_eigenvalues₀_add_gaussianEnsemble`: 1D
  coordinate-ray corollaries.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices* (2010), §4.3.1.
* T. Tao, *Topics in Random Matrix Theory*, AMS (2012), §1.3.4 and §3.1.
-/

public section

noncomputable section

open Matrix Topology
open scoped ContDiff Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal

namespace TauCeti

namespace Probability

private def shiftEnsembleSelfAdjoint (β n : ℕ) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (g' : Fin n × Fin n → ℝ) :
    selfAdjoint (Matrix (Fin n) (Fin n) ℂ) :=
  (⟨A, hA.isSelfAdjoint⟩ : selfAdjoint (Matrix (Fin n) (Fin n) ℂ)) +
    gaussianEnsembleSelfAdjointCLM β n g'

@[simp]
private theorem coe_shiftEnsembleSelfAdjoint (β n : ℕ) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (g' : Fin n × Fin n → ℝ) :
    (shiftEnsembleSelfAdjoint β n hA g' : Matrix (Fin n) (Fin n) ℂ) =
      A + gaussianEnsemble β n g' := by
  simp [shiftEnsembleSelfAdjoint]

private theorem hasStrictFDerivAt_shiftEnsembleSelfAdjoint (β n : ℕ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g : Fin n × Fin n → ℝ) :
    HasStrictFDerivAt (shiftEnsembleSelfAdjoint β n hA)
      (gaussianEnsembleSelfAdjointCLM β n) g :=
  (gaussianEnsembleSelfAdjointCLM β n).hasStrictFDerivAt.const_add _

private theorem contDiff_shiftEnsembleSelfAdjoint (β n : ℕ) {r : ℕ∞ω}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ContDiff ℝ r (shiftEnsembleSelfAdjoint β n hA) :=
  contDiff_const.add (gaussianEnsembleSelfAdjointCLM β n).contDiff

private theorem eigenvalues₀_add_gaussianEnsemble_comp_eq {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (k : Fin (Fintype.card (Fin n))) :
    (fun g' : Fin n × Fin n → ℝ ↦
        (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k) =
      (fun X : selfAdjoint (Matrix (Fin n) (Fin n) ℂ) ↦ X.2.isHermitian.eigenvalues₀ k) ∘
        shiftEnsembleSelfAdjoint β n hA :=
  funext fun g' ↦ congrFun
    ((hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀_congr
      (shiftEnsembleSelfAdjoint β n hA g').2.isHermitian (by simp)) k

private theorem forall_eigenvalues₀_selfAdjoint_ne {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) {g : Fin n × Fin n → ℝ}
    {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    ∀ j ≠ k,
      (shiftEnsembleSelfAdjoint β n hA g).2.isHermitian.eigenvalues₀ j ≠
        (shiftEnsembleSelfAdjoint β n hA g).2.isHermitian.eigenvalues₀ k := by
  have h := (shiftEnsembleSelfAdjoint β n hA g).2.isHermitian.eigenvalues₀_congr
    (hA.add (isHermitian_gaussianEnsemble β n g)) (by simp)
  simpa only [h] using hk

/-- At any `g` where `λₖ(A + gaussianEnsemble β n g)` is simple,
`g' ↦ (A + gaussianEnsemble β n g').eigenvalues₀ k` is `C^r` for every `r : ℕ∞ω`. -/
theorem contDiffAt_eigenvalues₀_add_gaussianEnsemble {β n : ℕ} {r : ℕ∞ω}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g : Fin n × Fin n → ℝ)
    {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    ContDiffAt ℝ r (fun g' : Fin n × Fin n → ℝ ↦
      (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k) g := by
  rw [eigenvalues₀_add_gaussianEnsemble_comp_eq hA k]
  exact (contDiffAt_eigenvalues₀ (forall_eigenvalues₀_selfAdjoint_ne hA hk)).comp g
    (contDiff_shiftEnsembleSelfAdjoint β n hA).contDiffAt

/-- Strict Fréchet derivative of `g' ↦ (A + gaussianEnsemble β n g').eigenvalues₀ k` at a point `g`
where `λₖ(A + gaussianEnsemble β n g)` is simple. -/
theorem hasStrictFDerivAt_eigenvalues₀_add_gaussianEnsemble {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g : Fin n × Fin n → ℝ)
    {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    HasStrictFDerivAt
      (fun g' : Fin n × Fin n → ℝ ↦
        (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k)
      ((RCLike.reCLM (K := ℂ)).comp <|
        (Matrix.traceCLM (Fin n) ℝ ℂ).comp <|
          (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)
            ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenprojector₀ k)).comp <|
            (selfAdjoint.subtypeL ℝ (Matrix (Fin n) (Fin n) ℂ)).comp
              (gaussianEnsembleSelfAdjointCLM β n)) g := by
  rw [eigenvalues₀_add_gaussianEnsemble_comp_eq hA k]
  refine ((hasStrictFDerivAt_eigenvalues₀ (forall_eigenvalues₀_selfAdjoint_ne hA hk)).comp g
    (hasStrictFDerivAt_shiftEnsembleSelfAdjoint β n hA g)).congr_fderiv ?_
  have hP := congrFun
    ((shiftEnsembleSelfAdjoint β n hA g).2.isHermitian.eigenprojector₀_congr
      (hA.add (isHermitian_gaussianEnsemble β n g)) (by simp)) k
  ext v
  simp [hP]

/-- Applied Fréchet derivative of `g' ↦ (A + gaussianEnsemble β n g').eigenvalues₀ k` at `g` in
direction `v`. -/
theorem fderiv_eigenvalues₀_add_gaussianEnsemble_apply {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g v : Fin n × Fin n → ℝ)
    {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    fderiv ℝ (fun g' : Fin n × Fin n → ℝ ↦
        (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k) g v =
      ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenprojector₀ k *
        gaussianEnsemble β n v).trace.re := by
  rw [(hasStrictFDerivAt_eigenvalues₀_add_gaussianEnsemble hA g hk).hasFDerivAt.fderiv]
  simp

/-- Applied second Fréchet derivative of `g' ↦ (A + gaussianEnsemble β n g').eigenvalues₀ k` at `g`
in directions `v` and `w`. -/
theorem fderiv_fderiv_eigenvalues₀_add_gaussianEnsemble_apply {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g v w : Fin n × Fin n → ℝ)
    {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    fderiv ℝ (fderiv ℝ fun g' : Fin n × Fin n → ℝ ↦
        (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k) g v w =
      2 * ∑ j ∈ Finset.univ.erase k,
        ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k -
          (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j)⁻¹ *
          ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenprojector₀ k *
            gaussianEnsemble β n v *
            (hA.add (isHermitian_gaussianEnsemble β n g)).eigenprojector₀ j *
            gaussianEnsemble β n w).trace.re := by
  have hDΦ : fderiv ℝ (shiftEnsembleSelfAdjoint β n hA) =
      fun _ ↦ gaussianEnsembleSelfAdjointCLM β n :=
    funext fun g' ↦ (hasStrictFDerivAt_shiftEnsembleSelfAdjoint β n hA g').hasFDerivAt.fderiv
  have hkΦ := forall_eigenvalues₀_selfAdjoint_ne hA hk
  rw [eigenvalues₀_add_gaussianEnsemble_comp_eq hA k,
    TauCeti.fderiv_fderiv_comp_apply (φ := shiftEnsembleSelfAdjoint β n hA)
      (contDiffAt_eigenvalues₀ hkΦ) (contDiff_shiftEnsembleSelfAdjoint β n hA).contDiffAt v w,
    hDΦ, fderiv_const_apply, zero_apply, zero_apply,
    map_zero, add_zero, fderiv_fderiv_eigenvalues₀_apply hkΦ]
  have heig := (shiftEnsembleSelfAdjoint β n hA g).2.isHermitian.eigenvalues₀_congr
    (hA.add (isHermitian_gaussianEnsemble β n g)) (by simp)
  have hproj := (shiftEnsembleSelfAdjoint β n hA g).2.isHermitian.eigenprojector₀_congr
    (hA.add (isHermitian_gaussianEnsemble β n g)) (by simp)
  rw [heig, hproj]
  simp

/-- **GUE coordinate-gradient inner product** (Fréchet form): for `β ≠ 1`, Hermitian `A`, and
simple sorted eigenvalues `λₖ, λₘ` of `A + gaussianEnsemble β n g`, summing the product of their
coordinate partial derivatives over `p : Fin n × Fin n` yields `n⁻¹ * δₖₘ`. -/
theorem sum_fderiv_eigenvalues₀_add_gaussianEnsemble_single_mul_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g : Fin n × Fin n → ℝ)
    {k m : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k)
    (hm : ∀ j ≠ m, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ m) :
    ∑ p : Fin n × Fin n,
        fderiv ℝ (fun g' ↦ (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k)
          g (Pi.single p 1) *
        fderiv ℝ (fun g' ↦ (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ m)
          g (Pi.single p 1) =
      if k = m then (n : ℝ)⁻¹ else 0 := by
  set hH := hA.add (isHermitian_gaussianEnsemble β n g)
  simp_rw [fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g (Pi.single _ 1) hk,
    fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g (Pi.single _ 1) hm]
  rw [sum_re_trace_mul_gaussianEnsemble_single_mul_of_ne_one hβ (hH.isHermitian_eigenprojector₀ k)
    (hH.isHermitian_eigenprojector₀ m)]
  by_cases hkm : k = m
  · subst hkm; simp [hH.eigenprojector₀_mul_self, hH.trace_eigenprojector₀]
  · simp [hkm, hH.eigenprojector₀_mul_of_ne hkm]

/-- **GOE coordinate-gradient inner product** (Fréchet form): for `β = 1`, Hermitian symmetric `A`,
and simple sorted eigenvalues `λₖ, λₘ` of `A + gaussianEnsemble β n g`, summing the product of their
coordinate partial derivatives over `p : Fin n × Fin n` yields `2 * n⁻¹ * δₖₘ`. -/
theorem sum_fderiv_eigenvalues₀_add_gaussianEnsemble_single_mul_of_eq_one {β n : ℕ} (hβ : β = 1)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hA_symm : A.IsSymm)
    (g : Fin n × Fin n → ℝ) {k m : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k)
    (hm : ∀ j ≠ m, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ m) :
    ∑ p : Fin n × Fin n,
        fderiv ℝ (fun g' ↦ (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k)
          g (Pi.single p 1) *
        fderiv ℝ (fun g' ↦ (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ m)
          g (Pi.single p 1) =
      if k = m then 2 * (n : ℝ)⁻¹ else 0 := by
  set hH := hA.add (isHermitian_gaussianEnsemble β n g)
  have hPm_symm : (hH.eigenprojector₀ m).IsSymm :=
    hH.isSymm_eigenprojector₀ (hA_symm.add (isSymm_gaussianEnsemble_of_eq_one hβ g)) hm
  simp_rw [fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g (Pi.single _ 1) hk,
    fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g (Pi.single _ 1) hm]
  rw [sum_re_trace_mul_gaussianEnsemble_single_mul_of_eq_one hβ (hH.isHermitian_eigenprojector₀ k)
    (hH.isHermitian_eigenprojector₀ m), hPm_symm.eq]
  by_cases hkm : k = m
  · subst hkm; simp [hH.eigenprojector₀_mul_self, hH.trace_eigenprojector₀]; ring
  · simp [hkm, hH.eigenprojector₀_mul_of_ne hkm]

/-- Deterministic coordinate-gradient inner-product identity (Fréchet form) at simple sorted
eigenvalues `λₖ, λₘ` of `A + gaussianEnsemble β n g` for Hermitian `A` under `(β = 1 ∧ A.IsSymm) ∨
β = 2`, giving `(2 / (β * n)) * δₖₘ` (the quadratic-variation coefficient in Anderson–Guionnet–
Zeitouni Theorem 4.3.2). -/
theorem sum_fderiv_eigenvalues₀_add_gaussianEnsemble_single_mul {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (hβ : (β = 1 ∧ A.IsSymm) ∨ β = 2) (g : Fin n × Fin n → ℝ)
    {k m : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k)
    (hm : ∀ j ≠ m, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ m) :
    ∑ p : Fin n × Fin n,
        fderiv ℝ (fun g' ↦ (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k)
          g (Pi.single p 1) *
        fderiv ℝ (fun g' ↦ (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ m)
          g (Pi.single p 1) =
      if k = m then 2 / ((β : ℝ) * n) else 0 := by
  rcases hβ with ⟨hβ1, hA_symm⟩ | rfl
  · rw [sum_fderiv_eigenvalues₀_add_gaussianEnsemble_single_mul_of_eq_one hβ1 hA hA_symm g hk hm,
      hβ1]
    split_ifs <;> simp [div_eq_mul_inv]
  · rw [sum_fderiv_eigenvalues₀_add_gaussianEnsemble_single_mul_of_ne_one (by decide) hA g hk hm]
    split_ifs
    · push_cast; rw [div_mul_eq_div_div, div_self two_ne_zero, one_div]
    · rfl

/-- Deterministic coordinate half-Laplacian identity (Fréchet form) at a simple sorted eigenvalue
`λₖ` of `A + gaussianEnsemble β n g` for Hermitian `A` assuming `β ≠ 1 ∨ A.IsSymm`:
`(1 / 2) * ∑ p, D²λₖ(g)(eₚ, eₚ) = n⁻¹ * ∑ j ≠ k, (λₖ - λⱼ)⁻¹` (supplying the repulsion drift term in
Anderson–Guionnet–Zeitouni Theorem 4.3.2 and Lemma 4.3.4). -/
theorem half_sum_fderiv_fderiv_eigenvalues₀_add_gaussianEnsemble_single {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hβ : β ≠ 1 ∨ A.IsSymm)
    (g : Fin n × Fin n → ℝ) {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    (2 : ℝ)⁻¹ * ∑ p : Fin n × Fin n,
        fderiv ℝ (fderiv ℝ fun g' : Fin n × Fin n → ℝ ↦
          (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k)
          g (Pi.single p 1) (Pi.single p 1) =
      (n : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase k,
        ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k -
          (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j)⁻¹ := by
  set hH := hA.add (isHermitian_gaussianEnsemble β n g)
  simp_rw [fderiv_fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g (Pi.single _ 1)
    (Pi.single _ 1) hk, ← Finset.mul_sum]
  rw [← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
  suffices ∑ p : Fin n × Fin n,
      (hH.eigenprojector₀ k * gaussianEnsemble β n (Pi.single p 1) *
        hH.eigenprojector₀ j * gaussianEnsemble β n (Pi.single p 1)).trace.re = (n : ℝ)⁻¹ by
    rw [← Finset.mul_sum, this, mul_comm]
  rw [show ∑ p : Fin n × Fin n,
      (hH.eigenprojector₀ k * gaussianEnsemble β n (Pi.single p 1) *
        hH.eigenprojector₀ j * gaussianEnsemble β n (Pi.single p 1)).trace.re =
      (hH.eigenprojector₀ k * ∑ p : Fin n × Fin n,
        gaussianEnsemble β n (Pi.single p 1) * hH.eigenprojector₀ j *
          gaussianEnsemble β n (Pi.single p 1)).trace.re by
    rw [Matrix.mul_sum, trace_sum, Complex.re_sum]
    exact Finset.sum_congr rfl fun p _ ↦ by simp only [Matrix.mul_assoc]]
  by_cases hβ1 : β = 1
  · have hPk_symm : (hH.eigenprojector₀ k).IsSymm := hH.isSymm_eigenprojector₀
      ((hβ.resolve_left (not_not.mpr hβ1)).add (isSymm_gaussianEnsemble_of_eq_one hβ1 g)) hk
    have hvanish : (hH.eigenprojector₀ k * (hH.eigenprojector₀ j)ᵀ).trace = 0 := by
      rw [← hPk_symm.eq, ← transpose_mul, trace_transpose, hH.eigenprojector₀_mul_of_ne hjk,
        trace_zero]
    rw [sum_gaussianEnsemble_single_mul_mul_self_of_eq_one hβ1]
    simp [mul_add, hvanish, ← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  · rw [sum_gaussianEnsemble_single_mul_mul_self_of_ne_one hβ1]
    simp [← Complex.ofReal_natCast, ← Complex.ofReal_inv]

/-- Directional derivative of `t ↦ (A + gaussianEnsemble β n (g + t • v)).eigenvalues₀ k` at `0`. -/
theorem hasDerivAt_eigenvalues₀_add_gaussianEnsemble {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g v : Fin n × Fin n → ℝ)
    {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    HasDerivAt
      (fun t : ℝ ↦ (hA.add (isHermitian_gaussianEnsemble β n (g + t • v))).eigenvalues₀ k)
      ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenprojector₀ k *
        gaussianEnsemble β n v).trace.re 0 :=
  (((hasStrictFDerivAt_eigenvalues₀_add_gaussianEnsemble hA g hk).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add g) (by simp)).congr_deriv
    (by simp))

/-- Directional second derivative of `t ↦ (A + gaussianEnsemble β n (g + t • v)).eigenvalues₀ k` at
`0`. -/
theorem iteratedDeriv_two_eigenvalues₀_add_gaussianEnsemble {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g v : Fin n × Fin n → ℝ)
    {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    iteratedDeriv 2
      (fun t : ℝ ↦ (hA.add (isHermitian_gaussianEnsemble β n (g + t • v))).eigenvalues₀ k) 0 =
      2 * ∑ j ∈ Finset.univ.erase k,
        ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k -
          (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j)⁻¹ *
          ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenprojector₀ k *
            gaussianEnsemble β n v *
            (hA.add (isHermitian_gaussianEnsemble β n g)).eigenprojector₀ j *
            gaussianEnsemble β n v).trace.re := by
  have h0 : g + (0 : ℝ) • v = g := by simp
  have h := TauCeti.iteratedDeriv_two_comp (𝕜 := ℝ)
    (f := fun g' : Fin n × Fin n → ℝ ↦
      (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k)
    (γ := fun t : ℝ ↦ g + t • v) (t := 0)
    (by rw [h0]; exact contDiffAt_eigenvalues₀_add_gaussianEnsemble hA g hk)
    (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  simp only [TauCeti.deriv_const_add_smul, TauCeti.iteratedDeriv_two_const_add_smul, Pi.zero_apply,
    map_zero, add_zero, h0,
    fderiv_fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g v v hk] at h
  exact h

/-- **GUE coordinate-gradient inner product** (1D coordinate-ray form): for `β ≠ 1`, Hermitian `A`,
and simple sorted eigenvalues `λₖ, λₘ` of `A + gaussianEnsemble β n g`, the inner product of their
coordinate ray derivatives equals `n⁻¹ * δₖₘ`. -/
theorem sum_deriv_eigenvalues₀_add_gaussianEnsemble_mul_of_ne_one {β n : ℕ} (hβ : β ≠ 1)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (g : Fin n × Fin n → ℝ)
    {k m : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k)
    (hm : ∀ j ≠ m, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ m) :
    ∑ p : Fin n × Fin n,
        deriv (fun t : ℝ ↦
          (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ k) 0 *
        deriv (fun t : ℝ ↦
          (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ m) 0 =
      if k = m then (n : ℝ)⁻¹ else 0 := by
  simp_rw [(hasDerivAt_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single _ 1) hk).deriv,
    (hasDerivAt_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single _ 1) hm).deriv,
    ← fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g (Pi.single _ 1) hk,
    ← fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g (Pi.single _ 1) hm]
  exact sum_fderiv_eigenvalues₀_add_gaussianEnsemble_single_mul_of_ne_one hβ hA g hk hm

/-- **GOE coordinate-gradient inner product** (1D coordinate-ray form): for `β = 1`, Hermitian
symmetric `A`, and simple sorted eigenvalues `λₖ, λₘ` of `A + gaussianEnsemble β n g`, the inner
product of their coordinate ray derivatives equals `2 * n⁻¹ * δₖₘ`. -/
theorem sum_deriv_eigenvalues₀_add_gaussianEnsemble_mul_of_eq_one {β n : ℕ} (hβ : β = 1)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hA_symm : A.IsSymm)
    (g : Fin n × Fin n → ℝ) {k m : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k)
    (hm : ∀ j ≠ m, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ m) :
    ∑ p : Fin n × Fin n,
        deriv (fun t : ℝ ↦
          (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ k) 0 *
        deriv (fun t : ℝ ↦
          (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ m) 0 =
      if k = m then 2 * (n : ℝ)⁻¹ else 0 := by
  simp_rw [(hasDerivAt_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single _ 1) hk).deriv,
    (hasDerivAt_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single _ 1) hm).deriv,
    ← fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g (Pi.single _ 1) hk,
    ← fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g (Pi.single _ 1) hm]
  exact sum_fderiv_eigenvalues₀_add_gaussianEnsemble_single_mul_of_eq_one hβ hA hA_symm g hk hm

/-- Deterministic coordinate-gradient inner-product identity (1D coordinate-ray form) at simple
sorted eigenvalues `λₖ, λₘ` of `A + gaussianEnsemble β n g` for Hermitian `A` under
`(β = 1 ∧ A.IsSymm) ∨ β = 2`, giving `(2 / (β * n)) * δₖₘ` (the quadratic-variation coefficient in
Anderson–Guionnet–Zeitouni Theorem 4.3.2). -/
theorem sum_deriv_eigenvalues₀_add_gaussianEnsemble_mul {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (hβ : (β = 1 ∧ A.IsSymm) ∨ β = 2) (g : Fin n × Fin n → ℝ)
    {k m : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k)
    (hm : ∀ j ≠ m, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ m) :
    ∑ p : Fin n × Fin n,
        deriv (fun t : ℝ ↦
          (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ k) 0 *
        deriv (fun t : ℝ ↦
          (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ m) 0 =
      if k = m then 2 / ((β : ℝ) * n) else 0 := by
  simp_rw [(hasDerivAt_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single _ 1) hk).deriv,
    (hasDerivAt_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single _ 1) hm).deriv,
    ← fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g (Pi.single _ 1) hk,
    ← fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g (Pi.single _ 1) hm]
  exact sum_fderiv_eigenvalues₀_add_gaussianEnsemble_single_mul hA hβ g hk hm

/-- Deterministic coordinate half-Laplacian identity (1D coordinate-ray form) at a simple sorted
eigenvalue `λₖ` of `A + gaussianEnsemble β n g` for Hermitian `A` assuming `β ≠ 1 ∨ A.IsSymm`:
`(1 / 2) * ∑ p, (d²/dt²)|₀ λₖ(A + gaussianEnsemble β n (g + t • eₚ)) = n⁻¹ * ∑ j ≠ k, (λₖ - λⱼ)⁻¹`
(supplying the repulsion drift term in Anderson–Guionnet–Zeitouni Theorem 4.3.2 and Lemma 4.3.4). -/
theorem half_sum_iteratedDeriv_two_eigenvalues₀_add_gaussianEnsemble {β n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hβ : β ≠ 1 ∨ A.IsSymm)
    (g : Fin n × Fin n → ℝ) {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    (2 : ℝ)⁻¹ * ∑ p : Fin n × Fin n,
        iteratedDeriv 2 (fun t : ℝ ↦
          (hA.add (isHermitian_gaussianEnsemble β n (g + t • Pi.single p 1))).eigenvalues₀ k) 0 =
      (n : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase k,
        ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k -
          (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j)⁻¹ := by
  simp_rw [iteratedDeriv_two_eigenvalues₀_add_gaussianEnsemble hA g (Pi.single _ 1) hk,
    ← fderiv_fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g (Pi.single _ 1) (Pi.single _ 1) hk]
  exact half_sum_fderiv_fderiv_eigenvalues₀_add_gaussianEnsemble_single hA hβ g hk

end Probability

end TauCeti
