/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.Derivative
public import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Matrix.Eigenvalues.Basic
import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Completeness
import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Covariance

/-!
# Coordinate variation of sorted eigenvalues for Gaussian ensembles

Combining Hadamard's projector-trace first and second eigenvalue variation formulas
(`TauCeti.Analysis.Matrix.Eigenvalues.Derivative`) with the coordinate parameterization of
`gaussianEnsemble β n` (`TauCeti.Probability.RandomMatrices.GaussianEnsemble.Basic`) and its trace
covariance and completeness identities
(`TauCeti.Probability.RandomMatrices.GaussianEnsemble.Covariance` and
`TauCeti.Probability.RandomMatrices.GaussianEnsemble.Completeness`), we compute multivariable
Fréchet and 1D coordinate-ray derivatives at simple sorted eigenvalues of
`A + gaussianEnsemble β n g`. These identities supply the `(2 / (β n)) δₖₘ` diffusion bracket and
`n⁻¹ ∑_{j ≠ k} (λₖ - λⱼ)⁻¹` repulsion drift coefficients for GOE (`β = 1`, symmetric `A`) and GUE
(`β = 2`, Hermitian `A`) matrix Brownian motions (Anderson–Guionnet–Zeitouni Theorem 4.3.2).

To state or use the normed calculus declarations in this file,
`open scoped Matrix.Norms.L2Operator` and enable
`attribute [local instance] Matrix.l2OpNormedAlgebraReal`.

## Main results

* `TauCeti.Probability.contDiffAt_eigenvalues₀_add_gaussianEnsemble`,
  `TauCeti.Probability.hasStrictFDerivAt_eigenvalues₀_add_gaussianEnsemble`,
  `TauCeti.Probability.fderiv_eigenvalues₀_add_gaussianEnsemble_apply`, and
  `TauCeti.Probability.fderiv_fderiv_eigenvalues₀_add_gaussianEnsemble_apply`.
* `TauCeti.Probability.sum_fderiv_eigenvalues₀_add_gaussianEnsemble_single_mul` and
  `TauCeti.Probability.half_sum_fderiv_fderiv_eigenvalues₀_add_gaussianEnsemble_single`.
* `TauCeti.Probability.hasDerivAt_eigenvalues₀_add_gaussianEnsemble`,
  `TauCeti.Probability.deriv_eigenvalues₀_add_gaussianEnsemble_eq_fderiv`, and
  `TauCeti.Probability.iteratedDeriv_two_eigenvalues₀_add_gaussianEnsemble`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices* (2010), §4.3.1.
* T. Tao, *Topics in Random Matrix Theory*, AMS (2012), §1.3.4 and §3.1.
-/

public section

noncomputable section

open Matrix Topology
open scoped ContDiff Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal

namespace TauCeti.Probability

private def shiftEnsembleSelfAdjoint (β n : ℕ) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (g' : Fin n × Fin n → ℝ) : selfAdjoint (Matrix (Fin n) (Fin n) ℂ) :=
  ⟨A, hA.isSelfAdjoint⟩ + gaussianEnsembleSelfAdjointCLM β n g'

@[simp] private theorem coe_shiftEnsembleSelfAdjoint (β n : ℕ) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (g' : Fin n × Fin n → ℝ) :
    (shiftEnsembleSelfAdjoint β n hA g' : Matrix (Fin n) (Fin n) ℂ) =
      A + gaussianEnsemble β n g' := by simp [shiftEnsembleSelfAdjoint]

variable {β n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}

@[simp] private theorem shiftEnsembleSelfAdjoint_eigenvalues₀ (hA : A.IsHermitian)
    (g' : Fin n × Fin n → ℝ) :
    (shiftEnsembleSelfAdjoint β n hA g').property.isHermitian.eigenvalues₀ =
      (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ :=
  IsHermitian.eigenvalues₀_congr (by simp)
    (shiftEnsembleSelfAdjoint β n hA g').property.isHermitian
    (hA.add (isHermitian_gaussianEnsemble β n g'))

@[simp] private theorem shiftEnsembleSelfAdjoint_eigenprojector₀ (hA : A.IsHermitian)
    (g' : Fin n × Fin n → ℝ) :
    (shiftEnsembleSelfAdjoint β n hA g').property.isHermitian.eigenprojector₀ =
      (hA.add (isHermitian_gaussianEnsemble β n g')).eigenprojector₀ :=
  (shiftEnsembleSelfAdjoint β n hA g').property.isHermitian.eigenprojector₀_congr
    (hA.add (isHermitian_gaussianEnsemble β n g')) (by simp)

private theorem eigenvalues₀_add_gaussianEnsemble_comp_eq (hA : A.IsHermitian)
    (k : Fin (Fintype.card (Fin n))) :
    (fun g' : Fin n × Fin n → ℝ ↦ (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k) =
      (fun X : selfAdjoint (Matrix (Fin n) (Fin n) ℂ) ↦ X.property.isHermitian.eigenvalues₀ k) ∘
        shiftEnsembleSelfAdjoint β n hA := funext fun _ ↦ by simp

/-- At any `g` where `λₖ(A + gaussianEnsemble β n g)` is simple,
`g' ↦ (A + gaussianEnsemble β n g').eigenvalues₀ k` is `C^r` for every `r : ℕ∞ω`. -/
theorem contDiffAt_eigenvalues₀_add_gaussianEnsemble {r : ℕ∞ω} (hA : A.IsHermitian)
    (g : Fin n × Fin n → ℝ) {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    ContDiffAt ℝ r (fun g' : Fin n × Fin n → ℝ ↦
      (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k) g := by
  rw [eigenvalues₀_add_gaussianEnsemble_comp_eq hA k]
  exact (contDiffAt_eigenvalues₀_selfAdjoint (by simpa using hk)).comp g
    (contDiff_const.add (gaussianEnsembleSelfAdjointCLM β n).contDiff).contDiffAt

/-- Strict Fréchet derivative of `g' ↦ (A + gaussianEnsemble β n g').eigenvalues₀ k` at a point `g`
where `λₖ(A + gaussianEnsemble β n g)` is simple. -/
theorem hasStrictFDerivAt_eigenvalues₀_add_gaussianEnsemble (hA : A.IsHermitian)
    (g : Fin n × Fin n → ℝ) {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    HasStrictFDerivAt
      (fun g' : Fin n × Fin n → ℝ ↦ (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k)
      ((RCLike.reCLM (K := ℂ)).comp <| (Matrix.traceCLM (Fin n) ℝ ℂ).comp <|
        (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)
          ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenprojector₀ k)).comp <|
          (selfAdjoint.subtypeL ℝ (Matrix (Fin n) (Fin n) ℂ)).comp
            (gaussianEnsembleSelfAdjointCLM β n)) g := by
  rw [eigenvalues₀_add_gaussianEnsemble_comp_eq hA k]
  refine ((hasStrictFDerivAt_eigenvalues₀_selfAdjoint (A := shiftEnsembleSelfAdjoint β n hA g)
    (by simpa using hk)).comp g ((gaussianEnsembleSelfAdjointCLM β n).hasStrictFDerivAt.const_add
      ⟨A, hA.isSelfAdjoint⟩)).congr_fderiv (by ext v; simp)

/-- Applied Fréchet derivative of `g' ↦ (A + gaussianEnsemble β n g').eigenvalues₀ k` at `g` in
direction `v`. -/
theorem fderiv_eigenvalues₀_add_gaussianEnsemble_apply (hA : A.IsHermitian)
    (g v : Fin n × Fin n → ℝ) {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    fderiv ℝ (fun g' : Fin n × Fin n → ℝ ↦
        (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k) g v =
      ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenprojector₀ k *
        gaussianEnsemble β n v).trace.re := by
  rw [(hasStrictFDerivAt_eigenvalues₀_add_gaussianEnsemble hA g hk).hasFDerivAt.fderiv]; simp

/-- Applied second Fréchet derivative of `g' ↦ (A + gaussianEnsemble β n g').eigenvalues₀ k` at `g`
in directions `v` and `w`. -/
theorem fderiv_fderiv_eigenvalues₀_add_gaussianEnsemble_apply (hA : A.IsHermitian)
    (g v w : Fin n × Fin n → ℝ) {k : Fin (Fintype.card (Fin n))}
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
      fun _ ↦ gaussianEnsembleSelfAdjointCLM β n := funext fun g' ↦
    (((gaussianEnsembleSelfAdjointCLM β n).hasStrictFDerivAt (x := g')).const_add
      _).hasFDerivAt.fderiv
  have hkΦ : ∀ j ≠ k, (shiftEnsembleSelfAdjoint β n hA g).property.isHermitian.eigenvalues₀ j ≠
      (shiftEnsembleSelfAdjoint β n hA g).property.isHermitian.eigenvalues₀ k := by simpa using hk
  rw [eigenvalues₀_add_gaussianEnsemble_comp_eq hA k,
    TauCeti.fderiv_fderiv_comp_apply (φ := shiftEnsembleSelfAdjoint β n hA)
      (contDiffAt_eigenvalues₀_selfAdjoint hkΦ)
      (contDiff_const.add (gaussianEnsembleSelfAdjointCLM β n).contDiff).contDiffAt v w, hDΦ]
  simp [fderiv_fderiv_eigenvalues₀_apply hkΦ]

private theorem re_sum_trace_mul_gaussianEnsemble_single_mul (β n : ℕ)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    ∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace.re *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace.re =
      (∑ p : Fin n × Fin n,
        (X * gaussianEnsemble β n (Pi.single p 1)).trace *
          (Y * gaussianEnsemble β n (Pi.single p 1)).trace).re := by
  have hreal {M N : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (hN : N.IsHermitian) :
      (((M * N).trace).re : ℂ) = (M * N).trace :=
    RCLike.conj_eq_iff_re.mp
      (by rw [← RCLike.star_def, ← trace_conjTranspose, conjTranspose_mul, hM.eq, hN.eq,
        trace_mul_comm])
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hE := isHermitian_gaussianEnsemble β n (Pi.single p 1)
  conv_rhs => rw [← hreal hX hE, ← hreal hY hE]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- Deterministic coordinate-gradient inner-product identity (Fréchet form) at simple sorted
eigenvalues `λₖ, λₘ` of `A + gaussianEnsemble β n g` under `(β = 1 ∧ A.IsSymm) ∨ β = 2`, giving
`(2 / (β * n)) * δₖₘ` (Anderson–Guionnet–Zeitouni Theorem 4.3.2). -/
theorem sum_fderiv_eigenvalues₀_add_gaussianEnsemble_single_mul (hA : A.IsHermitian)
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
  set hH := hA.add (isHermitian_gaussianEnsemble β n g)
  simp_rw [fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g (Pi.single _ 1) hk,
    fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g (Pi.single _ 1) hm]
  rcases hβ with ⟨rfl, hA_symm⟩ | rfl
  · have hPm_symm : (hH.eigenprojector₀ m).IsSymm :=
      hH.isSymm_eigenprojector₀ (hA_symm.add (isSymm_gaussianEnsemble_one n g)) hm
    rw [re_sum_trace_mul_gaussianEnsemble_single_mul 1 n
      (hH.isHermitian_eigenprojector₀ k) (hH.isHermitian_eigenprojector₀ m),
      sum_trace_mul_gaussianEnsemble_one_single_mul_trace_mul, ← Complex.ofReal_natCast,
      ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.add_re, hPm_symm.eq]
    by_cases hkm : k = m
    · subst hkm
      simp only [hH.eigenprojector₀_mul_self, hH.trace_eigenprojector₀, Complex.one_re, ↓reduceIte,
        Nat.cast_one, one_mul]
      ring
    · simp [hkm, hH.eigenprojector₀_mul_of_ne hkm]
  · rw [re_sum_trace_mul_gaussianEnsemble_single_mul 2 n
      (hH.isHermitian_eigenprojector₀ k) (hH.isHermitian_eigenprojector₀ m),
      sum_trace_mul_gaussianEnsemble_single_mul_trace_mul_of_ne_one (by decide),
      ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    by_cases hkm : k = m
    · subst hkm
      simp only [hH.eigenprojector₀_mul_self, hH.trace_eigenprojector₀, Complex.one_re, mul_one,
        ↓reduceIte, Nat.cast_ofNat]
      rw [div_mul_eq_div_div, div_self two_ne_zero, one_div]
    · simp [hkm, hH.eigenprojector₀_mul_of_ne hkm]

private theorem sum_re_trace_mul_gaussianEnsemble_single_sandwich (β n : ℕ)
    (P Q : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin n × Fin n, (P * gaussianEnsemble β n (Pi.single p 1) *
        Q * gaussianEnsemble β n (Pi.single p 1)).trace.re =
      (P * ∑ p : Fin n × Fin n, gaussianEnsemble β n (Pi.single p 1) *
        Q * gaussianEnsemble β n (Pi.single p 1)).trace.re := by
  rw [Matrix.mul_sum, trace_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun p _ ↦ by simp only [Matrix.mul_assoc]

/-- Deterministic coordinate half-Laplacian identity (Fréchet form) at a simple sorted eigenvalue
`λₖ` of `A + gaussianEnsemble β n g` assuming `β ≠ 1 ∨ A.IsSymm`:
`(1 / 2) * ∑ p, D²λₖ(g)(eₚ, eₚ) = n⁻¹ * ∑ j ≠ k, (λₖ - λⱼ)⁻¹`, where `eₚ = Pi.single p 1`
(Anderson–Guionnet–Zeitouni Theorem 4.3.2 and Lemma 4.3.4). -/
theorem half_sum_fderiv_fderiv_eigenvalues₀_add_gaussianEnsemble_single (hA : A.IsHermitian)
    (hβ : β ≠ 1 ∨ A.IsSymm) (g : Fin n × Fin n → ℝ) {k : Fin (Fintype.card (Fin n))}
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
  have hjk : j ≠ k := (Finset.mem_erase.mp hj).left
  suffices ∑ p : Fin n × Fin n,
      (hH.eigenprojector₀ k * gaussianEnsemble β n (Pi.single p 1) *
        hH.eigenprojector₀ j * gaussianEnsemble β n (Pi.single p 1)).trace.re = (n : ℝ)⁻¹ by
    rw [← Finset.mul_sum, this, mul_comm]
  rw [sum_re_trace_mul_gaussianEnsemble_single_sandwich]
  by_cases hβ1 : β = 1
  · subst hβ1
    have hPk_symm : (hH.eigenprojector₀ k).IsSymm := hH.isSymm_eigenprojector₀
      ((hβ.resolve_left (not_not.mpr rfl)).add (isSymm_gaussianEnsemble_one n g)) hk
    have hvanish : (hH.eigenprojector₀ k * (hH.eigenprojector₀ j)ᵀ).trace = 0 := by
      rw [← hPk_symm.eq, ← transpose_mul, trace_transpose, hH.eigenprojector₀_mul_of_ne hjk,
        trace_zero]
    rw [sum_gaussianEnsemble_one_single_mul_mul_gaussianEnsemble_one_single]
    simp [mul_add, hvanish, ← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  · rw [sum_gaussianEnsemble_single_mul_mul_gaussianEnsemble_single_of_ne_one hβ1]
    simp [← Complex.ofReal_natCast, ← Complex.ofReal_inv]

/-- Directional derivative of `t ↦ (A + gaussianEnsemble β n (g + t • v)).eigenvalues₀ k` at `0`. -/
theorem hasDerivAt_eigenvalues₀_add_gaussianEnsemble (hA : A.IsHermitian)
    (g v : Fin n × Fin n → ℝ) {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    HasDerivAt
      (fun t : ℝ ↦ (hA.add (isHermitian_gaussianEnsemble β n (g + t • v))).eigenvalues₀ k)
      ((hA.add (isHermitian_gaussianEnsemble β n g)).eigenprojector₀ k *
        gaussianEnsemble β n v).trace.re 0 :=
  ((hasStrictFDerivAt_eigenvalues₀_add_gaussianEnsemble hA g hk).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add g) (by simp)).congr_deriv (by simp)

/-- The directional ray derivative of `t ↦ (A + gaussianEnsemble β n (g + t • v)).eigenvalues₀ k`
at `t = 0` equals the applied Fréchet derivative at `g` in direction `v`. -/
theorem deriv_eigenvalues₀_add_gaussianEnsemble_eq_fderiv (hA : A.IsHermitian)
    (g v : Fin n × Fin n → ℝ) {k : Fin (Fintype.card (Fin n))}
    (hk : ∀ j ≠ k, (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ j ≠
      (hA.add (isHermitian_gaussianEnsemble β n g)).eigenvalues₀ k) :
    deriv (fun t : ℝ ↦ (hA.add (isHermitian_gaussianEnsemble β n (g + t • v))).eigenvalues₀ k) 0 =
      fderiv ℝ (fun g' : Fin n × Fin n → ℝ ↦
        (hA.add (isHermitian_gaussianEnsemble β n g')).eigenvalues₀ k) g v := by
  rw [(hasDerivAt_eigenvalues₀_add_gaussianEnsemble hA g v hk).deriv,
    fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g v hk]

/-- Directional second derivative of `t ↦ (A + gaussianEnsemble β n (g + t • v)).eigenvalues₀ k` at
`0`. -/
theorem iteratedDeriv_two_eigenvalues₀_add_gaussianEnsemble (hA : A.IsHermitian)
    (g v : Fin n × Fin n → ℝ) {k : Fin (Fintype.card (Fin n))}
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
  simpa only [Function.comp_def, TauCeti.deriv_const_add_smul,
    TauCeti.iteratedDeriv_two_const_add_smul, Pi.zero_apply, map_zero, add_zero, h0,
    fderiv_fderiv_eigenvalues₀_add_gaussianEnsemble_apply hA g v v hk] using h

end TauCeti.Probability
