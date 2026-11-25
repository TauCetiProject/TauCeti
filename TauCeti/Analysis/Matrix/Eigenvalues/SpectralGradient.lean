/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.SpectralFunction
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.Matrix.Spectrum

/-!
# The gradient of a spectral function

For a symmetric function `f : ℝⁿ → ℝ`, the spectral function `A ↦ f(λ(A))` on Hermitian matrices,
with `λ(A)` the decreasingly sorted eigenvalue vector `Matrix.IsHermitian.eigenvalues₀`, has
derivative `H ↦ ∑ⱼ ∂ⱼ f(λ(A)) Re ⟪uⱼ, H uⱼ⟫` at `A` by Lewis's theorem
(`Matrix.fderiv_spectralFunction_selfAdjoint_apply`), for an orthonormal eigenbasis `(uⱼ)` of `A`
ordered as `λ(A)`. This file names the matrix representing that derivative under the trace
pairing, the *gradient*

`∇F_f(A) = U diag(∂₁ f(λ(A)), …, ∂ₙ f(λ(A))) U*`,

for `U` the unitary whose columns are the eigenvectors of `A`
(`Matrix.IsHermitian.spectralGradient`), and proves the identities used for fully nonlinear
equations: the derivative of the spectral function is `H ↦ Re tr(∇F_f(A) H)`, the determinant
of the gradient is `∏ᵢ ∂ᵢ f(λ(A))`, the gradient is positive definite when every `∂ᵢ f(λ(A))` is
positive, and `Re tr(∇F_f(A) A) = Df(λ(A)) λ(A)`, which is `f(λ(A))` when `f` is positively
homogeneous of degree one (Euler's identity).

## Main definitions

* `Matrix.IsHermitian.spectralGradient`: the gradient `∇F_f(A)` of the spectral function of `f`
  at a Hermitian matrix `A`.

## Main results

* `Matrix.fderiv_spectralFunction_selfAdjoint_apply_eq_re_trace`: the derivative of the spectral
  function at `A` in the direction `H` is `Re tr(∇F_f(A) H)`.
* `Matrix.IsHermitian.det_spectralGradient`: `det ∇F_f(A) = ∏ᵢ ∂ᵢ f(λ(A))`.
* `Matrix.IsHermitian.posDef_spectralGradient`: if every `∂ᵢ f(λ(A))` is positive, then
  `∇F_f(A)` is positive definite.
* `Matrix.IsHermitian.re_trace_spectralGradient_mul_self_of_homogeneous`: Euler's identity
  `Re tr(∇F_f(A) A) = f(λ(A))` for `f` positively homogeneous of degree one.

## References

* A. S. Lewis, *Derivatives of spectral functions*, Math. Oper. Res. **21** (1996), 576–588,
  Theorem 1.1.
-/

public section

noncomputable section

open Finset Topology
open scoped ComplexOrder

namespace Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] {A : Matrix ι ι 𝕜}

namespace IsHermitian

/-- The partial derivatives `∂ᵢ f(λ(A))` of `f` at the sorted eigenvalue vector of `A`, indexed by
the matrix index `ι` through the canonical equivalence `Fin n ≃ ι`, as are Mathlib's
`Matrix.IsHermitian.eigenvalues` and `Matrix.IsHermitian.eigenvectorBasis`. -/
def spectralGradientWeights (hA : A.IsHermitian) (f : (Fin (Fintype.card ι) → ℝ) → ℝ) (i : ι) :
    ℝ :=
  fderiv ℝ f hA.eigenvalues₀
    (Pi.single ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm i) 1)

/-- Unfold `Matrix.IsHermitian.spectralGradientWeights`. -/
theorem spectralGradientWeights_def (hA : A.IsHermitian) (f : (Fin (Fintype.card ι) → ℝ) → ℝ)
    (i : ι) : hA.spectralGradientWeights f i = fderiv ℝ f hA.eigenvalues₀
      (Pi.single ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm i) 1) :=
  (rfl)

/-- The weight at the matrix index corresponding to a sorted index `k` is `∂ₖ f(λ(A))`. -/
@[simp]
theorem spectralGradientWeights_equivOfCardEq (hA : A.IsHermitian)
    (f : (Fin (Fintype.card ι) → ℝ) → ℝ) (k : Fin (Fintype.card ι)) :
    hA.spectralGradientWeights f (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) k) =
      fderiv ℝ f hA.eigenvalues₀ (Pi.single k 1) := by
  rw [spectralGradientWeights_def, Equiv.symm_apply_apply]

/-- **The gradient of a spectral function.** For a Hermitian matrix `A` and `f : ℝⁿ → ℝ`, the
matrix `∇F_f(A) = U diag(∂ᵢ f(λ(A))) U*`, where `U` is the unitary `eigenvectorUnitary` whose
columns are the eigenvectors of `A`, listed as Mathlib's `Matrix.IsHermitian.eigenvalues`. When `f`
is symmetric and differentiable at `λ(A)`, it represents the derivative of the spectral function
`B ↦ f(λ(B))` at `A` under the pairing `(G, H) ↦ Re tr(G H)`
(`Matrix.fderiv_spectralFunction_selfAdjoint_apply_eq_re_trace`). -/
def spectralGradient (hA : A.IsHermitian) (f : (Fin (Fintype.card ι) → ℝ) → ℝ) :
    Matrix ι ι 𝕜 :=
  (hA.eigenvectorUnitary : Matrix ι ι 𝕜) *
    diagonal (fun i ↦ (hA.spectralGradientWeights f i : 𝕜)) *
      star (hA.eigenvectorUnitary : Matrix ι ι 𝕜)

/-- Unfold `Matrix.IsHermitian.spectralGradient`. -/
theorem spectralGradient_def (hA : A.IsHermitian) (f : (Fin (Fintype.card ι) → ℝ) → ℝ) :
    hA.spectralGradient f = (hA.eigenvectorUnitary : Matrix ι ι 𝕜) *
      diagonal (fun i ↦ (hA.spectralGradientWeights f i : 𝕜)) *
        star (hA.eigenvectorUnitary : Matrix ι ι 𝕜) :=
  (rfl)

/-- The gradient of a spectral function acts on the eigenvector `uᵢ` of `A` as multiplication by
the weight `∂ᵢ f(λ(A))`. -/
@[simp]
theorem spectralGradient_mulVec_eigenvectorBasis (hA : A.IsHermitian)
    (f : (Fin (Fintype.card ι) → ℝ) → ℝ) (i : ι) :
    hA.spectralGradient f *ᵥ ⇑(hA.eigenvectorBasis i) =
      (hA.spectralGradientWeights f i : 𝕜) • ⇑(hA.eigenvectorBasis i) := by
  rw [spectralGradient_def, ← mulVec_mulVec, ← mulVec_mulVec, star_eigenvectorUnitary_mulVec,
    diagonal_mulVec_single, ← smul_eq_mul, Pi.single_smul', mulVec_smul, eigenvectorUnitary_mulVec]

/-- The gradient of a spectral function is Hermitian. -/
theorem isHermitian_spectralGradient (hA : A.IsHermitian) (f : (Fin (Fintype.card ι) → ℝ) → ℝ) :
    (hA.spectralGradient f).IsHermitian := by
  rw [spectralGradient_def, star_eq_conjTranspose]
  exact isHermitian_mul_mul_conjTranspose _
    (isHermitian_diagonal_of_self_adjoint _ (funext fun _ ↦ RCLike.conj_ofReal _))

/-- The trace pairing of the gradient with a matrix `H` is the weighted sum of the diagonal
entries `Re ⟪uᵢ, H uᵢ⟫` of `H` in the eigenbasis `(uᵢ)` of `A`. -/
theorem re_trace_spectralGradient_mul (hA : A.IsHermitian) (f : (Fin (Fintype.card ι) → ℝ) → ℝ)
    (H : Matrix ι ι 𝕜) :
    RCLike.re (hA.spectralGradient f * H).trace = ∑ i, hA.spectralGradientWeights f i *
      RCLike.re (star ⇑(hA.eigenvectorBasis i) ⬝ᵥ (H *ᵥ ⇑(hA.eigenvectorBasis i))) := by
  rw [spectralGradient_def, Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc,
    trace, map_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [diag_apply, diagonal_mul, ← RCLike.re_ofReal_mul]
  congr 1
  simp only [Matrix.mul_apply, star_apply, eigenvectorUnitary_apply, dotProduct, mulVec,
    sum_mul, mul_sum, Pi.star_apply]
  rw [sum_comm]
  exact sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ by ring

/-- **The determinant of the gradient** of a spectral function is `∏ᵢ ∂ᵢ f(λ(A))`. -/
theorem det_spectralGradient (hA : A.IsHermitian) (f : (Fin (Fintype.card ι) → ℝ) → ℝ) :
    (hA.spectralGradient f).det = ((∏ k, fderiv ℝ f hA.eigenvalues₀ (Pi.single k 1) : ℝ) : 𝕜) := by
  set U : Matrix ι ι 𝕜 := ↑hA.eigenvectorUnitary
  have hU : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  rw [spectralGradient_def, det_mul_right_comm, hU, Matrix.one_mul, det_diagonal,
    RCLike.ofReal_prod,
    ← Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)))]
  simp only [spectralGradientWeights_equivOfCardEq]

/-- **The gradient of an elliptic spectral function is positive definite.** If every partial
derivative `∂ᵢ f(λ(A))` is positive, then `∇F_f(A)` is positive definite. -/
theorem posDef_spectralGradient (hA : A.IsHermitian) {f : (Fin (Fintype.card ι) → ℝ) → ℝ}
    (hpos : ∀ k, 0 < fderiv ℝ f hA.eigenvalues₀ (Pi.single k 1)) :
    (hA.spectralGradient f).PosDef := by
  rw [spectralGradient_def, IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe,
    posDef_diagonal_iff]
  exact fun i ↦ RCLike.ofReal_pos.2 (hpos _)

/-- The trace pairing of the gradient with `A` itself is `Df(λ(A)) λ(A)`. -/
theorem re_trace_spectralGradient_mul_self (hA : A.IsHermitian)
    (f : (Fin (Fintype.card ι) → ℝ) → ℝ) :
    RCLike.re (hA.spectralGradient f * A).trace = fderiv ℝ f hA.eigenvalues₀ hA.eigenvalues₀ := by
  rw [re_trace_spectralGradient_mul,
    ← Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)))]
  rw [show fderiv ℝ f hA.eigenvalues₀ hA.eigenvalues₀ =
      ∑ k, fderiv ℝ f hA.eigenvalues₀ (Pi.single k (hA.eigenvalues₀ k)) by
    rw [← map_sum, univ_sum_single]]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [spectralGradientWeights_equivOfCardEq, ← hA.eigenvalues_eq,
    hA.eigenvalues_apply_equivOfCardEq,
    show (Pi.single k (hA.eigenvalues₀ k) : Fin (Fintype.card ι) → ℝ) =
      hA.eigenvalues₀ k • Pi.single k 1 by ext j; simp [Pi.single_apply],
    map_smul, smul_eq_mul, mul_comm]

/-- **Euler's identity for spectral functions.** If `f` is differentiable at `λ(A)` and positively
homogeneous of degree one along `λ(A)`, that is `f(t • λ(A)) = t f(λ(A))` for `t > 0`, then
`Re tr(∇F_f(A) A) = f(λ(A))`. -/
theorem re_trace_spectralGradient_mul_self_of_homogeneous (hA : A.IsHermitian)
    {f : (Fin (Fintype.card ι) → ℝ) → ℝ} (hfd : DifferentiableAt ℝ f hA.eigenvalues₀)
    (hhom : ∀ t : ℝ, 0 < t → f (t • hA.eigenvalues₀) = t * f hA.eigenvalues₀) :
    RCLike.re (hA.spectralGradient f * A).trace = f hA.eigenvalues₀ := by
  rw [re_trace_spectralGradient_mul_self]
  simpa using HasFDerivAt.apply_self_eq_smul_of_eventuallyEq hfd.hasFDerivAt (hasDerivAt_id (1 : ℝ))
    (Filter.mem_of_superset (Ioi_mem_nhds one_pos) fun t ht ↦ by
      simpa [smul_eq_mul] using hhom t ht)

end IsHermitian

/-- **The gradient of a spectral function represents its derivative** (Lewis's theorem,
[Lewis 1996, Theorem 1.1]). If `f` is symmetric and differentiable at `λ(A)`, the derivative of
the spectral function `B ↦ f(λ(B))` on Hermitian matrices at `A` in the direction `H` is
`Re tr(∇F_f(A) H)`. -/
theorem fderiv_spectralFunction_selfAdjoint_apply_eq_re_trace {f : (Fin (Fintype.card ι) → ℝ) → ℝ}
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ)
    (A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜))
    (hfA : DifferentiableAt ℝ f A.property.isHermitian.eigenvalues₀)
    (H : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜)) :
    fderiv ℝ (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      f B.property.isHermitian.eigenvalues₀) A H =
      RCLike.re (A.property.isHermitian.spectralGradient f * (H : Matrix ι ι 𝕜)).trace := by
  set hA : (A : Matrix ι ι 𝕜).IsHermitian := A.property.isHermitian
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  rw [fderiv_spectralFunction_selfAdjoint_apply hf A hfA _
      hA.mulVec_eigenvectorBasis_reindex_eq_eigenvalues₀_smul, hA.re_trace_spectralGradient_mul,
    ← Equiv.sum_comp e]
  simp only [OrthonormalBasis.reindex_apply, Equiv.symm_symm, e,
    IsHermitian.spectralGradientWeights_equivOfCardEq]

end Matrix
