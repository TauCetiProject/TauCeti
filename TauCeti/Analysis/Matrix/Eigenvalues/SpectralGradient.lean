/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.SpectralFunction.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic
import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic

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

For a symmetric `f` the gradient does not depend on the eigenbasis: the weights `∂ᵢ f(λ(A))` agree
on each eigenvalue cluster, so `∇F_f(A)` acts on every eigenvector for `λₖ(A)` as multiplication by
`∂ₖ f(λ(A))`, and `∇F_f(A) = V diag(∂ f(λ(A))) V*` for every unitary `V` diagonalizing `A` with the
eigenvalues in any order. Consequently `∇F_f(U A U*) = U ∇F_f(A) U*` for unitary `U`. The gradient
of the trace is the identity, that of `tr(A²)` is `2A`, and that of the determinant is the
adjugate `adj A`, which is `det(A) A⁻¹` at an invertible `A`.

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
* `Matrix.IsHermitian.spectralGradient_mulVec_of_mulVec_eq`,
  `Matrix.IsHermitian.spectralGradient_eq_mul_diagonal_mul_star`: for a symmetric `f`, the gradient
  computed in any eigenbasis.
* `Matrix.IsHermitian.spectralGradient_mul_mul_star`: unitary equivariance
  `∇F_f(U A U*) = U ∇F_f(A) U*`.
* `Matrix.IsHermitian.commute_spectralGradient`: `∇F_f(A)` commutes with `A`.
* `Matrix.IsHermitian.spectralGradient_sum`, `Matrix.IsHermitian.spectralGradient_sum_sq`,
  `Matrix.IsHermitian.spectralGradient_prod`: the gradients of `tr`, `tr(A²)` and `det`, the
  last being the adjugate; `Matrix.IsHermitian.spectralGradient_prod_eq_of_mul_eq` identifies the
  gradient of `det` at an invertible `A` with any `B` satisfying `B A = det A • 1`.
* `Matrix.IsHermitian.spectralGradient_comp`, `Matrix.IsHermitian.spectralGradient_log`: the
  chain rule `∇F_{g ∘ f}(A) = g'(f(λ(A))) ∇F_f(A)`, and `∇ log F_f = ∇F_f / F_f`.

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
  -- Expand the direction `λ(A)` in the standard basis of `ℝⁿ`.
  conv_rhs => arg 2; rw [← (Pi.basisFun ℝ _).sum_repr hA.eigenvalues₀]
  simp only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply, smul_eq_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [spectralGradientWeights_equivOfCardEq, ← hA.eigenvalues_eq,
    hA.eigenvalues_apply_equivOfCardEq, mul_comm]

/-- **Euler's identity for spectral functions.** If `f` is differentiable at `λ(A)` and positively
homogeneous of degree one along `λ(A)`, that is `f(t • λ(A)) = t f(λ(A))` for `t > 0`, then
`Re tr(∇F_f(A) A) = f(λ(A))`. -/
theorem re_trace_spectralGradient_mul_self_of_homogeneous (hA : A.IsHermitian)
    {f : (Fin (Fintype.card ι) → ℝ) → ℝ} (hfd : DifferentiableAt ℝ f hA.eigenvalues₀)
    (hhom : ∀ t : ℝ, 0 < t → f (t • hA.eigenvalues₀) = t * f hA.eigenvalues₀) :
    RCLike.re (hA.spectralGradient f * A).trace = f hA.eigenvalues₀ := by
  rw [re_trace_spectralGradient_mul_self]
  simpa using HasFDerivAt.apply_self_eq_smul_of_eventuallyEq hfd.hasFDerivAt (hasDerivAt_id (1 : ℝ))
    ((eventually_gt_nhds one_pos).mono fun t ht ↦ by simpa [smul_eq_mul] using hhom t ht)

/-! ### Basis independence and unitary equivariance -/

/-- For a symmetric `f`, the weights of the gradient agree at matrix indices with equal
eigenvalues, since `∂ᵢ f(μ) = ∂ⱼ f(μ)` whenever `μᵢ = μⱼ`. -/
theorem spectralGradientWeights_eq_of_eigenvalues_eq (hA : A.IsHermitian)
    {f : (Fin (Fintype.card ι) → ℝ) → ℝ}
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ) {i j : ι}
    (h : hA.eigenvalues i = hA.eigenvalues j) :
    hA.spectralGradientWeights f i = hA.spectralGradientWeights f j :=
  TauCeti.fderiv_apply_single_eq_of_comp_swap (hf _) h 1

/-- **The gradient acts on every eigenvector by its weight.** For a symmetric `f`, if `u` is an
eigenvector of `A` for the sorted eigenvalue `λₖ(A)`, then `∇F_f(A) u = ∂ₖ f(λ(A)) u`. The vector
`u` need not be a column of the eigenvector unitary chosen by Mathlib. -/
theorem spectralGradient_mulVec_of_mulVec_eq (hA : A.IsHermitian)
    {f : (Fin (Fintype.card ι) → ℝ) → ℝ}
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ)
    {k : Fin (Fintype.card ι)} {u : ι → 𝕜} (hu : A *ᵥ u = (hA.eigenvalues₀ k : 𝕜) • u) :
    hA.spectralGradient f *ᵥ u = (fderiv ℝ f hA.eigenvalues₀ (Pi.single k 1) : 𝕜) • u := by
  set U : Matrix ι ι 𝕜 := ↑hA.eigenvectorUnitary
  -- In the eigen-coordinates `U* u`, the diagonal of weights acts as the scalar `∂ₖ f(λ(A))`.
  have hD : diagonal (fun i ↦ (hA.spectralGradientWeights f i : 𝕜)) *ᵥ (star U *ᵥ u) =
      (fderiv ℝ f hA.eigenvalues₀ (Pi.single k 1) : 𝕜) • (star U *ᵥ u) := by
    funext i
    rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hi : hA.eigenvalues i = hA.eigenvalues₀ k
    · rw [hA.spectralGradientWeights_eq_of_eigenvalues_eq hf
        (hi.trans (hA.eigenvalues_apply_equivOfCardEq k).symm),
        spectralGradientWeights_equivOfCardEq]
    · rw [hA.star_eigenvectorUnitary_mulVec_apply_eq_zero hu hi, mul_zero, mul_zero]
  rw [spectralGradient_def, ← mulVec_mulVec, ← mulVec_mulVec, hD, mulVec_smul, mulVec_mulVec,
    Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.property, one_mulVec]

/-- **The gradient in any eigenbasis.** For a symmetric `f`, if the columns of `V` are eigenvectors
of `A`, the column `i` for the sorted eigenvalue `λ_{σ i}(A)`, then
`∇F_f(A) V = V diag(∂_{σ i} f(λ(A)))`. -/
theorem spectralGradient_mul_eq_mul_diagonal (hA : A.IsHermitian)
    {f : (Fin (Fintype.card ι) → ℝ) → ℝ}
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ)
    {V : Matrix ι ι 𝕜} (σ : ι → Fin (Fintype.card ι))
    (hV : A * V = V * diagonal (fun i ↦ (hA.eigenvalues₀ (σ i) : 𝕜))) :
    hA.spectralGradient f * V =
      V * diagonal (fun i ↦ (fderiv ℝ f hA.eigenvalues₀ (Pi.single (σ i) 1) : 𝕜)) := by
  ext a i
  -- The column `i` of `V` is an eigenvector for `λ_{σ i}(A)`.
  have hcol : A *ᵥ V.col i = (hA.eigenvalues₀ (σ i) : 𝕜) • V.col i := by
    rw [← col_mul_eq_mulVec_col, hV]
    ext b
    simp [Matrix.mul_diagonal, mul_comm]
  rw [Matrix.mul_diagonal, ← col_apply (hA.spectralGradient f * V), col_mul_eq_mulVec_col,
    hA.spectralGradient_mulVec_of_mulVec_eq hf hcol, Pi.smul_apply, col_apply, smul_eq_mul,
    mul_comm]

/-- **The gradient does not depend on the eigenbasis.** For a symmetric `f` and any unitary `V`
with `A = V diag(λ_{σ i}(A)) V*`, the gradient is `∇F_f(A) = V diag(∂_{σ i} f(λ(A))) V*`. -/
theorem spectralGradient_eq_mul_diagonal_mul_star (hA : A.IsHermitian)
    {f : (Fin (Fintype.card ι) → ℝ) → ℝ}
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ)
    {V : Matrix ι ι 𝕜} (hVu : V ∈ unitaryGroup ι 𝕜) (σ : ι → Fin (Fintype.card ι))
    (hAV : A = V * diagonal (fun i ↦ (hA.eigenvalues₀ (σ i) : 𝕜)) * star V) :
    hA.spectralGradient f =
      V * diagonal (fun i ↦ (fderiv ℝ f hA.eigenvalues₀ (Pi.single (σ i) 1) : 𝕜)) * star V := by
  have hV : A * V = V * diagonal (fun i ↦ (hA.eigenvalues₀ (σ i) : 𝕜)) := by
    conv_lhs => rw [hAV]
    rw [Matrix.mul_assoc, Unitary.star_mul_self_of_mem hVu, Matrix.mul_one]
  rw [← hA.spectralGradient_mul_eq_mul_diagonal hf σ hV, Matrix.mul_assoc,
    Unitary.mul_star_self_of_mem hVu, Matrix.mul_one]

/-- **Unitary equivariance of the gradient.** For a symmetric `f` and a unitary `U`,
`∇F_f(U A U*) = U ∇F_f(A) U*`. -/
theorem spectralGradient_mul_mul_star (hA : A.IsHermitian) {f : (Fin (Fintype.card ι) → ℝ) → ℝ}
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), ∀ μ, f (μ ∘ σ) = f μ)
    {U : Matrix ι ι 𝕜} (hU : U ∈ unitaryGroup ι 𝕜) (hUA : (U * A * star U).IsHermitian) :
    hUA.spectralGradient f = U * hA.spectralGradient f * star U := by
  have he : hUA.eigenvalues₀ = hA.eigenvalues₀ := hA.eigenvalues₀_mul_mul_star hU hUA
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  set W : Matrix ι ι 𝕜 := ↑hA.eigenvectorUnitary
  have hW : U * W ∈ unitaryGroup ι 𝕜 := mul_mem hU hA.eigenvectorUnitary.property
  have hAW : A = W * diagonal (fun i ↦ (hA.eigenvalues₀ (e.symm i) : 𝕜)) * star W := by
    have hev : (RCLike.ofReal ∘ hA.eigenvalues : ι → 𝕜) =
        fun i ↦ (hA.eigenvalues₀ (e.symm i) : 𝕜) := by
      funext i
      rw [Function.comp_apply, hA.eigenvalues₀_equivOfCardEq_symm]
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply, hev]
  have hUAW : U * A * star U =
      (U * W) * diagonal (fun i ↦ (hUA.eigenvalues₀ (e.symm i) : 𝕜)) * star (U * W) := by
    rw [he]
    conv_lhs => rw [hAW]
    simp only [star_mul, Matrix.mul_assoc]
  rw [hUA.spectralGradient_eq_mul_diagonal_mul_star hf hW e.symm hUAW, spectralGradient_def, he]
  simp only [spectralGradientWeights_def, star_mul, Matrix.mul_assoc, e, W]

/-- The gradient of a spectral function commutes with the matrix. -/
theorem commute_spectralGradient (hA : A.IsHermitian) (f : (Fin (Fintype.card ι) → ℝ) → ℝ) :
    Commute (hA.spectralGradient f) A := by
  -- Both are conjugates of diagonal matrices by the same unitary.
  have h := (commute_diagonal (fun i ↦ (hA.spectralGradientWeights f i : 𝕜))
    (RCLike.ofReal ∘ hA.eigenvalues)).map (Unitary.conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary)
  rwa [← hA.spectral_theorem, Unitary.conjStarAlgAut_apply, ← spectralGradient_def] at h

/-! ### The trace, the sum of squares and the determinant -/

/-- **The gradient of the trace** is the identity: for `f = σ₁`, `∇F_f(A) = 1`. -/
@[simp]
theorem spectralGradient_sum (hA : A.IsHermitian) :
    hA.spectralGradient (fun μ ↦ ∑ k, μ k) = 1 := by
  have hd : ∀ μ : Fin (Fintype.card ι) → ℝ, HasFDerivAt (fun μ ↦ ∑ k, μ k)
      (∑ k, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Fintype.card ι) ↦ ℝ) k) μ :=
    fun μ ↦ HasFDerivAt.fun_sum fun k _ ↦ hasFDerivAt_apply k μ
  have hw : ∀ i, (hA.spectralGradientWeights (fun μ ↦ ∑ k, μ k) i : 𝕜) = 1 := fun i ↦ by
    rw [spectralGradientWeights_def, (hd _).fderiv]
    simp
  rw [spectralGradient_def]
  simp only [hw, diagonal_one, Matrix.mul_one,
    Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.property]

/-- **The gradient of `tr(A²)`**: for `f(μ) = ∑ₖ μₖ²`, `∇F_f(A) = 2 A`. -/
@[simp]
theorem spectralGradient_sum_sq (hA : A.IsHermitian) :
    hA.spectralGradient (fun μ ↦ ∑ k, μ k ^ 2) = (2 : 𝕜) • A := by
  have hd : ∀ μ : Fin (Fintype.card ι) → ℝ, HasFDerivAt (fun μ ↦ ∑ k, μ k ^ 2)
      (∑ k, (2 * μ k) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Fintype.card ι) ↦ ℝ) k) μ :=
    fun μ ↦ (HasFDerivAt.fun_sum fun k _ ↦ HasFDerivAt.pow (hasFDerivAt_apply k μ) 2).congr_fderiv
      (by simp)
  have hw : ∀ i, (hA.spectralGradientWeights (fun μ ↦ ∑ k, μ k ^ 2) i : 𝕜) =
      2 * (hA.eigenvalues i : 𝕜) := fun i ↦ by
    rw [spectralGradientWeights_def, (hd _).fderiv]
    simp [hA.eigenvalues₀_equivOfCardEq_symm, Pi.single_apply, map_ofNat]
  rw [spectralGradient_def]
  conv_rhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  simp only [hw]
  have h2 : (diagonal fun i ↦ 2 * (hA.eigenvalues i : 𝕜)) =
      (2 : 𝕜) • diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    rw [← diagonal_smul]
    exact congrArg diagonal (funext fun i ↦ by simp)
  rw [h2, Matrix.mul_smul, Matrix.smul_mul]

/-- **The gradient of the determinant** is the adjugate: for `f = σₙ`, `∇F_f(A) = adj A`. The
weights `∏_{j ≠ i} λⱼ(A)` are the diagonal of the adjugate of `diag(λ(A))`, and the adjugate
commutes with unitary conjugation. -/
@[simp]
theorem spectralGradient_prod (hA : A.IsHermitian) :
    hA.spectralGradient (fun μ ↦ ∏ k, μ k) = A.adjugate := by
  have hw : (fun i ↦ (hA.spectralGradientWeights (fun μ ↦ ∏ k, μ k) i : 𝕜)) =
      fun i ↦ ∏ j ∈ univ.erase i, (RCLike.ofReal ∘ hA.eigenvalues) j := by
    funext i
    rw [spectralGradientWeights_def, TauCeti.fderiv_prod_apply_single, RCLike.ofReal_prod]
    -- Reindex the product from sorted indices to matrix indices.
    refine prod_equiv (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)))
      (by simp [Equiv.eq_symm_apply]) fun j _ ↦ ?_
    rw [Function.comp_apply, hA.eigenvalues_apply_equivOfCardEq]
  rw [spectralGradient_def, hw, ← adjugate_diagonal]
  conv_rhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply,
    adjugate_mul_mul_of_mul_eq_one (Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.property)]

/-- The gradient of the determinant times the matrix is `det A • 1`: for `f = σₙ`,
`∇F_f(A) A = det A • 1`. -/
theorem spectralGradient_prod_mul_self (hA : A.IsHermitian) :
    hA.spectralGradient (fun μ ↦ ∏ k, μ k) * A = A.det • 1 := by
  rw [spectralGradient_prod, adjugate_mul]

/-- At an invertible Hermitian `A`, the gradient of the determinant (`f = σₙ`) is the unique
matrix `B` with `B A = det A • 1`. -/
theorem spectralGradient_prod_eq_of_mul_eq (hA : A.IsHermitian) (h : IsUnit A.det)
    {B : Matrix ι ι 𝕜} (hB : B * A = A.det • 1) :
    hA.spectralGradient (fun μ ↦ ∏ k, μ k) = B :=
  ((isUnit_iff_isUnit_det A).2 h).mul_left_inj.1 (hA.spectralGradient_prod_mul_self.trans hB.symm)

/-- At an invertible Hermitian `A`, the gradient of the determinant is `det A • A⁻¹`. -/
theorem spectralGradient_prod_eq_det_smul_inv (hA : A.IsHermitian) (h : IsUnit A.det) :
    hA.spectralGradient (fun μ ↦ ∏ k, μ k) = A.det • A⁻¹ :=
  hA.spectralGradient_prod_eq_of_mul_eq h (by rw [Matrix.smul_mul, nonsing_inv_mul A h])

/-! ### Composition with a real function -/

/-- **The chain rule for the gradient**: if `f` is differentiable at `λ(A)` and `g : ℝ → ℝ` is
differentiable at `f(λ(A))`, then `∇F_{g ∘ f}(A) = g'(f(λ(A))) ∇F_f(A)`. -/
theorem spectralGradient_comp (hA : A.IsHermitian) {f : (Fin (Fintype.card ι) → ℝ) → ℝ}
    {g : ℝ → ℝ} (hg : DifferentiableAt ℝ g (f hA.eigenvalues₀))
    (hf : DifferentiableAt ℝ f hA.eigenvalues₀) :
    hA.spectralGradient (fun μ ↦ g (f μ)) =
      ((deriv g (f hA.eigenvalues₀) : ℝ) : 𝕜) • hA.spectralGradient f := by
  have hd := (hg.hasDerivAt.comp_hasFDerivAt hA.eigenvalues₀ hf.hasFDerivAt).fderiv
  rw [Function.comp_def] at hd
  have hw : (fun i ↦ (hA.spectralGradientWeights (fun μ ↦ g (f μ)) i : 𝕜)) =
      ((deriv g (f hA.eigenvalues₀) : ℝ) : 𝕜) • fun i ↦ (hA.spectralGradientWeights f i : 𝕜) := by
    funext i
    simp only [spectralGradientWeights_def, Pi.smul_apply, smul_eq_mul]
    rw [hd, smul_apply, smul_eq_mul, RCLike.ofReal_mul]
  rw [spectralGradient_def, spectralGradient_def, hw, diagonal_smul, Matrix.mul_smul,
    Matrix.smul_mul]

/-- **The gradient of `log F_f`** is `∇F_f / F_f`: if `f` is differentiable at `λ(A)`, then
`∇F_{log ∘ f}(A) = f(λ(A))⁻¹ ∇F_f(A)`. Where `f(λ(A)) = 0` both sides vanish, with the
conventions `log 0 = 0` and `0⁻¹ = 0`. -/
theorem spectralGradient_log (hA : A.IsHermitian) {f : (Fin (Fintype.card ι) → ℝ) → ℝ}
    (hf : DifferentiableAt ℝ f hA.eigenvalues₀) :
    hA.spectralGradient (fun μ ↦ Real.log (f μ)) =
      ((f hA.eigenvalues₀)⁻¹ : 𝕜) • hA.spectralGradient f := by
  by_cases hf0 : f hA.eigenvalues₀ = 0
  · rw [spectralGradient_def]
    simp [hf0, spectralGradientWeights_def,
      TauCeti.fderiv_log_comp_eq_zero_of_continuousAt hf.continuousAt hf0]
  rw [hA.spectralGradient_comp (Real.differentiableAt_log hf0) hf, Real.deriv_log,
    RCLike.ofReal_inv]

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
