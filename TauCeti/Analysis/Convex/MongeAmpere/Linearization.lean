/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Gradient
public import Mathlib.Topology.Algebra.Module.Determinant
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.FDeriv.Det
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# First variation of the classical Monge–Ampère equation

For a `C³` potential `u` with invertible Hessian, differentiating `det D²u = f` in direction `v`
gives `tr((D²u)⁻¹ D²(∂ᵥu)) = ∂ᵥf / f`. The determinant equation uses the same Hessian
`fderiv ℝ (∇ u)` as the classical density formula for the Aleksandrov measure. In an orthonormal
basis, the trace is the contraction with the inverse Hessian in the nondivergence-form operator.

## Main statements

* `TauCeti.trace_inv_hessian_directional_eq` is the trace form of the differentiated equation.
* `TauCeti.sum_inv_hessian_directional_eq` is its coordinate form for the nondivergence operator.

The use of Jacobi's formula and symmetry of third derivatives follows the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/9cde7938fc09cd017519c7c8a498bee99c12f717/formalization/FunctionalInequalities/Analysis/BakryEmery/LinearizedEquation.lean).
-/

public section

namespace TauCeti

open Filter InnerProductSpace Set
open scoped Gradient Matrix.Norms.Operator Topology

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype ι] [DecidableEq ι]

private noncomputable abbrev hessianMatrix (b : OrthonormalBasis ι ℝ E) (u : E → ℝ) (x : E) :
    Matrix ι ι ℝ :=
  LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (∇ u) x).toLinearMap

private theorem hessian_entry (b : OrthonormalBasis ι ℝ E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (i j : ι) :
    hessianMatrix b u x i j = fderiv ℝ (fderiv ℝ u) x (b j) (b i) := by
  let dual := (toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap
  have hgrad := (hu.gradient_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h := dual.hasFDerivAt.comp x hgrad.hasFDerivAt
  have h' : HasFDerivAt (fderiv ℝ u) (dual.comp (fderiv ℝ (∇ u) x)) x := by
    simpa only [dual, Function.comp_def, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, toDual_gradient] using h
  change LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (∇ u) x).toLinearMap i j = _
  rw [h'.fderiv, LinearMap.toMatrix_apply]
  change b.repr (fderiv ℝ (∇ u) x (b j)) i = dual (fderiv ℝ (∇ u) x (b j)) (b i)
  rw [OrthonormalBasis.repr_apply_apply, real_inner_comm]
  rfl

private theorem hasFDerivAt_hessian_matrix (b : OrthonormalBasis ι ℝ E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) :
    ∃ D : E →L[ℝ] Matrix ι ι ℝ, HasFDerivAt (fun y ↦ hessianMatrix b u y) D x ∧
      ∀ v, D v = hessianMatrix b (fun y ↦ fderiv ℝ u y v) x := by
  let A (y : E) : Matrix ι ι ℝ := Matrix.of fun i j ↦ fderiv ℝ (fderiv ℝ u) y (b j) (b i)
  have hDu : ContDiffAt ℝ 2 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  have hD2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ u)) x :=
    (hDu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hrow (i : ι) : DifferentiableAt ℝ
      (fun y ↦ fun j : ι ↦ fderiv ℝ (fderiv ℝ u) y (b j) (b i)) x :=
    differentiableAt_pi.mpr fun j ↦
      (hD2.clm_apply (differentiableAt_const (b j))).clm_apply (differentiableAt_const (b i))
  have hRows : DifferentiableAt ℝ
      (fun y ↦ fun i j : ι ↦ fderiv ℝ (fderiv ℝ u) y (b j) (b i)) x :=
    differentiableAt_pi.mpr hrow
  have hA : DifferentiableAt ℝ A x := hRows
  have hnear : A =ᶠ[𝓝 x] fun y ↦ hessianMatrix b u y := by
    have hu₂ : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
    filter_upwards [hu₂.eventually (by norm_num)] with y hy
    ext i j
    exact (hessian_entry b hy i j).symm
  refine ⟨fderiv ℝ A x, hA.hasFDerivAt.congr_of_eventuallyEq hnear.symm, fun v ↦ ?_⟩
  have hv : ContDiffAt ℝ 2 (fun y ↦ fderiv ℝ u y v) x := hDu.clm_apply contDiffAt_const
  ext i j
  have hi := congrArg (fun L : E →L[ℝ] (ι → ℝ) => L v j) (fderiv_apply hRows i)
  have hij := congrArg (fun L : E →L[ℝ] ℝ => L v) (fderiv_apply (hrow i) j)
  calc
    _ = fderiv ℝ (fun y ↦ fun j : ι ↦ fderiv ℝ (fderiv ℝ u) y (b j) (b i)) x v j :=
      hi.symm
    _ = fderiv ℝ (fun y ↦ fderiv ℝ (fderiv ℝ u) y (b j) (b i)) x v := hij.symm
    _ = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v (b j) (b i) :=
      fderiv_clm_apply_const_apply₂ hD2 (b j) (b i) v
    _ = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x (b j) v (b i) :=
      congrArg (fun L : E →L[ℝ] ℝ ↦ L (b i)) (hDu.isSymmSndFDerivAt (by norm_num) v (b j))
    _ = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x (b j) (b i) v :=
      fderiv_fderiv_fderiv_apply_comm hu (by norm_num) (b j) v (b i)
    _ = _ := (fderiv_fderiv_fderiv_apply hu v (b j) (b i)).symm.trans
      (hessian_entry b hv i j).symm

/-- The classical determinant equation with invertible Hessian linearizes in each direction on an
open set. The matrices represent the derivatives of the gradients in the given orthonormal basis. -/
theorem trace_inv_hessian_directional_eq (b : OrthonormalBasis ι ℝ E)
    {Ω : Set E} (hΩ : IsOpen Ω) {u f : E → ℝ} (hu : ContDiffOn ℝ 3 u Ω)
    {x : E} (hx : x ∈ Ω)
    (hne : (fderiv ℝ (∇ u) x).det ≠ 0)
    (heq : EqOn (fun y ↦ (fderiv ℝ (∇ u) y).det) f Ω) (v : E) :
    Matrix.trace ((LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (∇ u) x).toLinearMap)⁻¹ *
      LinearMap.toMatrix b.toBasis b.toBasis
        (fderiv ℝ (∇ fun y ↦ fderiv ℝ u y v) x).toLinearMap) = fderiv ℝ f x v / f x := by
  have hΩx := hΩ.mem_nhds hx
  obtain ⟨D, hD, hDir⟩ := hasFDerivAt_hessian_matrix b (hu.contDiffAt hΩx)
  have hdet (y : E) : (hessianMatrix b u y).det = (fderiv ℝ (∇ u) y).det :=
    LinearMap.det_toMatrix _ _
  have hdet_ne : (hessianMatrix b u x).det ≠ 0 := by rwa [hdet x]
  have hlocal : (fun y ↦ (hessianMatrix b u y).det) =ᶠ[𝓝 x] f :=
    Filter.eventually_of_mem hΩx fun y hy ↦ (hdet y).trans (heq hy)
  have hJacobi : fderiv ℝ f x v = (hessianMatrix b u x).det *
      Matrix.trace ((hessianMatrix b u x)⁻¹ * hessianMatrix b (fun y ↦ fderiv ℝ u y v) x) := by
    rw [← hlocal.fderiv_eq]
    have hchain := Matrix.differentiable_det.differentiableAt.hasFDerivAt.comp x hD
    change fderiv ℝ (Matrix.det ∘ fun y ↦ hessianMatrix b u y) x v = _
    rw [hchain.fderiv]
    change fderiv ℝ Matrix.det (hessianMatrix b u x) (D v) = _
    rw [hDir]
    exact Matrix.fderiv_det_apply (isUnit_iff_ne_zero.mpr hdet_ne) _
  have hfx : (hessianMatrix b u x).det = f x := (hdet x).trans (heq hx)
  rw [← hfx, hJacobi, mul_comm, mul_div_cancel_right₀ _ hdet_ne]

/-- The differentiated Monge–Ampère equation in the coordinate convention of the
nondivergence-form Schauder estimate. -/
theorem sum_inv_hessian_directional_eq (b : OrthonormalBasis ι ℝ E)
    {Ω : Set E} (hΩ : IsOpen Ω) {u f : E → ℝ} (hu : ContDiffOn ℝ 3 u Ω)
    {x : E} (hx : x ∈ Ω)
    (hne : (fderiv ℝ (∇ u) x).det ≠ 0)
    (heq : EqOn (fun y ↦ (fderiv ℝ (∇ u) y).det) f Ω) (v : E) :
    (∑ i, ∑ j,
      (LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (∇ u) x).toLinearMap)⁻¹ i j •
      fderiv ℝ (fderiv ℝ (fun y ↦ fderiv ℝ u y v)) x (b i) (b j)) = fderiv ℝ f x v / f x := by
  have hDu : ContDiffAt ℝ 2 (fderiv ℝ u) x := (hu.contDiffAt (hΩ.mem_nhds hx)).fderiv_right
    (by norm_num)
  have hv : ContDiffAt ℝ 2 (fun y ↦ fderiv ℝ u y v) x := hDu.clm_apply contDiffAt_const
  rw [← trace_inv_hessian_directional_eq b hΩ hu hx hne heq v]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hessian_entry b hv, smul_eq_mul]

end TauCeti
