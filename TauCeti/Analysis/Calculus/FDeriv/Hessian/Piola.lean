/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.Calculus.FDeriv.Adjugate
public import TauCeti.Analysis.Calculus.FDeriv.Matrix
public import TauCeti.Analysis.Calculus.Morse.Linearization
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# The Hessian Piola identity

At a point where a real function `u` is `C³`, the adjugate of its Hessian has divergence-free
rows. For a scalar perturbation `v` that is `C²` at the point, the scalar divergence of the
cofactor flux `adj(Hess u) ∇v` is `trace (adj(Hess u) * Hess v)`. Divergence is the trace of the
Fréchet derivative, and the Hessian is `TauCeti.hessianOperator` in an orthonormal basis.
The identities include singular Hessians and the zero-dimensional case.

The row-cancellation argument is adapted from the smooth Piola theorem in the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/65810c73f9dd7945fc646ab484cb19d673f5291d/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean).
-/

public section

open TauCeti
open scoped Gradient Matrix.Norms.Operator ContDiff Topology

namespace OrthonormalBasis

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- At a point where a function is `C³`, the rows of its adjugate Hessian are divergence free. -/
theorem sum_fderiv_adjugate_hessianOperator_eq_zero (b : OrthonormalBasis ι ℝ E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 3 u x) (i : ι) :
    ∑ j, fderiv ℝ (fun y ↦
      (LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator u y).toLinearMap).adjugate i j)
      x (b j) = 0 := by
  have hD : ContDiffAt ℝ 2 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  have hD2 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ u)) x := hD.fderiv_right (by norm_num)
  have hcoords (k l : ι) :
      (fun y ↦ LinearMap.toMatrix b.toBasis b.toBasis
        (hessianOperator u y).toLinearMap k l) =ᶠ[𝓝 x]
      (fun y ↦ fderiv ℝ (fderiv ℝ u) y (b k) (b l)) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    rw [b.toMatrix_hessianOperator_apply]
    exact hy.isSymmSndFDerivAt (by norm_num) _ _
  refine Matrix.sum_fderiv_adjugate_eq_zero_of_comm
    (fun y ↦ LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator u y).toLinearMap)
    (fun j ↦ b j) x ?_ ?_ i
  · intro k l
    have hd : DifferentiableAt ℝ (fun y ↦ fderiv ℝ (fderiv ℝ u) y (b k) (b l)) x :=
      ((hD2.clm_apply (contDiffAt_const (c := b k))).clm_apply
        (contDiffAt_const (c := b l))).differentiableAt one_ne_zero
    exact ((hcoords k l).differentiableAt_iff).2 hd
  · intro j k l
    rw [(hcoords k l).fderiv_eq, (hcoords j l).fderiv_eq,
      fderiv_clm_apply_const_apply₂ (hD2.differentiableAt (by norm_num)),
      fderiv_clm_apply_const_apply₂ (hD2.differentiableAt (by norm_num))]
    exact congrArg (fun L : E →L[ℝ] ℝ ↦ L (b l))
      (hD.isSymmSndFDerivAt (by norm_num) (b j) (b k))

/-- The divergence of the cofactor Hessian flux is its contraction with the Hessian of the
scalar perturbation. -/
theorem trace_fderiv_adjugate_hessianOperator_gradient (b : OrthonormalBasis ι ℝ E)
    {u v : E → ℝ} {x : E} (hu : ContDiffAt ℝ 3 u x) (hv : ContDiffAt ℝ 2 v x) :
    LinearMap.trace ℝ E (fderiv ℝ (fun y ↦
      Matrix.toLin b.toBasis b.toBasis
        (LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator u y).toLinearMap).adjugate
        (∇ v y)) x).toLinearMap =
      ((LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator u x).toLinearMap).adjugate *
        LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator v x).toLinearMap).trace := by
  let : FiniteDimensional ℝ E := Module.Finite.of_basis b.toBasis
  let H (y : E) : Matrix ι ι ℝ :=
    LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator u y).toLinearMap
  have hH : ContDiffAt ℝ 1 (hessianOperator u) x :=
    hu.contDiffAt_hessianOperator (by norm_num)
  have hentry (i j : ι) : DifferentiableAt ℝ (fun y ↦ H y i j) x := by
    have hc : ContDiffAt ℝ 1 (fun _ : E ↦ b i) x := contDiffAt_const
    have hd : ContDiffAt ℝ 1 (fun y ↦ inner ℝ (b i) (hessianOperator u y (b j))) x :=
      hc.inner ℝ (hH.clm_apply (contDiffAt_const (c := b j)))
    simpa only [H, LinearMap.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply,
      ContinuousLinearMap.coe_coe, b.repr_apply_apply] using hd.differentiableAt one_ne_zero
  have hAdj (i j : ι) : DifferentiableAt ℝ (fun y ↦ (H y).adjugate i j) x :=
    Matrix.differentiableAt_adjugate_apply H x hentry i j
  have hDv (j : ι) : DifferentiableAt ℝ (fun y ↦ fderiv ℝ v y (b j)) x :=
    ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hsym : ∀ᶠ y in 𝓝 x, (H y).IsSymm := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    ext i j
    simp only [Matrix.transpose_apply, H, b.toMatrix_hessianOperator_apply]
    exact hy.isSymmSndFDerivAt (by norm_num) _ _
  have hcol (j : ι) :
      ∑ i, fderiv ℝ (fun y ↦ (H y).adjugate i j) x (b i) = 0 := by
    have heq (i : ι) :
        (fun y ↦ (H y).adjugate i j) =ᶠ[𝓝 x] fun y ↦ (H y).adjugate j i := by
      filter_upwards [hsym] with y hy
      exact (congrArg (fun A : Matrix ι ι ℝ ↦ A i j) hy.adjugate).symm
    calc
      ∑ i, fderiv ℝ (fun y ↦ (H y).adjugate i j) x (b i) =
          ∑ i, fderiv ℝ (fun y ↦ (H y).adjugate j i) x (b i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun L : E →L[ℝ] ℝ ↦ L (b i)) (heq i).fderiv_eq
      _ = 0 := b.sum_fderiv_adjugate_hessianOperator_eq_zero hu j
  let c (i : ι) (y : E) := ∑ j, (H y).adjugate i j * fderiv ℝ v y (b j)
  have hc (i : ι) : DifferentiableAt ℝ (c i) x :=
    DifferentiableAt.fun_sum fun j _ ↦ (hAdj i j).mul (hDv j)
  have hflux : (fun y ↦ Matrix.toLin b.toBasis b.toBasis (H y).adjugate (∇ v y)) =
      fun y ↦ ∑ i, c i y • b i := by
    funext y
    simp only [Matrix.toLin_apply, Matrix.mulVec, dotProduct, b.coe_toBasis,
      b.coe_toBasis_repr_apply, b.repr_apply_apply, inner_gradient_right, conj_trivial, c]
  have hdiv : LinearMap.trace ℝ E
      (fderiv ℝ (fun y ↦ ∑ i, c i y • b i) x).toLinearMap =
        ∑ i, fderiv ℝ (c i) x (b i) := by
    rw [fderiv_fun_sum (fun i _ ↦ (hc i).smul_const (b i)),
      ContinuousLinearMap.toLinearMap_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [fderiv_smul_const (hc i)]
    exact LinearMap.trace_smulRight _ _
  have hproduct : ∑ i, fderiv ℝ (c i) x (b i) =
      ((H x).adjugate *
        Matrix.of (fun j i ↦ fderiv ℝ (fun y ↦ fderiv ℝ v y (b j)) x (b i))).trace := by
    simpa only [Matrix.mulVec, dotProduct, c] using
      Matrix.sum_fderiv_mulVec_eq_trace_of_sum_fderiv_eq_zero
        (fun y ↦ (H y).adjugate) (fun y j ↦ fderiv ℝ v y (b j)) (fun i ↦ b i) x hAdj hDv hcol
  have hJac : Matrix.of (fun j i ↦ fderiv ℝ (fun y ↦ fderiv ℝ v y (b j)) x (b i)) =
      LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator v x).toLinearMap := by
    ext j i
    rw [Matrix.of_apply, b.toMatrix_hessianOperator_apply,
      fderiv_clm_apply_const_apply
        ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)]
  have hmain : LinearMap.trace ℝ E
      (fderiv ℝ (fun y ↦ Matrix.toLin b.toBasis b.toBasis (H y).adjugate (∇ v y)) x).toLinearMap =
      ((H x).adjugate *
        LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator v x).toLinearMap).trace := by
    rw [hflux, hdiv, hproduct, hJac]
  simpa only [H] using hmain

end OrthonormalBasis
