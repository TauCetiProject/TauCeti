/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Gradient.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Derivatives of solutions of `Δ g = k g` and a Kato subsolution

On a finite-dimensional real inner product space the Laplacian commutes with derivatives of `C³`
maps: `Δ (∂ᵥ u) = ∂ᵥ (Δ u)` (`ContDiffAt.laplacian_fderiv_apply`, `ContDiffAt.laplacian_fderiv`),
and `Δ (∇ u) = ∇ (Δ u)` for real functions (`ContDiffAt.laplacian_gradient`).
So the derivatives of a solution of a semilinear equation `Δ u = F(u)` satisfy the linearized
equation `Δ (∂ᵥ u) = F'(u) ∂ᵥ u`.

For a vector-valued `g` with `Δ g = k g`, `k ≥ 0`, the Bochner identity
`Δ ‖g‖² = 2 ‖Dg‖² + 2 k ‖g‖²` and the Kato inequality `|∇ ‖g‖| ≤ ‖Dg‖` show that `‖g‖` is a
subsolution of `-Δ + k`. Since `‖g‖` need not be differentiable where `g` vanishes, the
statement here uses the smooth regularization `w = √(‖g‖² + δ)`, `δ > 0`:

`k (w - √δ) ≤ Δ w`  (`ContDiffAt.mul_sqrt_norm_sq_add_sub_le_laplacian`).

As `δ → 0` the function `w - √δ` increases to `‖g‖`, so a comparison principle applied to
`w - √δ` with bounds uniform in `δ` transfers to `‖g‖` itself. This gives exponential decay of
`‖g‖` at every rate below `√k`, whereas the Bochner identity alone only makes `‖g‖²` a
subsolution of `-Δ + 2k`, which gives `‖g‖` the slower rates below `√(k / 2)`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001, Chapter 3 (the comparison principle).
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Filter Topology
open scoped Gradient RealInnerProductSpace

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The Laplacian commutes with directional derivatives.** For a map `u` which is `C³` at `x`,
`Δ (∂ᵥ u) = ∂ᵥ (Δ u)` at `x`. -/
theorem _root_.ContDiffAt.laplacian_fderiv_apply {u : E → F} {x : E} (hu : ContDiffAt ℝ 3 u x)
    (v : E) : Δ (fun y ↦ fderiv ℝ u y v) x = fderiv ℝ (Δ u) x v := by
  set b := stdOrthonormalBasis ℝ E
  have hDu : ContDiffAt ℝ 2 (fderiv ℝ u) x := hu.fderiv_right (m := 2) (by norm_num)
  have hD2 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ u)) x := hDu.fderiv_right (m := 1) (by norm_num)
  have hD2d : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ u)) x := hD2.differentiableAt (by norm_num)
  -- `Δ u` is the sum of the diagonal second derivatives in the basis `b`, at every point.
  have hΔ : Δ u = fun y ↦ ∑ i, fderiv ℝ (fderiv ℝ u) y (b i) (b i) := by
    funext y
    rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis u b) y]
    simp [iteratedFDeriv_two_apply]
  have hd (i : Fin (Module.finrank ℝ E)) :
      DifferentiableAt ℝ (fun y ↦ fderiv ℝ (fderiv ℝ u) y (b i) (b i)) x :=
    (hD2d.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis _ b) x, hΔ,
    fderiv_fun_sum fun i _ ↦ hd i]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fderiv_fderiv_fderiv_apply hu, fderiv_clm_apply_const_apply
      (hD2d.clm_apply (differentiableAt_const _)),
    fderiv_clm_apply_const_apply hD2d,
    fderiv_fderiv_fderiv_apply_comm hu (by simp) (b i) (b i) v,
    hDu.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) (b i) v]

/-- **The Laplacian commutes with the derivative.** For a map `u` which is `C³` at `x`,
`Δ (Du) = D (Δ u)` at `x`, as continuous linear maps. -/
theorem _root_.ContDiffAt.laplacian_fderiv {u : E → F} {x : E} (hu : ContDiffAt ℝ 3 u x) :
    Δ (fderiv ℝ u) x = fderiv ℝ (Δ u) x := by
  have hDu : ContDiffAt ℝ 2 (fderiv ℝ u) x := hu.fderiv_right (m := 2) (by norm_num)
  ext v
  rw [← hu.laplacian_fderiv_apply v]
  exact (hDu.laplacian_CLM_comp_left (l := ContinuousLinearMap.apply ℝ F v)).symm

/-- **The Laplacian commutes with the gradient.** For a real function `u` which is `C³` at `x`,
`Δ (∇ u) = ∇ (Δ u)` at `x`. -/
theorem _root_.ContDiffAt.laplacian_gradient {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 3 u x) :
    Δ (∇ u) x = ∇ (Δ u) x := by
  have hg : ContDiffAt ℝ 2 (∇ u) x := hu.gradient_right (by norm_num)
  refine ext_inner_left ℝ fun a ↦ ?_
  have hcomp : (innerSL ℝ a ∘ ∇ u) = fun y ↦ fderiv ℝ u y a := by
    funext y
    simp [inner_gradient_right]
  have h := hg.laplacian_CLM_comp_left (l := innerSL ℝ a)
  rw [hcomp, hu.laplacian_fderiv_apply, Function.comp_apply, innerSL_apply_apply] at h
  rw [← h, inner_gradient_right, conj_trivial]

variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- **A Kato subsolution.** Let `g` be `C²` at `x` with `Δ g = k g` at `x`, where `k ≥ 0`. For
`δ > 0` the regularized norm `w = √(‖g‖² + δ)` satisfies `k (w - √δ) ≤ Δ w` at `x`. As `δ → 0`,
`w - √δ` increases to `‖g‖`, which is therefore a subsolution of `-Δ + k` in the limit. -/
theorem _root_.ContDiffAt.mul_sqrt_norm_sq_add_sub_le_laplacian {g : E → G} {x : E} {k δ : ℝ}
    (hg : ContDiffAt ℝ 2 g x) (hΔ : Δ g x = k • g x) (hk : 0 ≤ k) (hδ : 0 < δ) :
    k * (√(‖g x‖ ^ 2 + δ) - √δ) ≤ Δ (fun y ↦ √(‖g y‖ ^ 2 + δ)) x := by
  set b := stdOrthonormalBasis ℝ E
  set v : E → ℝ := fun y ↦ ‖g y‖ ^ 2
  set w : E → ℝ := fun y ↦ √(v y + δ)
  have hv : ContDiffAt ℝ 2 v x := hg.norm_sq ℝ
  have hvδ : ∀ y, 0 < v y + δ := fun y ↦ by positivity
  have hw : ContDiffAt ℝ 2 w x := (hv.add contDiffAt_const).sqrt (hvδ x).ne'
  have hwx : 0 < w x := Real.sqrt_pos.mpr (hvδ x)
  have hww : ∀ y, w y * w y = v y + δ := fun y ↦ Real.mul_self_sqrt (hvδ y).le
  -- The Bochner identity for `‖g‖²`, with `H = ∑ᵢ ‖Dg (bᵢ)‖²`.
  set H := ∑ i, ‖fderiv ℝ g x (b i)‖ ^ 2
  have hΔv : Δ v x = 2 * H + 2 * k * v x := by
    rw [hg.laplacian_norm_sq b, hΔ, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  -- Differentiating `w² = ‖g‖² + δ` gives `w ∂ᵥw = ⟪g, ∂ᵥg⟫`.
  have hD (h : E) : w x * fderiv ℝ w x h = ⟪g x, fderiv ℝ g x h⟫ := by
    have hgd := hg.differentiableAt (by norm_num)
    have hwd := hw.differentiableAt (by norm_num)
    have h₁ := congrArg (fun L : E →L[ℝ] ℝ ↦ L h)
      (congrArg (fun f ↦ fderiv ℝ f x) (funext hww))
    rw [fderiv_fun_mul hwd hwd, fderiv_add_const, hgd.hasFDerivAt.norm_sq.fderiv] at h₁
    simp only [add_apply, smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply] at h₁
    linarith
  -- The Kato inequality: `‖∇w‖² ≤ H`, since `‖g‖ ≤ w`.
  have hkato : ‖∇ w x‖ ^ 2 ≤ H := by
    rw [← b.sum_sq_inner_left]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [inner_gradient_left]
    have hcs := abs_real_inner_le_norm (g x) (fderiv ℝ g x (b i))
    have hgw : ‖g x‖ ^ 2 ≤ w x ^ 2 := by
      rw [sq (w x), hww]
      exact le_add_of_nonneg_right hδ.le
    have hsq : (w x * fderiv ℝ w x (b i)) ^ 2 ≤ w x ^ 2 * ‖fderiv ℝ g x (b i)‖ ^ 2 := by
      rw [hD, ← sq_abs]
      calc |⟪g x, fderiv ℝ g x (b i)⟫| ^ 2 ≤ (‖g x‖ * ‖fderiv ℝ g x (b i)‖) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hcs 2
        _ = ‖g x‖ ^ 2 * ‖fderiv ℝ g x (b i)‖ ^ 2 := by ring
        _ ≤ w x ^ 2 * ‖fderiv ℝ g x (b i)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hgw (by positivity)
    rw [mul_pow] at hsq
    exact le_of_mul_le_mul_left hsq (by positivity)
  -- The Laplacian of `w² = ‖g‖² + δ`, computed in two ways.
  have hΔww : 2 * w x * Δ w x + 2 * ‖∇ w x‖ ^ 2 = 2 * H + 2 * k * v x := by
    have h₁ := hw.laplacian_fun_mul hw
    rw [real_inner_self_eq_norm_sq] at h₁
    have h₂ : Δ (fun y ↦ w y * w y) x = Δ v x := by
      rw [funext hww]
      exact (hv.laplacian_add (contDiffAt_const (c := δ))).trans (by simp [laplacian_const])
    rw [h₂, hΔv] at h₁
    linarith
  -- Hence `w Δw ≥ k ‖g‖² = k (w² - δ) ≥ k w (w - √δ)`.
  have hsδ : √δ ≤ w x := Real.sqrt_le_sqrt (le_add_of_nonneg_left (by positivity))
  have hsqδ : √δ * √δ = δ := Real.mul_self_sqrt hδ.le
  have hmain : w x * (k * (w x - √δ)) ≤ w x * Δ w x := by
    have hvx : v x = w x * w x - δ := by rw [hww]; ring
    nlinarith [mul_nonneg hk (mul_nonneg (Real.sqrt_nonneg δ) (sub_nonneg.mpr hsδ))]
  exact le_of_mul_le_mul_left hmain hwx

end TauCeti
