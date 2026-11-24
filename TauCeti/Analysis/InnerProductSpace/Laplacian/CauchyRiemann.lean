/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.MeanValueInequality
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Linear Cauchy–Riemann equations

A map `v : ℂ → W`, with `s + i t` the coordinate on `ℂ`, solves a *linear Cauchy–Riemann
equation* when `∂ₜv = J ∂ₛv + B v` for coefficient families `J`, `B : ℂ → End W` with `J² = -1`.
Here `∂ₛv = dv(1)` and `∂ₜv = dv(i)` are written `fderiv ℝ v y 1` and `fderiv ℝ v y I`. Such
equations arise by linearising a nonlinear Cauchy–Riemann equation: the `s`-derivative of a
`J`-holomorphic curve or of a Floer cylinder solves one.

Differentiating the equation once and using `J² = -1`, the second derivatives of `v` cancel in
`Δ v`, which is then a first-order expression in `v` with coefficients built from `J`, `B` and
their first derivatives. In an inner product space this gives `Δ ‖v‖² ≥ -K ‖v‖²`, with `K`
depending on bounds for `J`, `B` and their first derivatives. The right-hand side is linear in
`‖v‖²`, so the two-dimensional mean-value inequality
`TauCeti.pi_mul_sq_mul_le_fifteen_mul_setIntegral_ball_of_neg_mul_le_laplacian` holds on every disc
with `16 K r² ≤ 1`, whatever the integral of `‖v‖²`.

## Main declarations

* `TauCeti.fderiv_fderiv_apply_I_eq_of_fderiv_I_eq`, `TauCeti.laplacian_eq_of_fderiv_I_eq`: a
  linear Cauchy–Riemann equation differentiated once, and the resulting first-order formula for
  the Laplacian of a solution.
* `TauCeti.neg_mul_norm_sq_le_laplacian_of_fderiv_I_eq`: the differential inequality
  `Δ ‖v‖² ≥ -K ‖v‖²` for a solution of a linear Cauchy–Riemann equation.
* `TauCeti.pi_mul_sq_mul_norm_sq_le_fifteen_mul_setIntegral_ball_of_fderiv_I_eq`: the mean-value
  inequality for solutions of linear Cauchy–Riemann equations.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.3.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Filter Topology Complex Metric MeasureTheory Real

variable {z : ℂ}

/-! ### The differentiated equation and the Laplacian -/

section NormedSpace

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {v : ℂ → W} {J B : ℂ → W →L[ℝ] W}

/-- **The differentiated linear Cauchy–Riemann equation.** If `v` is `C²` at `z` and solves
`∂ₜv = J ∂ₛv + B v` near `z`, with `J` and `B` differentiable at `z`, then differentiating the
equation at `z` in the direction `w` gives
`∂_w ∂ₜv = (∂_w J) ∂ₛv + J ∂_w ∂ₛv + (∂_w B) v + B ∂_w v`. -/
theorem fderiv_fderiv_apply_I_eq_of_fderiv_I_eq (hv : ContDiffAt ℝ 2 v z)
    (hJ : DifferentiableAt ℝ J z) (hB : DifferentiableAt ℝ B z)
    (heq : ∀ᶠ y in 𝓝 z, fderiv ℝ v y I = J y (fderiv ℝ v y 1) + B y (v y)) (w : ℂ) :
    fderiv ℝ (fderiv ℝ v) z w I =
      fderiv ℝ J z w (fderiv ℝ v z 1) + J z (fderiv ℝ (fderiv ℝ v) z w 1) +
        fderiv ℝ B z w (v z) + B z (fderiv ℝ v z w) := by
  have hvd : DifferentiableAt ℝ v z := hv.differentiableAt (by norm_num)
  have hDv : DifferentiableAt ℝ (fderiv ℝ v) z :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hvs : DifferentiableAt ℝ (fun y ↦ fderiv ℝ v y 1) z :=
    hDv.clm_apply (differentiableAt_const 1)
  have h := congrArg (fun L : ℂ →L[ℝ] W ↦ L w)
    (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (f₁ := fun y ↦ fderiv ℝ v y I)
      (f := fun y ↦ J y (fderiv ℝ v y 1) + B y (v y)) heq)
  rw [fderiv_clm_apply_const_apply hDv, fderiv_fun_add (hJ.clm_apply hvs) (hB.clm_apply hvd),
    fderiv_clm_apply hJ hvs, fderiv_clm_apply hB hvd] at h
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    fderiv_clm_apply_const_apply hDv] at h
  rw [h]
  abel

/-- **The Laplacian of a solution of a linear Cauchy–Riemann equation.** If `v` is `C²` at `z` and
solves `∂ₜv = J ∂ₛv + B v` near `z`, with `J` and `B` differentiable at `z` and `J(z)² = -1`, then
the second derivatives of `v` drop out of `Δ v z`, leaving first-order terms in `v` whose
coefficients involve `J`, `B` and their first derivatives. -/
theorem laplacian_eq_of_fderiv_I_eq (hv : ContDiffAt ℝ 2 v z) (hJ : DifferentiableAt ℝ J z)
    (hB : DifferentiableAt ℝ B z)
    (heq : ∀ᶠ y in 𝓝 z, fderiv ℝ v y I = J y (fderiv ℝ v y 1) + B y (v y))
    (hJsq : ∀ w, J z (J z w) = -w) :
    Δ v z = fderiv ℝ J z I (fderiv ℝ v z 1) + J z (fderiv ℝ J z 1 (fderiv ℝ v z 1)) +
      J z (B z (fderiv ℝ v z 1)) + B z (fderiv ℝ v z I) +
      J z (fderiv ℝ B z 1 (v z)) + fderiv ℝ B z I (v z) := by
  have hsymm : fderiv ℝ (fderiv ℝ v) z I 1 = fderiv ℝ (fderiv ℝ v) z 1 I :=
    hv.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) I 1
  have hDv : DifferentiableAt ℝ (fderiv ℝ v) z :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h₁ := fderiv_fderiv_apply_I_eq_of_fderiv_I_eq hv hJ hB heq I
  have h₂ := fderiv_fderiv_apply_I_eq_of_fderiv_I_eq hv hJ hB heq 1
  rw [hsymm, h₂] at h₁
  rw [laplacian_eq_fderiv_fderiv_apply_one_add_fderiv_fderiv_apply_I hDv,
    fderiv_clm_apply_const_apply hDv 1 1, fderiv_clm_apply_const_apply hDv I I, h₁]
  simp only [map_add, hJsq]
  abel

end NormedSpace

/-! ### The mean-value inequality -/

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {v : ℂ → V}
  {J B : ℂ → V →L[ℝ] V}

/-- **The squared norm of a solution of a linear Cauchy–Riemann equation is almost
subharmonic.** Let `v : ℂ → V` be `C²` at `z` and solve `∂ₜv = J ∂ₛv + B v` near `z`, where the
families `J`, `B : ℂ → End V` are differentiable at `z` and `J(z)² = -1`. If `a`, `b`, `β`, `γ`
bound the norms of `J z`, of the derivative of `J` at `z`, of `B z` and of the derivative of `B`
at `z`, then

`Δ ‖v‖² ≥ -K ‖v‖²` at `z`, with `K = ((b + ab + aβ)² + β²) / 2 + 2 (aγ + γ)`.

Unlike the nonlinear equation of `TauCeti.neg_mul_norm_fderiv_one_pow_four_le_laplacian`, the
right-hand side is quadratic, not quartic, in `v`. The derivative `v = ∂ₛu` of a Floer cylinder
for a Hamiltonian perturbation `H_t dt` solves such an equation. -/
theorem neg_mul_norm_sq_le_laplacian_of_fderiv_I_eq {a b β γ : ℝ} (hv : ContDiffAt ℝ 2 v z)
    (hJ : DifferentiableAt ℝ J z) (hB : DifferentiableAt ℝ B z)
    (heq : ∀ᶠ y in 𝓝 z, fderiv ℝ v y I = J y (fderiv ℝ v y 1) + B y (v y))
    (hJsq : ∀ w, J z (J z w) = -w) (ha : ‖J z‖ ≤ a) (hb : ‖fderiv ℝ J z‖ ≤ b)
    (hβ : ‖B z‖ ≤ β) (hγ : ‖fderiv ℝ B z‖ ≤ γ) :
    -((((b + a * b + a * β) ^ 2 + β ^ 2) / 2 + 2 * (a * γ + γ)) * ‖v z‖ ^ 2) ≤
      Δ (fun y ↦ ‖v y‖ ^ 2) z := by
  set vs := fderiv ℝ v z 1
  set vt := fderiv ℝ v z I
  have ha₀ : 0 ≤ a := (J z).opNorm_nonneg.trans ha
  have hJ₀ : ∀ w, ‖J z w‖ ≤ a * ‖w‖ := fun w ↦ (J z).le_of_opNorm_le ha w
  have hB₀ : ∀ w, ‖B z w‖ ≤ β * ‖w‖ := fun w ↦ (B z).le_of_opNorm_le hβ w
  have hJ₁ : ∀ (d : ℂ) w, ‖d‖ ≤ 1 → ‖fderiv ℝ J z d w‖ ≤ b * ‖w‖ := fun d w hd ↦
    ((fderiv ℝ J z).le_of_opNorm₂_le_of_le hb hd le_rfl).trans_eq (by ring)
  have hB₁ : ∀ (d : ℂ) w, ‖d‖ ≤ 1 → ‖fderiv ℝ B z d w‖ ≤ γ * ‖w‖ := fun d w hd ↦
    ((fderiv ℝ B z).le_of_opNorm₂_le_of_le hγ hd le_rfl).trans_eq (by ring)
  -- `‖Δ v‖ ≤ (b + ab + aβ) ‖∂ₛv‖ + β ‖∂ₜv‖ + (aγ + γ) ‖v‖`.
  have hL : ‖Δ v z‖ ≤ (b + a * b + a * β) * ‖vs‖ + β * ‖vt‖ + (a * γ + γ) * ‖v z‖ := by
    rw [laplacian_eq_of_fderiv_I_eq hv hJ hB heq hJsq]
    have h1 := hJ₁ I vs (by simp)
    have h2 : ‖J z (fderiv ℝ J z 1 vs)‖ ≤ a * (b * ‖vs‖) :=
      (hJ₀ _).trans (by gcongr; exact hJ₁ 1 vs (by simp))
    have h3 : ‖J z (B z vs)‖ ≤ a * (β * ‖vs‖) := (hJ₀ _).trans (by gcongr; exact hB₀ vs)
    have h4 := hB₀ vt
    have h5 : ‖J z (fderiv ℝ B z 1 (v z))‖ ≤ a * (γ * ‖v z‖) :=
      (hJ₀ _).trans (by gcongr; exact hB₁ 1 (v z) (by simp))
    have h6 := hB₁ I (v z) (by simp)
    refine (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
      (norm_add_le_of_le h1 h2) h3) h4) h5) h6).trans_eq ?_
    ring
  have hinner := neg_le_of_abs_le (abs_real_inner_le_norm (v z) (Δ v z))
  rw [hv.laplacian_norm_sq Complex.orthonormalBasisOneI]
  simp only [Complex.coe_orthonormalBasisOneI, Fin.sum_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hX := norm_nonneg (v z)
  nlinarith [mul_le_mul_of_nonneg_left hL hX,
    sq_nonneg (‖vs‖ - (b + a * b + a * β) * ‖v z‖ / 2), sq_nonneg (‖vt‖ - β * ‖v z‖ / 2)]

/-- **The mean-value inequality for linear Cauchy–Riemann equations.** Let `v : ℂ → V` be `C²` on
the open disk `ball z₀ r` and continuous on its closure, and solve `∂ₜv = J ∂ₛv + B v` on the
disk, where `J` and `B` are differentiable on the disk with `J² = -1` there. Suppose that `a`,
`b`, `β`, `γ` bound the norms of `J`, of its derivative, of `B` and of its derivative on the disk,
and put `K = ((b + ab + aβ)² + β²) / 2 + 2 (aγ + γ)`. If `16 K r² ≤ 1`, then

`π r² ‖v(z₀)‖² ≤ 15 ∫_{B_r(z₀)} ‖v‖²`.

No smallness of the integral is needed, in contrast to
`TauCeti.pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball`. -/
theorem pi_mul_sq_mul_norm_sq_le_fifteen_mul_setIntegral_ball_of_fderiv_I_eq {z₀ : ℂ}
    {r a b β γ : ℝ} (hr : 0 ≤ r) (hv : ContDiffOn ℝ 2 v (ball z₀ r))
    (hvc : ContinuousOn v (closedBall z₀ r)) (hJ : ∀ y ∈ ball z₀ r, DifferentiableAt ℝ J y)
    (hB : ∀ y ∈ ball z₀ r, DifferentiableAt ℝ B y)
    (heq : ∀ y ∈ ball z₀ r, fderiv ℝ v y I = J y (fderiv ℝ v y 1) + B y (v y))
    (hJsq : ∀ y ∈ ball z₀ r, ∀ w, J y (J y w) = -w) (ha : ∀ y ∈ ball z₀ r, ‖J y‖ ≤ a)
    (hb : ∀ y ∈ ball z₀ r, ‖fderiv ℝ J y‖ ≤ b) (hβ : ∀ y ∈ ball z₀ r, ‖B y‖ ≤ β)
    (hγ : ∀ y ∈ ball z₀ r, ‖fderiv ℝ B y‖ ≤ γ)
    (hKr : 16 * (((b + a * b + a * β) ^ 2 + β ^ 2) / 2 + 2 * (a * γ + γ)) * r ^ 2 ≤ 1) :
    π * r ^ 2 * ‖v z₀‖ ^ 2 ≤ 15 * ∫ y in ball z₀ r, ‖v y‖ ^ 2 := by
  exact pi_mul_sq_mul_le_fifteen_mul_setIntegral_ball_of_neg_mul_le_laplacian
    (w := fun y ↦ ‖v y‖ ^ 2) hr (hv.norm_sq ℝ) (hvc.norm.pow 2) (fun _ _ ↦ by positivity)
    (fun y hy ↦ neg_mul_norm_sq_le_laplacian_of_fderiv_I_eq
      (hv.contDiffAt (isOpen_ball.mem_nhds hy)) (hJ y hy) (hB y hy)
      (eventually_of_mem (isOpen_ball.mem_nhds hy) heq) (hJsq y hy) (ha y hy) (hb y hy)
      (hβ y hy) (hγ y hy)) hKr

end InnerProductSpace

end TauCeti
