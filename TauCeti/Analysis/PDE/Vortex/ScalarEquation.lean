/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Deformation
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
public import TauCeti.Analysis.InnerProductSpace.Laplacian.LocalExtr

/-!
# The scalar equation of a plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has connection
`a = i (b₁ ds + b₂ dt)` and section `α = 2 (p + i q)`, so `|α|² = 4 (p² + q²)`. Away from the
zeros of `α`, the holomorphicity equation `∂bar_a α = 0` determines the connection from `α`:
the gradient of `log |α|²` is twice the rotated sum of `b` and the phase current
`(p ∇q - q ∇p) / (p² + q²)` of `α`. Since the phase current is curl free, the curvature
equation `*iF_a = (1 - |α|²) / 8` becomes the scalar equation

`Δ (log |α|²) = (|α|² - 1) / 4`

on the open set where `α ≠ 0`. This is the reduction of the vortex equations to a single
semilinear elliptic equation for `u = 2 log |α|`, which underlies the existence, uniqueness and
reconstruction theory of vortices with prescribed zeros.

## Main results

* `TauCeti.Vortex.fderiv_log_normSq_apply_one`, `TauCeti.Vortex.fderiv_log_normSq_apply_I`:
  the two partial derivatives of `log |α|²` at a nonzero point where `∂bar_a α = 0`.
* `TauCeti.Vortex.laplacian_log_normSq`: if `∂bar_a α = 0` near a point where `α ≠ 0`, then
  `Δ (log |α|²) = (|α|² - 1) / 4 - 2 E`, where `E` is the curvature defect `equation x z 0`.
* `TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`: the scalar equation
  `Δ (log |α|²) = (|α|² - 1) / 4` near a nonzero point of a solution.
* `TauCeti.Vortex.normSq_le_one_of_tendsto`: a `C²` solution on the whole plane with
  `|α| → 1` at infinity satisfies `|α| ≤ 1` everywhere, by the maximum principle.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg-Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Topology InnerProductSpace Laplacian

/-- The derivative of `|α|² = 4 (p² + q²)` along `v`. -/
private theorem fderiv_normSq_apply {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (v : ℂ) :
    fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z v =
      8 * (x z 2 * fderiv ℝ (fun w ↦ x w 2) z v + x z 3 * fderiv ℝ (fun w ↦ x w 3) z v) := by
  rw [(((hp.hasFDerivAt.pow 2).fun_add (hq.hasFDerivAt.pow 2)).const_mul 4).fderiv]
  simp
  ring

/-- At a point where `α ≠ 0` and `∂bar_a α = 0`, the derivative of `log |α|²` along `∂_s` is
`2 (p ∂_t q - q ∂_t p) / (p² + q²) + 2 b₂`. -/
theorem fderiv_log_normSq_apply_one {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0) (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0) :
    fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z 1 =
      2 * (x z 2 * fderiv ℝ (fun w ↦ x w 3) z I - x z 3 * fderiv ℝ (fun w ↦ x w 2) z I) /
        (x z 2 ^ 2 + x z 3 ^ 2) + 2 * x z 1 := by
  have hρ : DifferentiableAt ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z := by fun_prop
  rw [fderiv.log hρ (mul_ne_zero four_ne_zero hα)]
  rw [equation_apply_one] at h₁
  rw [equation_apply_two] at h₂
  rw [FunLike.coe_smul, Pi.smul_apply, fderiv_normSq_apply hp hq, smul_eq_mul, inv_mul_eq_div,
    div_add' _ _ _ hα, div_eq_div_iff (mul_ne_zero four_ne_zero hα) hα]
  linear_combination (8 * (x z 2 ^ 2 + x z 3 ^ 2)) * (x z 2 * h₁ + x z 3 * h₂)

/-- At a point where `α ≠ 0` and `∂bar_a α = 0`, the derivative of `log |α|²` along `∂_t` is
`-2 (p ∂_s q - q ∂_s p) / (p² + q²) - 2 b₁`. -/
theorem fderiv_log_normSq_apply_I {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0) (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0) :
    fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z I =
      -(2 * (x z 2 * fderiv ℝ (fun w ↦ x w 3) z 1 - x z 3 * fderiv ℝ (fun w ↦ x w 2) z 1) /
        (x z 2 ^ 2 + x z 3 ^ 2)) - 2 * x z 0 := by
  have hρ : DifferentiableAt ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z := by fun_prop
  rw [fderiv.log hρ (mul_ne_zero four_ne_zero hα)]
  rw [equation_apply_one] at h₁
  rw [equation_apply_two] at h₂
  rw [FunLike.coe_smul, Pi.smul_apply, fderiv_normSq_apply hp hq, smul_eq_mul, inv_mul_eq_div,
    neg_div', div_sub' hα, div_eq_div_iff (mul_ne_zero four_ne_zero hα) hα]
  linear_combination (8 * (x z 2 ^ 2 + x z 3 ^ 2)) * (x z 2 * h₂ - x z 3 * h₁)

/-- If `∂bar_a α = 0` near a point `z` where `α ≠ 0`, then
`Δ (log |α|²) = (|α|² - 1) / 4 - 2 E` at `z`, where `E = equation x z 0` is the defect in the
curvature equation `*iF_a = (1 - |α|²) / 8`. Only the components `b` need be differentiable
at `z`; the section components are `C²` at `z`. -/
theorem laplacian_log_normSq {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hb₁ : DifferentiableAt ℝ (fun w ↦ x w 0) z) (hb₂ : DifferentiableAt ℝ (fun w ↦ x w 1) z)
    (hp : ContDiffAt ℝ 2 (fun w ↦ x w 2) z) (hq : ContDiffAt ℝ 2 (fun w ↦ x w 3) z)
    (hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0)
    (hsol : ∀ᶠ w in 𝓝 z, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    Δ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z =
      (4 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 4 - 2 * equation x z 0 := by
  have hℓ : ContDiffAt ℝ 2 (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z :=
    (contDiffAt_const.mul ((hp.pow 2).add (hq.pow 2))).log (mul_ne_zero four_ne_zero hα)
  have hdℓ := (hℓ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hR : ContinuousAt (fun w ↦ x w 2 ^ 2 + x w 3 ^ 2) z :=
    (hp.continuousAt.pow 2).add (hq.continuousAt.pow 2)
  have hev := ((hp.eventually (by simp)).and ((hq.eventually (by simp)).and
    ((hR.eventually_ne hα).and hsol)))
  have e₁ := hev.mono fun w ⟨hpw, hqw, hαw, h₁, h₂⟩ ↦ fderiv_log_normSq_apply_one
    (hpw.differentiableAt (by norm_num)) (hqw.differentiableAt (by norm_num)) hαw h₁ h₂
  have e₂ := hev.mono fun w ⟨hpw, hqw, hαw, h₁, h₂⟩ ↦ fderiv_log_normSq_apply_I
    (hpw.differentiableAt (by norm_num)) (hqw.differentiableAt (by norm_num)) hαw h₁ h₂
  -- Near `z` the partial derivatives of `log |α|²` are the first-order expressions above,
  -- so the Laplacian is the sum of their derivatives along `∂_s` and `∂_t`.
  rw [laplacian_eq_sum_fderiv_fderiv_apply Complex.orthonormalBasisOneI hdℓ, Fin.sum_univ_two]
  simp only [Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Filter.EventuallyEq.fderiv_eq e₁, Filter.EventuallyEq.fderiv_eq e₂]
  -- Differentiate those expressions explicitly; the phase-current terms cancel by symmetry
  -- of the second derivatives of `p` and `q`, leaving `2 (∂_s b₂ - ∂_t b₁)`.
  have hp' := hp.differentiableAt (by norm_num)
  have hq' := hq.differentiableAt (by norm_num)
  have hdp := (hp.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdq := (hq.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hpart (v : ℂ) : DifferentiableAt ℝ (fun w ↦ fderiv ℝ (fun w ↦ x w 2) w v) z :=
    hdp.clm_apply (differentiableAt_const _)
  have hqart (v : ℂ) : DifferentiableAt ℝ (fun w ↦ fderiv ℝ (fun w ↦ x w 3) w v) z :=
    hdq.clm_apply (differentiableAt_const _)
  have hRh := (hp'.hasFDerivAt.pow 2).fun_add (hq'.hasFDerivAt.pow 2)
  have hinv := (hasDerivAt_inv hα).comp_hasFDerivAt z hRh
  simp only [Function.comp_def] at hinv
  have hG₁ := (((hp'.hasFDerivAt.fun_mul (hqart I).hasFDerivAt).fun_sub
    (hq'.hasFDerivAt.fun_mul (hpart I).hasFDerivAt)).const_mul 2 |>.fun_mul hinv).fun_add
    (hb₂.hasFDerivAt.const_mul 2)
  have hG₂ := ((((hp'.hasFDerivAt.fun_mul (hqart 1).hasFDerivAt).fun_sub
    (hq'.hasFDerivAt.fun_mul (hpart 1).hasFDerivAt)).const_mul 2 |>.fun_mul hinv).fun_neg).fun_sub
    (hb₁.hasFDerivAt.const_mul 2)
  have hpcomm := (hp.isSymmSndFDerivAt (by norm_num)).eq (1 : ℂ) I
  have hqcomm := (hq.isSymmSndFDerivAt (by norm_num)).eq (1 : ℂ) I
  simp_rw [div_eq_mul_inv]
  rw [hG₁.fderiv, hG₂.fderiv]
  simp only [Fin.isValue, Nat.add_one_sub_one, pow_one, nsmul_eq_mul, Nat.cast_ofNat, smul_add,
    neg_smul, smul_neg, fderiv_clm_apply hdq (differentiableAt_const _), fderiv_fun_const,
    Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    fderiv_clm_apply hdp (differentiableAt_const _), add_apply, neg_apply, smul_apply, smul_eq_mul,
    sub_apply, ContinuousLinearMap.flip_apply, neg_add_rev, neg_neg, equation_apply_zero]
  rw [hpcomm, hqcomm]
  field_simp
  ring

/-- The scalar equation of a plane vortex: if `x` solves the vortex equation near a point `z`
where `α ≠ 0`, then `Δ (log |α|²) = (|α|² - 1) / 4` at `z`. -/
theorem laplacian_log_normSq_of_equation_eq_zero {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hb₁ : DifferentiableAt ℝ (fun w ↦ x w 0) z) (hb₂ : DifferentiableAt ℝ (fun w ↦ x w 1) z)
    (hp : ContDiffAt ℝ 2 (fun w ↦ x w 2) z) (hq : ContDiffAt ℝ 2 (fun w ↦ x w 3) z)
    (hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0) (hsol : ∀ᶠ w in 𝓝 z, equation x w = 0) :
    Δ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z =
      (4 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 4 := by
  rw [laplacian_log_normSq hb₁ hb₂ hp hq hα (hsol.mono fun w hw ↦ by simp [hw]),
    hsol.self_of_nhds]
  simp

/-- A vortex on the whole plane whose section satisfies `|α| → 1` at infinity has `|α| ≤ 1`
everywhere. -/
theorem normSq_le_one_of_tendsto {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) (z : ℂ) :
    4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ 1 := by
  by_contra! h
  have hc : Continuous fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    continuous_const.mul ((hp.continuous.pow 2).add (hq.continuous.pow 2))
  obtain ⟨z₁, hz₁⟩ := hc.exists_forall_ge' z
    ((hlim.eventually (gt_mem_nhds h)).mono fun _ hw ↦ hw.le)
  have h₁ : 1 < 4 * (x z₁ 2 ^ 2 + x z₁ 3 ^ 2) := h.trans_le (hz₁ z)
  have hα : x z₁ 2 ^ 2 + x z₁ 3 ^ 2 ≠ 0 := fun h₀ ↦ by simp [h₀] at h₁; linarith
  have hmax : IsLocalMax (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z₁ :=
    (hc.continuousAt.eventually (lt_mem_nhds (zero_lt_one.trans h₁))).mono
      fun w hw ↦ Real.log_le_log hw (hz₁ w)
  refine not_isLocalMax_of_laplacian_pos ?_ ?_ hmax
  · exact (contDiffAt_const.mul ((hp.contDiffAt.pow 2).add (hq.contDiffAt.pow 2))).log
      (mul_ne_zero four_ne_zero hα)
  · rw [laplacian_log_normSq_of_equation_eq_zero hb₁.differentiableAt hb₂.differentiableAt
      hp.contDiffAt hq.contDiffAt hα (Eventually.of_forall hsol)]
    linarith

end TauCeti.Vortex
