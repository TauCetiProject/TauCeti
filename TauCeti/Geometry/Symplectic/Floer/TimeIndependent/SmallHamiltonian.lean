/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.IntervalIntegral.Slice
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Convex.BddAbove
import TauCeti.Analysis.Fourier.Wirtinger
import TauCeti.Analysis.InnerProductSpace.CompleteSquare
import TauCeti.Geometry.Symplectic.CompatibleMetric

/-!
# Floer cylinders of small autonomous Hamiltonians are time-independent

Let `(V, ω)` be a symplectic vector space whose inner product is the metric `g = ω(·, J ·)` of a
constant compatible almost complex structure `J`, and let `H : V → ℝ` be an autonomous
Hamiltonian. For the cylindrical perturbation `K = H dt` the Floer equation reads
`∂s u + J (∂t u - X_H(u)) = 0`. Its solutions that do not depend on `t` are the gradient lines of
`H` (`TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Basic`). This file proves a converse: a
solution of period one in `t` whose derivative is small relative to the Hamiltonian is independent
of `t`, and so is a gradient line. This is the analytic step behind the identification of the
Floer cylinders of a small Morse Hamiltonian with its gradient trajectories.

The smallness condition couples `H` and the solution. If `H` is `C³` with `‖dX_H‖ ≤ a < 2π` and
`‖d²X_H‖ ≤ c` everywhere, `u` is `C³`, and `‖du‖ ≤ M` with `c M < 2 (2π - a)²`, then
`u(s, t) = u(s, 0)`
(`TauCeti.SymplecticForm.eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv`), and
`γ(s) = u(s, 0)` solves `γ' = ∇H(γ)`
(`TauCeti.SymplecticForm.hasDerivAt_gradient_of_isComplexLinearMap_perturbedFDeriv`). No finite
energy, limits at the ends or nondegeneracy are assumed.

**The argument.** Differentiating the Floer equation in `t`, the derivative `ξ = ∂t u` solves
the linearized equation `∂s ξ = -J ∂t ξ + S ξ` with `S = J dX_H(u)`. Since `J X_H` is the
gradient of `H`, the operator `S` is the Hessian of `H` along `u`, so it is symmetric, and `J` is
skew-adjoint. Each slice `t ↦ ξ(s, t)` is the derivative of a loop, so it has mean zero. The
slice energy `f(s) = ∫₀¹ ‖ξ(s, t)‖² dt` then satisfies

`f'' = 4 ∫₀¹ ‖∂s ξ‖² + 2 ∫₀¹ ⟪ξ, (∂s S) ξ⟫`,

after an integration by parts in `t` whose boundary terms cancel by periodicity. Wirtinger's
inequality on the mean-zero slices (`TauCeti.integral_norm_sub_average_sq_le`, with its sharp
constant `2π`) bounds `∫₀¹ ‖∂s ξ‖² = ∫₀¹ ‖∂t ξ - dX_H(u) ξ‖²` below by `(2π - a)² f`, and
`‖∂s S‖ ≤ c M`. Hence `f'' ≥ (4 (2π - a)² - 2 c M) f` with a positive constant. A nonnegative
bounded function with `f'' ≥ κ f`, `κ > 0`, is convex and bounded, hence zero
(`TauCeti.eq_zero_of_hasDerivAt_of_mul_le_of_bddAbove`). So `ξ = 0`.

The constant structure `J` covers flat targets. On a torus `V / Λ` with a flat compatible
structure, a Floer cylinder whose loops are contractible lifts to a solution on `V` of period one
in `t`, for the lifted `Λ`-periodic Hamiltonian. Domain- or target-dependent structures, for which
the linearized operator acquires derivatives of `J`, and the bound on `du` in terms of `H` are not
treated here.

## References

* A. Floer, *Witten's complex and infinite dimensional Morse theory*, J. Differential Geom.
  **30** (1989), 207–221.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360.
-/

public section

open Real Set Filter Topology MeasureTheory
open scoped Gradient RealInnerProductSpace

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : V → ℝ} {u : ℝ × ℝ → V}

section Derivatives

/-- Applying the constant structure `J` commutes with differentiation. -/
private theorem hasFDerivAt_apply {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : W → V} {f' : W →L[ℝ] V} {z : W} (hf : HasFDerivAt f f' z) :
    HasFDerivAt (fun y ↦ J (f y)) (J.toLinearMap.toContinuousLinearMap.comp f') z :=
  J.toLinearMap.toContinuousLinearMap.hasFDerivAt.comp z hf

/-- The Floer equation of `K = H dt`, solved for `∂s u`. -/
private theorem fderiv_apply_real_eq {z : ℝ × ℝ}
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) u z : ℝ × ℝ →ₗ[ℝ] V)) :
    fderiv ℝ u z (1, 0) = -J (fderiv ℝ u z (0, 1)) + J (ω.hamiltonianVectorField H (u z)) := by
  rw [ω.isComplexLinearMap_perturbedFDeriv_iff] at hfl
  simp only [hamiltonianVectorField_const, Pi.zero_apply, sub_zero, stdComplexLineReal_eq,
    stdComplexLineImag_eq, map_sub] at hfl
  linear_combination (norm := module) hfl

/-- **The linearized equation of `∂t u`.** For a solution `u` of the Floer equation of `K = H dt`,
the derivative `ξ = ∂t u` solves `∂s ξ + J ∂t ξ - J dX_H(u) ξ = 0`. -/
private theorem fderiv_imag_apply_real (hH : ContDiff ℝ 2 H) (hu : ContDiff ℝ 2 u)
    (hfl : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) u z : ℝ × ℝ →ₗ[ℝ] V)) (z : ℝ × ℝ) :
    fderiv ℝ (fun y ↦ fderiv ℝ u y (0, 1)) z (1, 0) =
      -J (fderiv ℝ (fun y ↦ fderiv ℝ u y (0, 1)) z (0, 1)) +
        J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (fderiv ℝ u z (0, 1))) := by
  have hfun : (fun y ↦ fderiv ℝ u y (1, 0)) =
      fun y ↦ -J (fderiv ℝ u y (0, 1)) + J (ω.hamiltonianVectorField H (u y)) :=
    funext fun y ↦ fderiv_apply_real_eq (hfl y)
  rw [fderiv_fderiv_apply_comm hu.contDiffAt
    (by norm_num [minSmoothness_of_isRCLikeNormedField]), hfun]
  have hξ : DifferentiableAt ℝ (fun y ↦ fderiv ℝ u y (0, 1)) z :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      one_ne_zero z
  have hX : DifferentiableAt ℝ (ω.hamiltonianVectorField H) (u z) :=
    (ω.contDiff_hamiltonianVectorField (n := 1) hH).differentiable one_ne_zero _
  have h : HasFDerivAt
      (fun y ↦ -J (fderiv ℝ u y (0, 1)) + J (ω.hamiltonianVectorField H (u y)))
      (_ : ℝ × ℝ →L[ℝ] V) z :=
    (hasFDerivAt_apply hξ.hasFDerivAt).neg.add (hasFDerivAt_apply
      (hX.hasFDerivAt.comp z ((hu.differentiable (by norm_num)) z).hasFDerivAt))
  rw [h.fderiv]
  simp

/-- **The equation of `∂s ξ`.** If `ξ` solves `∂s ξ = -J ∂t ξ + J dX_H(u) ξ`, then `η = ∂s ξ`
solves `∂s η = -J ∂t η + J (d²X_H(u)(∂s u) ξ) + J dX_H(u) η`. -/
private theorem fderiv_real_apply_real (hH : ContDiff ℝ 3 H) (hu : Differentiable ℝ u)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ)
    (hξeq : ∀ z, fderiv ℝ ξ z (1, 0) =
      -J (fderiv ℝ ξ z (0, 1)) + J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)))
    (z : ℝ × ℝ) :
    fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) z (1, 0) =
      -J (fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) z (0, 1)) +
        J (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) (u z) (fderiv ℝ u z (1, 0)) (ξ z)) +
        J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (fderiv ℝ ξ z (1, 0))) := by
  rw [fderiv_fderiv_apply_comm hξ.contDiffAt
    (by norm_num [minSmoothness_of_isRCLikeNormedField]) (1, 0) (0, 1)]
  conv_lhs => rw [funext hξeq]
  set dX := fderiv ℝ (ω.hamiltonianVectorField H)
  have hdξ : DifferentiableAt ℝ (fun y ↦ fderiv ℝ ξ y (0, 1)) z :=
    ((hξ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      one_ne_zero z
  have hdX : DifferentiableAt ℝ dX (u z) :=
    ((ω.contDiff_hamiltonianVectorField (n := 2) hH).fderiv_right (m := 1)
      (by norm_num)).differentiable one_ne_zero _
  have h : HasFDerivAt (fun y ↦ -J (fderiv ℝ ξ y (0, 1)) + J (dX (u y) (ξ y)))
      (_ : ℝ × ℝ →L[ℝ] V) z :=
    (hasFDerivAt_apply hdξ.hasFDerivAt).neg.add
      (hasFDerivAt_apply ((hdX.hasFDerivAt.comp z (hu z).hasFDerivAt).clm_apply
        ((hξ.differentiable (by norm_num)) z).hasFDerivAt))
  rw [h.fderiv]
  simp only [add_apply, neg_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply, LinearMap.coe_toContinuousLinearMap', map_add]
  abel

end Derivatives

section Slice

variable {ξ : ℝ × ℝ → V}

/-- **The lower bound for `∂s ξ`.** If `ξ` solves `∂s ξ = -J ∂t ξ + J dX_H(u) ξ`, with `ξ` of
period one in `t` and mean zero on every slice, and `‖dX_H‖ ≤ a ≤ 2π`, then
`(2π - a)² ∫₀¹ ‖ξ(s, t)‖² dt ≤ ∫₀¹ ‖∂s ξ(s, t)‖² dt`. -/
private theorem mul_integral_norm_sq_slice_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {a : ℝ}
    (ha0 : 0 ≤ a) (ha2π : a ≤ 2 * π)
    (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a) (hξ : ContDiff ℝ 1 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (hmean : ∀ s, ∫ t in (0 : ℝ)..1, ξ (s, t) = 0)
    (hξeq : ∀ z, fderiv ℝ ξ z (1, 0) =
      -J (fderiv ℝ ξ z (0, 1)) + J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)))
    (s : ℝ) :
    (2 * π - a) ^ 2 * ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2 := by
  -- Pointwise, `∂s ξ = -J (∂t ξ - dX_H(u) ξ)` with `‖dX_H(u) ξ‖ ≤ a ‖ξ‖`.
  have hpt (t : ℝ) : (1 - a / (2 * π)) * ‖fderiv ℝ ξ (s, t) (0, 1)‖ ^ 2 -
      (2 * π - a) * a * ‖ξ (s, t)‖ ^ 2 ≤ ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2 := by
    have he : fderiv ℝ ξ (s, t) (1, 0) = -J (fderiv ℝ ξ (s, t) (0, 1) -
        fderiv ℝ (ω.hamiltonianVectorField H) (u (s, t)) (ξ (s, t))) := by
      rw [hξeq, map_sub]
      abel
    rw [he, norm_neg, ω.norm_apply_eq_norm_of_apply_apply_self_eq_inner fun v ↦ hg v v]
    exact one_sub_div_mul_norm_sq_sub_le_norm_sub_sq ha0 ha2π
      (((fderiv ℝ (ω.hamiltonianVectorField H) (u (s, t))).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (ha _) (norm_nonneg _)))
  have hc₁ := ((continuous_fderiv_apply_slice_right hξ s (0, 1)).norm.pow 2).intervalIntegrable
    (μ := volume) 0 1
  have hc₂ := ((continuous_fderiv_apply_slice_right hξ s (1, 0)).norm.pow 2).intervalIntegrable
    (μ := volume) 0 1
  have hcξ : Continuous fun t ↦ ξ (s, t) := hξ.continuous.comp (.prodMk_right s)
  have hc₀ := (hcξ.norm.pow 2).intervalIntegrable (μ := volume) 0 1
  have hint := intervalIntegral.integral_mono_on zero_le_one
    ((hc₁.const_mul _).sub (hc₀.const_mul _)) hc₂ fun t _ ↦ hpt t
  rw [intervalIntegral.integral_sub (hc₁.const_mul _) (hc₀.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  simp only [Pi.pow_apply] at hint
  -- Wirtinger: `(2π)² ∫ ‖ξ‖² ≤ ∫ ‖∂t ξ‖²`.
  have hπ : 0 < 2 * π := by positivity
  have hW : (2 * π) ^ 2 * ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ‖fderiv ℝ ξ (s, t) (0, 1)‖ ^ 2 := by
    have h := integral_norm_sq_le_of_integral_eq_zero zero_lt_one
      (fun t ↦ hasDerivAt_slice_right (hξ.differentiable one_ne_zero (s, t)))
      (continuous_fderiv_apply_slice_right hξ s (0, 1)) (by simpa using (hper s 0).symm) (hmean s)
    rw [sub_zero] at h
    rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at h
    linarith
  have hcoef : 0 ≤ 1 - a / (2 * π) := by
    rw [sub_nonneg, div_le_one hπ]
    exact ha2π
  have hmul := mul_le_mul_of_nonneg_left hW hcoef
  have hid : (1 - a / (2 * π)) * (2 * π) ^ 2 = (2 * π - a) * (2 * π) := by
    field_simp
  rw [← mul_assoc, hid] at hmul
  linarith

/-- The integrand `t ↦ ⟪ξ, J (d²X_H(u)(∂s u) ξ)⟫` of the curvature term is continuous. -/
private theorem continuous_inner_apply_fderiv_fderiv_hamiltonianVectorField (hH : ContDiff ℝ 3 H)
    (hu : ContDiff ℝ 1 u) (hξ : ContDiff ℝ 1 ξ) (s : ℝ) :
    Continuous fun t ↦ ⟪ξ (s, t), J (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H))
      (u (s, t)) (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t)))⟫ := by
  have hd2X : Continuous (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H))) :=
    ((ω.contDiff_hamiltonianVectorField (n := 2) hH).fderiv_right (m := 1)
      (by norm_num)).continuous_fderiv one_ne_zero
  have hcξ : Continuous fun t ↦ ξ (s, t) := hξ.continuous.comp (.prodMk_right s)
  exact hcξ.inner (J.toLinearMap.toContinuousLinearMap.continuous.comp
    (((hd2X.comp (hu.continuous.comp (.prodMk_right s))).clm_apply
      (continuous_fderiv_apply_slice_right hu s (1, 0))).clm_apply hcξ))

/-- **The bound for the curvature of `dX_H` along `u`.** If `‖d²X_H‖ ≤ c` and `‖du‖ ≤ M`, then
`-c M ∫₀¹ ‖ξ‖² ≤ ∫₀¹ ⟪ξ, J (d²X_H(u)(∂s u) ξ)⟫`. -/
private theorem neg_mul_integral_norm_sq_slice_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {c M : ℝ}
    (hH : ContDiff ℝ 3 H)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (hu : ContDiff ℝ 1 u) (hM : ∀ z, ‖fderiv ℝ u z‖ ≤ M) (hξ : ContDiff ℝ 1 ξ) (s : ℝ) :
    -(c * M) * ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ⟪ξ (s, t), J (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H))
        (u (s, t)) (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t)))⟫ := by
  have hc0 : 0 ≤ c :=
    (norm_nonneg (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) 0)).trans (hc 0)
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on zero_le_one
    ((((hξ.continuous.comp (.prodMk_right s)).norm.pow 2).intervalIntegrable
      (μ := volume) 0 1).const_mul _)
    ((continuous_inner_apply_fderiv_fderiv_hamiltonianVectorField hH hu hξ s).intervalIntegrable
      0 1) fun t _ ↦ ?_
  set L := fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) (u (s, t))
  have hus : ‖fderiv ℝ u (s, t) (1, 0)‖ ≤ M :=
    ((fderiv ℝ u (s, t)).le_opNorm _).trans (by simpa using hM (s, t))
  have hLξ : ‖L (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t))‖ ≤ c * M * ‖ξ (s, t)‖ :=
    ((L _).le_opNorm _).trans (mul_le_mul_of_nonneg_right ((L.le_opNorm _).trans
      (mul_le_mul (hc _) hus (norm_nonneg _) hc0)) (norm_nonneg _))
  have hin := neg_le_of_abs_le (abs_real_inner_le_norm (ξ (s, t))
    (J (L (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t)))))
  rw [ω.norm_apply_eq_norm_of_apply_apply_self_eq_inner fun v ↦ hg v v] at hin
  nlinarith [mul_le_mul_of_nonneg_left hLξ (norm_nonneg (ξ (s, t)))]

/-- **The pointwise identity behind the second variation of the slice energy.** If `ξ` solves
`∂s ξ = -J ∂t ξ + J dX_H(u) ξ`, then, with `η = ∂s ξ`,
`⟪ξ, ∂s η⟫ + ‖η‖² = 2 ‖η‖² + ⟪ξ, J (d²X_H(u)(∂s u) ξ)⟫ + ∂t ⟪J ξ, η⟫`. This is where the
symmetry of `J dX_H(u)` and the skew-adjointness of `J` enter. -/
private theorem inner_fderiv_real_real_add_norm_sq_eq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (hu : Differentiable ℝ u) (hξ : ContDiff ℝ 2 ξ)
    (hξeq : ∀ z, fderiv ℝ ξ z (1, 0) =
      -J (fderiv ℝ ξ z (0, 1)) + J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)))
    (z : ℝ × ℝ) :
    ⟪ξ z, fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) z (1, 0)⟫ + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 =
      2 * ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ⟪ξ z, J (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H))
        (u z) (fderiv ℝ u z (1, 0)) (ξ z))⟫ +
        fderiv ℝ (fun y ↦ ⟪J (ξ y), fderiv ℝ ξ y (1, 0)⟫) z (0, 1) := by
  set η : ℝ × ℝ → V := fun y ↦ fderiv ℝ ξ y (1, 0)
  have hη : ContDiff ℝ 1 η := (hξ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hdξ : DifferentiableAt ℝ ξ z := (hξ.differentiable (by norm_num)) z
  have hdJξ : HasFDerivAt (fun y ↦ J (ξ y)) (_ : ℝ × ℝ →L[ℝ] V) z :=
    hasFDerivAt_apply hdξ.hasFDerivAt
  rw [fderiv_inner_apply ℝ hdJξ.differentiableAt (hη.differentiable one_ne_zero z),
    hdJξ.fderiv, fderiv_real_apply_real hH hu hξ hξeq z]
  have hsym : ⟪J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)), η z⟫ =
      ⟪ξ z, J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (η z))⟫ := by
    have h := (ω.invariant_of_apply_apply_eq_inner hg)
      |>.associatedBilinForm_apply_fderiv_hamiltonianVectorField_comm (x := u z)
        (hH.contDiffAt.of_le (by norm_num)) (ξ z) (η z)
    simpa only [associatedBilinForm_apply, hg] using h
  have hskew := inner_apply_left_eq_neg_of_apply_apply_eq_inner hg (ξ z) (fderiv ℝ η z (0, 1))
  have hηeq : η z = -J (fderiv ℝ ξ z (0, 1)) +
      J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)) := hξeq z
  have hnorm : ‖η z‖ ^ 2 = ⟪-J (fderiv ℝ ξ z (0, 1)) +
      J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)), η z⟫ := by
    rw [← hηeq, real_inner_self_eq_norm_sq]
  simp only [inner_add_right, inner_add_left, inner_neg_left, inner_neg_right,
    ContinuousLinearMap.coe_comp, Function.comp_apply, LinearMap.coe_toContinuousLinearMap']
    at hnorm ⊢
  linarith

/-- **The second variation of the slice energy.** If `ξ` solves `∂s ξ = -J ∂t ξ + J dX_H(u) ξ`
and has period one in `t`, then, with `η = ∂s ξ`,
`∫₀¹ (⟪ξ, ∂s η⟫ + ‖η‖²) = 2 ∫₀¹ ‖η‖² + ∫₀¹ ⟪ξ, J (d²X_H(u)(∂s u) ξ)⟫`. The difference of the
integrands is the `t`-derivative of `⟪J ξ, η⟫`, which integrates to zero over a period. -/
private theorem integral_inner_fderiv_slice_eq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (hu : ContDiff ℝ 1 u) (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    (hξeq : ∀ z, fderiv ℝ ξ z (1, 0) =
      -J (fderiv ℝ ξ z (0, 1)) + J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)))
    (s : ℝ) :
    ∫ t in (0 : ℝ)..1, (⟪ξ (s, t), fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) (s, t) (1, 0)⟫ +
        ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2) =
      2 * (∫ t in (0 : ℝ)..1, ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2) +
        ∫ t in (0 : ℝ)..1, ⟪ξ (s, t), J (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H))
          (u (s, t)) (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t)))⟫ := by
  set η : ℝ × ℝ → V := fun y ↦ fderiv ℝ ξ y (1, 0)
  have hξ1 : ContDiff ℝ 1 ξ := hξ.of_le (by norm_num)
  have hη : ContDiff ℝ 1 η := (hξ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  -- The boundary term `⟪J ξ, η⟫` has period one in `t`, so its `t`-derivative integrates to zero.
  have hB : ContDiff ℝ 1 fun y ↦ ⟪J (ξ y), η y⟫ :=
    (J.toLinearMap.toContinuousLinearMap.contDiff.comp hξ1).inner ℝ hη
  have hB0 := integral_fderiv_apply_zero_one_eq_zero hB (T := 1)
    (fun s t ↦ by simp only [η, hper, fderiv_add_snd_of_periodic_snd hper]) s
  have hA₁ : Continuous fun t ↦ ‖η (s, t)‖ ^ 2 :=
    (hη.continuous.comp (.prodMk_right s)).norm.pow 2
  have hA₂ := continuous_inner_apply_fderiv_fderiv_hamiltonianVectorField hH hu hξ1 s
    (ω := ω) (J := J)
  rw [intervalIntegral.integral_congr fun t _ ↦
      inner_fderiv_real_real_add_norm_sq_eq hg hH (hu.differentiable one_ne_zero) hξ hξeq (s, t),
    intervalIntegral.integral_add (((hA₁.intervalIntegrable (μ := volume) 0 1).const_mul 2).add
      (hA₂.intervalIntegrable 0 1))
      ((continuous_fderiv_apply_slice_right hB s (0, 1)).intervalIntegrable 0 1), hB0, add_zero,
    intervalIntegral.integral_add ((hA₁.intervalIntegrable 0 1).const_mul 2)
      (hA₂.intervalIntegrable 0 1), intervalIntegral.integral_const_mul]

/-- **Bounded solutions of the linearized equation with mean-zero slices vanish.** Let `ξ` be a
bounded `C²` solution of `∂s ξ = -J ∂t ξ + J dX_H(u) ξ`, of period one in `t`, whose slices
`t ↦ ξ(s, t)` have mean zero. If `‖dX_H‖ ≤ a < 2π`, `‖d²X_H‖ ≤ c`, `‖du‖ ≤ M` and
`c M < 2 (2π - a)²`, then `ξ = 0`. -/
private theorem eq_zero_of_fderiv_apply_real_eq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {a c M B : ℝ}
    (hH : ContDiff ℝ 3 H) (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (ha2π : a < 2 * π) (hcM : c * M < 2 * (2 * π - a) ^ 2)
    (hu : ContDiff ℝ 1 u) (hM : ∀ z, ‖fderiv ℝ u z‖ ≤ M) (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (hmean : ∀ s, ∫ t in (0 : ℝ)..1, ξ (s, t) = 0)
    (hξeq : ∀ z, fderiv ℝ ξ z (1, 0) =
      -J (fderiv ℝ ξ z (0, 1)) + J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)))
    (hB : ∀ z, ‖ξ z‖ ≤ B) (z : ℝ × ℝ) : ξ z = 0 := by
  have hξ1 : ContDiff ℝ 1 ξ := hξ.of_le (by norm_num)
  have ha0 : 0 ≤ a := (norm_nonneg (fderiv ℝ (ω.hamiltonianVectorField H) 0)).trans (ha 0)
  -- The slice energy `f` satisfies `f'' ≥ κ f` with `κ = 4 (2π - a)² - 2 c M > 0`.
  set f : ℝ → ℝ := fun s ↦ ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2 with hf_def
  have hle (s : ℝ) : (4 * (2 * π - a) ^ 2 - 2 * (c * M)) * f s ≤
      ∫ t in (0 : ℝ)..1, 2 * (⟪ξ (s, t), fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) (s, t) (1, 0)⟫ +
        ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2) := by
    rw [intervalIntegral.integral_const_mul,
      integral_inner_fderiv_slice_eq hg hH hu hξ hper hξeq s]
    have h₁ := mul_integral_norm_sq_slice_le hg ha0 ha2π.le ha hξ1 hper hmean hξeq s
    have h₂ := neg_mul_integral_norm_sq_slice_le hg hH hc hu hM hξ1 s
    simp only [hf_def]
    linarith
  have hf0 (s : ℝ) : 0 ≤ f s :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ ↦ sq_nonneg _
  have hcont (s : ℝ) : Continuous fun t ↦ ‖ξ (s, t)‖ ^ 2 :=
    (hξ.continuous.comp (.prodMk_right s)).norm.pow 2
  have hfb : BddAbove (range f) := ⟨B ^ 2, by
    rintro _ ⟨s, rfl⟩
    have h := intervalIntegral.integral_mono_on (g := fun _ ↦ B ^ 2) zero_le_one
      ((hcont s).intervalIntegrable (μ := volume) 0 1) intervalIntegrable_const
      fun t _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hB (s, t)) 2
    simpa using h⟩
  have hfz := eq_zero_of_hasDerivAt_of_mul_le_of_bddAbove (by nlinarith)
    (hasDerivAt_intervalIntegral_norm_sq hξ1 0 1)
    (hasDerivAt_intervalIntegral_two_mul_inner_fderiv hξ 0 1) hle hf0 hfb
  -- A continuous slice with vanishing `L²` norm vanishes on `(0, 1]`, hence everywhere.
  obtain ⟨s, t⟩ := z
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
    (Eventually.of_forall fun t ↦ sq_nonneg ‖ξ (s, t)‖)
    ((hcont s).intervalIntegrable (μ := volume) 0 1)).1 (hfz s)
  have hIoc := Measure.eqOn_Ioc_of_ae_eq volume hae (hcont s).continuousOn continuousOn_const
  have hpers : Function.Periodic (fun t ↦ ξ (s, t)) 1 := hper s
  obtain ⟨t', ht', hξt⟩ := hpers.exists_mem_Ioc zero_lt_one t 0
  rw [zero_add] at ht'
  simpa [hξt] using hIoc ht'

end Slice

section Main

variable {a c M : ℝ}

/-- **Floer cylinders of a small autonomous Hamiltonian are time-independent.** Let the inner
product of `V` be the metric `ω(·, J ·)` of a constant compatible almost complex structure `J`,
and let `H` be a `C³` autonomous Hamiltonian with `‖dX_H‖ ≤ a < 2π` and `‖d²X_H‖ ≤ c`. Let `u` be
a `C³` solution of the Floer equation `∂s u + J (∂t u - X_H(u)) = 0` of `K = H dt`, of period one
in `t`, with `‖du‖ ≤ M`. If `c M < 2 (2π - a)²`, then `u` does not depend on `t`:
`u(s, t) = u(s, 0)`. -/
theorem eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (ha2π : a < 2 * π) (hcM : c * M < 2 * (2 * π - a) ^ 2)
    (hu : ContDiff ℝ 3 u) (hper : ∀ s t, u (s, t + 1) = u (s, t))
    (hfl : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hM : ∀ z, ‖fderiv ℝ u z‖ ≤ M) :
    u = fun z ↦ u (z.1, 0) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  -- `ξ = ∂t u` is a bounded solution of the linearized equation with mean-zero slices.
  set ξ : ℝ × ℝ → V := fun y ↦ fderiv ℝ u y (0, 1)
  have hξ : ContDiff ℝ 2 ξ := (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hξper (s t : ℝ) : ξ (s, t + 1) = ξ (s, t) := by
    simp only [ξ, fderiv_add_snd_of_periodic_snd hper]
  have hB (z : ℝ × ℝ) : ‖ξ z‖ ≤ M :=
    ((fderiv ℝ u z).le_opNorm _).trans (by simpa using hM z)
  have hzero := eq_zero_of_fderiv_apply_real_eq hg hH ha hc ha2π hcM hu1 hM hξ hξper
    (integral_fderiv_apply_zero_one_eq_zero hu1 hper)
    (fderiv_imag_apply_real (hH.of_le (by norm_num)) (hu.of_le (by norm_num)) hfl) hB
  -- So every slice `t ↦ u(s, t)` has vanishing derivative.
  funext ⟨s, t⟩
  have hd (t : ℝ) : HasDerivAt (fun t ↦ u (s, t)) 0 t := by
    simpa [ξ, hzero (s, t)] using hasDerivAt_slice_right (hu1.differentiable one_ne_zero (s, t))
  exact is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt) (fun t ↦ (hd t).deriv) t 0

/-- **Floer cylinders of a small autonomous Hamiltonian are gradient lines.** Under the hypotheses
of `TauCeti.SymplecticForm.eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv`, the curve
`γ(s) = u(s, 0)` is an upward gradient line of `H`, `γ' = ∇H(γ)`, for the metric `ω(·, J ·)`. That
`u(s, t) = γ(s)` is `TauCeti.SymplecticForm.eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv`. -/
theorem hasDerivAt_gradient_of_isComplexLinearMap_perturbedFDeriv
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hH : ContDiff ℝ 3 H)
    (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (ha2π : a < 2 * π) (hcM : c * M < 2 * (2 * π - a) ^ 2)
    (hu : ContDiff ℝ 3 u) (hper : ∀ s t, u (s, t + 1) = u (s, t))
    (hfl : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hM : ∀ z, ‖fderiv ℝ u z‖ ≤ M) (s : ℝ) :
    HasDerivAt (fun s ↦ u (s, 0)) (∇ H (u (s, 0))) s := by
  have hmain := eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv hg hH ha hc ha2π hcM hu hper
    hfl hM
  have hγ : Differentiable ℝ fun s ↦ u (s, 0) :=
    (hu.differentiable (by norm_num)).comp (differentiable_id.prodMk (differentiable_const 0))
  have h := hfl (s, 0)
  rw [hmain] at h
  have hgrad := (Invariant.isComplexLinearMap_perturbedFDeriv_comp_fst_iff
    (ω.invariant_of_apply_apply_eq_inner hg) (γ := fun s ↦ u (s, 0)) (z := (s, 0)) (hγ s)).1 h
  have hd : deriv (fun s ↦ u (s, 0)) s = ∇ H (u (s, 0)) := ext_inner_right ℝ fun w ↦ by
    rw [inner_gradient_left, ← hg, ← associatedBilinForm_apply]
    exact hgrad w
  exact hd ▸ (hγ s).hasDerivAt

end Main

end TauCeti.SymplecticForm
