/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.MeanValueInequality
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.Varying

/-!
# The mean-value inequality for `J`-holomorphic curves and linear Cauchy–Riemann equations

Let `V` be a real inner product space and `J : V → (V →L[ℝ] V)` a `C²` family of linear maps with
`J(x)² = -1`, an almost complex structure on `V` written as a matrix-valued function, as in local
coordinates on an almost complex manifold. A map `u : ℂ → V`, with `s + i t` the coordinate on
`ℂ`, is `J`-holomorphic when it solves the Cauchy--Riemann equation `∂ₛu + J(u) ∂ₜu = 0`, that is
`∂ₜu = J(u) ∂ₛu`. Here `∂ₛu = du(1)` and `∂ₜu = du(i)` are written `fderiv ℝ u y 1` and
`fderiv ℝ u y I`. Since `J(u)² = -1`, this single equation says that `du` intertwines
multiplication by `i` with `J(u)`; a curve that is `TauCeti.IsJHolomorphicAt` for the standard
complex structure of `ℂ` satisfies it (`TauCeti.IsJHolomorphicAt.fderiv_I_eq`).

The energy density `‖∂ₛu‖²` of such a curve satisfies the differential inequality

`Δ ‖∂ₛu‖² ≥ -A ‖∂ₛu‖⁴`,

with `A = 4ac + 2b² + 8a²b²` whenever `a`, `b`, `c` bound `J`, its first derivative and its
second derivative along `u`. Differentiating the Cauchy--Riemann equation twice and using
`J(u)² = -1` removes the third derivatives of `u` from `Δ ∂ₛu`. What remains is bounded by
`‖∂ₛu‖³` and by `‖∂ₛu‖` times the second derivatives of `u`, and the positive term
`2 ‖∇ ∂ₛu‖²` in `Δ ‖∂ₛu‖²` absorbs the latter. For constant `J` the constant `A` vanishes and
`‖∂ₛu‖²` is subharmonic.

Fed into the two-dimensional mean-value inequality
`TauCeti.mul_le_eight_mul_setIntegral_ball_of_neg_mul_sq_le_laplacian`, this gives the
pointwise derivative bound for curves of small energy, the basic estimate behind bubbling and
Gromov compactness: if `8 A ∫_{B_r(z₀)} ‖∂ₛu‖² < π`, then

`π r² ‖∂ₛu(z₀)‖² ≤ 8 ∫_{B_r(z₀)} ‖∂ₛu‖²`.

For `J` that is `C²` on an open set containing a compact set `K`, one smallness threshold `δ > 0`
works for all curves with image in `K`. The threshold depends only on bounds for `J` and its first
two derivatives on `K`, so it is also uniform over a family of structures `J p` depending `C²` on a
parameter `p` in a compact set, such as the structures `J(z₀, ·)` frozen at the points `z₀` of a
compact window of the domain of an inhomogeneous equation. As `∂ₜu = J(u) ∂ₛu`, these bounds
control the full derivative of `u`.

**Curves in a target with a translation symmetry.** Suppose that `J` is invariant under the
translations along a vector `e₀`, so that `x ↦ x + τ e₀` maps solutions to solutions. Then the
derivatives of `J` vanish on `e₀`, and in the formula for `Δ ∂ₛu` every term contains either
`∂ₛu - e₀` or a second derivative of `u`. So `ζ = ∂ₛu - e₀` satisfies the *linear* inequality

`Δ ‖ζ‖² ≥ -A m² ‖ζ‖²`

wherever `m` bounds `‖∂ₛu‖` and `‖ζ‖`, with the same `A = 4ac + 2b² + 8a²b²`. Every `J` is
invariant along `e₀ = 0`, and with `m = ‖∂ₛu‖` this specializes to `Δ ‖∂ₛu‖² ≥ -A ‖∂ₛu‖⁴`. By
`TauCeti.mul_le_fifteen_mul_setIntegral_ball_of_neg_mul_le_laplacian`, on discs of radius
`r` with `16 A m² r² ≤ 1` this gives `π r² ‖ζ(z₀)‖² ≤ 15 ∫_{B_r(z₀)} ‖ζ‖²`, with no smallness
condition on the integral. The typical case is the graph `z ↦ (z, u z)` of a solution `u` of an
inhomogeneous Cauchy--Riemann equation whose data do not depend on `re z`, such as a Floer
trajectory: there `e₀ = (1, 0)`, `ζ = (0, ∂ₛu)`, and the inequality bounds `∂ₛu` pointwise by its
`L²` norm on a disc of fixed radius.

**Linear equations.** For a solution `v` of a linear Cauchy–Riemann equation
`∂ₜv = J ∂ₛv + B v`, with coefficient families `J`, `B : ℂ → End V` and `J² = -1`, the same
computation needs only one derivative of the equation. The second derivatives of `v` cancel in
`Δ v`, and `Δ ‖v‖² ≥ -K ‖v‖²` with `K` depending on bounds for `J`, `B` and their first
derivatives (`TauCeti.neg_mul_norm_sq_le_laplacian_of_fderiv_I_eq`). The right-hand side is
linear in `‖v‖²`, so the mean-value inequality holds on every disc with `16 K r² ≤ 1`, whatever
the integral (`TauCeti.pi_mul_sq_mul_norm_sq_le_fifteen_mul_setIntegral_ball_of_fderiv_I_eq`).
The `s`-derivative of a Floer cylinder solves such an equation.

## Main declarations

* `TauCeti.neg_mul_norm_fderiv_one_pow_four_le_laplacian`: the differential inequality
  `Δ ‖∂ₛu‖² ≥ -A ‖∂ₛu‖⁴` for a `J`-holomorphic curve.
* `TauCeti.pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball`: the mean-value
  inequality for `J`-holomorphic curves, with explicit constants.
* `TauCeti.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball`:
  the same with a smallness threshold that is uniform over curves with image in a compact set.
* One threshold for a compact family of structures:
  `exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball_parametric`.
* `TauCeti.exists_pos_exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_mul_setIntegral_ball`:
  the same in a finite-dimensional normed space, as for the coordinate expressions of curves in a
  chart of a manifold, with a constant depending on the norm in place of `8`; for a compact
  family of structures:
  `exists_pos_exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_mul_setIntegral_ball_parametric`
* `TauCeti.neg_mul_norm_fderiv_one_sub_sq_le_laplacian`: for `J` invariant under the translations
  along a vector `e₀`, the differential inequality `Δ ‖∂ₛu - e₀‖² ≥ -A m² ‖∂ₛu - e₀‖²`.
* `exists_nonneg_forall_pi_mul_sq_mul_norm_fderiv_one_sub_sq_le_fifteen_mul_setIntegral_ball`:
  the resulting mean-value inequality for `‖∂ₛu - e₀‖²` on discs of radius `r ≤ 1 / (4 m √A)`,
  uniformly over curves with image in a compact set.
* `TauCeti.neg_mul_norm_sq_le_laplacian_of_fderiv_I_eq`: the differential inequality
  `Δ ‖v‖² ≥ -K ‖v‖²` for a solution of a linear Cauchy–Riemann equation.
* `TauCeti.pi_mul_sq_mul_norm_sq_le_fifteen_mul_setIntegral_ball_of_fderiv_I_eq`: the mean-value
  inequality for solutions of linear Cauchy–Riemann equations.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.3 (the mean-value inequality and its
  application to the energy density of `J`-holomorphic curves).
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Filter Topology Complex Metric MeasureTheory Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable {u : ℂ → V} {J : V → V →L[ℝ] V} {z : ℂ} {e₀ : V}

/-- The Cauchy--Riemann equation `∂ₜu = J(u) ∂ₛu` differentiated twice at `z`, in the directions
`w` and then `a`. -/
private theorem fderiv_fderiv_fderiv_apply_I_eq (hu : ContDiffAt ℝ 3 u z)
    (hJ : ContDiffAt ℝ 2 J (u z)) (hCR : ∀ᶠ y in 𝓝 z, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1))
    (a w : ℂ) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ u)) z a w I =
      J (u z) (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) z a w 1) +
        fderiv ℝ (fun y ↦ J (u y)) z a (fderiv ℝ (fderiv ℝ u) z w 1) +
        fderiv ℝ (fderiv ℝ fun y ↦ J (u y)) z a w (fderiv ℝ u z 1) +
        fderiv ℝ (fun y ↦ J (u y)) z w (fderiv ℝ (fderiv ℝ u) z a 1) := by
  set g : ℂ → V →L[ℝ] V := fun y ↦ J (u y)
  have hDu : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (m := 2) (by norm_num)
  have hD2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ u)) z :=
    (hDu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg : ContDiffAt ℝ 2 g z := hJ.comp z (hu.of_le (by norm_num))
  have hDg : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- The equation differentiated once, at every point near `z`.
  have hfirst : (fun y ↦ fderiv ℝ (fderiv ℝ u) y w I) =ᶠ[𝓝 z]
      fun y ↦ g y (fderiv ℝ (fderiv ℝ u) y w 1) + fderiv ℝ g y w (fderiv ℝ u y 1) := by
    have hDu' : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 (fderiv ℝ u) y := hDu.eventually (by simp)
    have hg' : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 g y := hg.eventually (by simp)
    filter_upwards [hDu', hg', hCR.eventually_nhds] with y hy hgy hCRy
    have hξ : DifferentiableAt ℝ (fun y ↦ fderiv ℝ u y 1) y :=
      (hy.differentiableAt (by norm_num)).clm_apply (differentiableAt_const 1)
    have h := congrArg (fun L : ℂ →L[ℝ] V ↦ L w)
      (EventuallyEq.fderiv_eq (𝕜 := ℝ) (f₁ := fun y ↦ fderiv ℝ u y I)
        (f := fun y ↦ g y (fderiv ℝ u y 1)) hCRy)
    rw [fderiv_clm_apply_const_apply (hy.differentiableAt (by norm_num)),
      fderiv_clm_apply (hgy.differentiableAt (by norm_num)) hξ] at h
    simpa [fderiv_clm_apply_const_apply (hy.differentiableAt (by norm_num))] using h
  have h := congrArg (fun L : ℂ →L[ℝ] V ↦ L a) hfirst.fderiv_eq
  rw [fderiv_clm_apply (hD2.clm_apply (differentiableAt_const w)) (differentiableAt_const I),
    fderiv_fun_add (hg.differentiableAt (by norm_num) |>.clm_apply
      ((hD2.clm_apply (differentiableAt_const w)).clm_apply (differentiableAt_const 1)))
      ((hDg.clm_apply (differentiableAt_const w)).clm_apply
        ((hDu.differentiableAt (by norm_num)).clm_apply (differentiableAt_const 1))),
    fderiv_clm_apply (hg.differentiableAt (by norm_num))
      ((hD2.clm_apply (differentiableAt_const w)).clm_apply (differentiableAt_const 1)),
    fderiv_clm_apply (hDg.clm_apply (differentiableAt_const w))
      ((hDu.differentiableAt (by norm_num)).clm_apply (differentiableAt_const 1)),
    fderiv_clm_apply (hD2.clm_apply (differentiableAt_const w)) (differentiableAt_const 1)] at h
  simp only [fderiv_const_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add,
    fderiv_clm_apply_const_apply hD2, fderiv_clm_apply_const_apply hDg,
    fderiv_clm_apply_const_apply (hDu.differentiableAt (by norm_num))] at h
  rw [h]
  abel

/-- The Laplacian of `∂ₛu` for a solution of `∂ₜu = J(u) ∂ₛu` with `J(u z)² = -1`: the third
derivatives of `u` cancel, leaving an expression in `∂ₛu`, the second derivatives of `u`, and the
first and second derivatives of `J ∘ u`. -/
private theorem laplacian_fderiv_one_eq (hu : ContDiffAt ℝ 3 u z) (hJ : ContDiffAt ℝ 2 J (u z))
    (hCR : ∀ᶠ y in 𝓝 z, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1))
    (hJsq : ∀ v, J (u z) (J (u z) v) = -v) :
    Δ (fun y ↦ fderiv ℝ u y 1) z =
      (2 : ℝ) • J (u z) (fderiv ℝ (fun y ↦ J (u y)) z 1 (fderiv ℝ (fderiv ℝ u) z 1 1)) +
        J (u z) (fderiv ℝ (fderiv ℝ fun y ↦ J (u y)) z 1 1 (fderiv ℝ u z 1)) +
        fderiv ℝ (fun y ↦ J (u y)) z 1 (fderiv ℝ (fderiv ℝ u) z 1 I) +
        fderiv ℝ (fderiv ℝ fun y ↦ J (u y)) z 1 I (fderiv ℝ u z 1) +
        fderiv ℝ (fun y ↦ J (u y)) z I (fderiv ℝ (fderiv ℝ u) z 1 1) := by
  have hDu : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (m := 2) (by norm_num)
  -- The symmetries of the second and third derivatives used below.
  have hsymm₂ : fderiv ℝ (fderiv ℝ u) z I 1 = fderiv ℝ (fderiv ℝ u) z 1 I :=
    hu.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) I 1
  have hsymm₃ : fderiv ℝ (fderiv ℝ (fderiv ℝ u)) z I I 1 =
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) z 1 I I := by
    rw [fderiv_fderiv_fderiv_apply_comm hu (by simp) I I 1,
      hDu.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) I 1]
  have h₁ := fderiv_fderiv_fderiv_apply_I_eq hu hJ hCR 1 I
  have h₂ := fderiv_fderiv_fderiv_apply_I_eq hu hJ hCR 1 1
  rw [fderiv_fderiv_fderiv_apply_comm hu (by simp) 1 I 1, h₂, hsymm₂] at h₁
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [fderiv_fderiv_fderiv_apply hu, fderiv_fderiv_fderiv_apply hu, hsymm₃, h₁]
  simp only [map_add, hJsq]
  module

/-- The Laplacian of `∂ₛu` for a solution of `∂ₜu = J(u) ∂ₛu`, when `J` is invariant under the
translations along `e₀`: it is bounded by `‖∂ₛu - e₀‖` and the second derivatives `∂ₛ∂ₛu` and
`∂ₛ∂ₜu`, with constants from bounds on `J`, its first two derivatives and `∂ₛu`. -/
private theorem norm_laplacian_fderiv_one_le_of_periodic {a b c m : ℝ}
    (hJe : ∀ τ : ℝ, Function.Periodic J (τ • e₀))
    (hu : ContDiffAt ℝ 3 u z) (hJ : ContDiffAt ℝ 2 J (u z))
    (hCR : ∀ᶠ y in 𝓝 z, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1))
    (hJsq : ∀ v, J (u z) (J (u z) v) = -v) (ha : ‖J (u z)‖ ≤ a)
    (hb : ‖fderiv ℝ J (u z)‖ ≤ b) (hc : ‖iteratedFDeriv ℝ 2 J (u z)‖ ≤ c)
    (hm : ‖fderiv ℝ u z 1‖ ≤ m) (hm' : ‖fderiv ℝ u z 1 - e₀‖ ≤ m) :
    ‖Δ (fun y ↦ fderiv ℝ u y 1) z‖ ≤
      2 * a * c * m ^ 2 * ‖fderiv ℝ u z 1 - e₀‖ +
        4 * a * b * m * ‖fderiv ℝ (fderiv ℝ u) z 1 1‖ +
        2 * b * m * ‖fderiv ℝ (fderiv ℝ u) z 1 I‖ := by
  have hJu₁ : ∀ w, fderiv ℝ (fun y ↦ J (u y)) z w = fderiv ℝ J (u z) (fderiv ℝ u z w) := fun w ↦ by
    rw [fderiv_fun_comp z (hJ.differentiableAt (by norm_num)) (hu.differentiableAt (by norm_num)),
      ContinuousLinearMap.comp_apply]
  have hJu₂ : ∀ a w, fderiv ℝ (fderiv ℝ fun y ↦ J (u y)) z a w =
      fderiv ℝ (fderiv ℝ J) (u z) (fderiv ℝ u z a) (fderiv ℝ u z w) +
        fderiv ℝ J (u z) (fderiv ℝ (fderiv ℝ u) z a w) :=
    fderiv_fderiv_comp_apply hJ (hu.of_le (by norm_num))
  -- The derivatives of `J` vanish on `e₀`.
  have hJ₁e : fderiv ℝ J (u z) e₀ = 0 := fderiv_apply_eq_zero_of_forall_periodic_smul hJe _
  have hJ₂e : fderiv ℝ (fderiv ℝ J) (u z) e₀ = 0 :=
    fderiv_apply_eq_zero_of_forall_periodic_smul (fun τ ↦ (hJe τ).fderiv) _
  have hJ₂e' : ∀ w, fderiv ℝ (fderiv ℝ J) (u z) w e₀ = 0 := fun w ↦ by
    have hzero : (fun y ↦ fderiv ℝ J y e₀) = fun _ ↦ 0 :=
      funext fun y ↦ fderiv_apply_eq_zero_of_forall_periodic_smul hJe y
    have h := fderiv_clm_apply_const_apply
      ((hJ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) e₀ w
    rw [hzero, fderiv_const_apply, zero_apply] at h
    exact h.symm
  rw [laplacian_fderiv_one_eq hu hJ hCR hJsq]
  simp only [hJu₁, hJu₂]
  rw [hCR.self_of_nhds]
  set ξ := fderiv ℝ u z 1
  set ζ := ξ - e₀
  set ξs := fderiv ℝ (fderiv ℝ u) z 1 1
  set ξt := fderiv ℝ (fderiv ℝ u) z 1 I
  set J₀ := J (u z)
  set J₁ := fderiv ℝ J (u z)
  set J₂ := fderiv ℝ (fderiv ℝ J) (u z)
  -- Replace `∂ₛu = ζ + e₀` by `ζ` in the slots of `J₁` and `J₂` that kill `e₀`.
  have hξ : ξ = ζ + e₀ := (sub_add_cancel ξ e₀).symm
  have hJ₁ξ : J₁ ξ = J₁ ζ := by rw [hξ, map_add, hJ₁e, add_zero]
  have hJ₂ξ : ∀ v, J₂ ξ v = J₂ ζ v := fun v ↦ by rw [hξ, map_add, hJ₂e, add_zero]
  have hJ₂ξξ : J₂ ζ ξ = J₂ ζ ζ := by rw [hξ, map_add, hJ₂e', add_zero]
  rw [hJ₁ξ, hJ₂ξ, hJ₂ξ, hJ₂ξξ]
  have ha₀ : 0 ≤ a := (norm_nonneg _).trans ha
  have hb₀ : 0 ≤ b := J₁.opNorm_nonneg.trans hb
  have hc₀ : 0 ≤ c := (norm_nonneg _).trans hc
  have hm₀ : 0 ≤ m := (norm_nonneg _).trans hm
  have hJ₀ : ∀ v, ‖J₀ v‖ ≤ a * ‖v‖ := fun v ↦ (J₀.le_opNorm v).trans (by gcongr)
  have hJ₁ : ∀ x v, ‖J₁ x v‖ ≤ b * ‖x‖ * ‖v‖ := fun x v ↦ (J₁.le_opNorm₂ x v).trans (by gcongr)
  have hJ₂ : ∀ x y v, ‖J₂ x y v‖ ≤ c * ‖x‖ * ‖y‖ * ‖v‖ := by
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at hc
    exact fun x y v ↦ (ContinuousLinearMap.le_opNorm _ v).trans
      (by gcongr; exact (ContinuousLinearMap.le_opNorm₂ _ x y).trans (by gcongr))
  have hJ₀ξ : ‖J₀ ξ‖ ≤ a * m := (hJ₀ ξ).trans (by gcongr)
  -- Bound the five terms one by one.
  have h₁ : ‖(2 : ℝ) • J₀ (J₁ ζ ξs)‖ ≤ 2 * (a * (b * m * ‖ξs‖)) := by
    rw [norm_smul, Real.norm_two]
    gcongr
    exact (hJ₀ _).trans (by gcongr; exact (hJ₁ _ _).trans (by gcongr))
  have h₂ : ‖J₀ ((J₂ ζ ζ + J₁ ξs) ξ)‖ ≤ a * (c * m * ‖ζ‖ * m + b * ‖ξs‖ * m) := by
    refine (hJ₀ _).trans ?_
    gcongr
    rw [add_apply]
    refine norm_add_le_of_le ((hJ₂ _ _ _).trans ?_) ((hJ₁ _ _).trans (by gcongr))
    have : ‖ζ‖ * ‖ζ‖ * ‖ξ‖ ≤ m * ‖ζ‖ * m := by
      nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul hm' hm (norm_nonneg _) hm₀)
        (norm_nonneg ζ)]
    calc c * ‖ζ‖ * ‖ζ‖ * ‖ξ‖ = c * (‖ζ‖ * ‖ζ‖ * ‖ξ‖) := by ring
      _ ≤ c * (m * ‖ζ‖ * m) := by gcongr
      _ = c * m * ‖ζ‖ * m := by ring
  have h₃ : ‖J₁ ζ ξt‖ ≤ b * m * ‖ξt‖ := (hJ₁ _ _).trans (by gcongr)
  have h₄ : ‖(J₂ ζ (J₀ ξ) + J₁ ξt) ξ‖ ≤ c * ‖ζ‖ * (a * m) * m + b * ‖ξt‖ * m := by
    rw [add_apply]
    exact norm_add_le_of_le ((hJ₂ _ _ _).trans (by gcongr)) ((hJ₁ _ _).trans (by gcongr))
  have h₅ : ‖J₁ (J₀ ξ) ξs‖ ≤ b * (a * m) * ‖ξs‖ := (hJ₁ _ _).trans (by gcongr)
  refine (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le h₁ h₂)
    h₃) h₄) h₅).trans_eq ?_
  ring

/-- **The deviation of `∂ₛu` from a symmetry is almost subharmonic.** Let `J` be invariant under
the translations along a vector `e₀`, and let `u : ℂ → V` be `C³` at `z` and solve the
Cauchy--Riemann equation `∂ₜu = J(u) ∂ₛu` near `z`, where `J` is `C²` at `u z` with
`J(u z)² = -1`. If `a`, `b` and `c` bound the norms of `J`, of its derivative and of its second
derivative at `u z`, and `m` bounds both `‖∂ₛu‖` and `‖∂ₛu - e₀‖` at `z`, then

`Δ ‖∂ₛu - e₀‖² ≥ -(4ac + 2b² + 8a²b²) m² ‖∂ₛu - e₀‖²` at `z`. -/
theorem neg_mul_norm_fderiv_one_sub_sq_le_laplacian {a b c m : ℝ}
    (hJe : ∀ τ : ℝ, Function.Periodic J (τ • e₀))
    (hu : ContDiffAt ℝ 3 u z) (hJ : ContDiffAt ℝ 2 J (u z))
    (hCR : ∀ᶠ y in 𝓝 z, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1))
    (hJsq : ∀ v, J (u z) (J (u z) v) = -v) (ha : ‖J (u z)‖ ≤ a)
    (hb : ‖fderiv ℝ J (u z)‖ ≤ b) (hc : ‖iteratedFDeriv ℝ 2 J (u z)‖ ≤ c)
    (hm : ‖fderiv ℝ u z 1‖ ≤ m) (hm' : ‖fderiv ℝ u z 1 - e₀‖ ≤ m) :
    -((4 * a * c + 2 * b ^ 2 + 8 * a ^ 2 * b ^ 2) * m ^ 2 * ‖fderiv ℝ u z 1 - e₀‖ ^ 2) ≤
      Δ (fun y ↦ ‖fderiv ℝ u y 1 - e₀‖ ^ 2) z := by
  have hDu : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (m := 2) (by norm_num)
  have hξ : ContDiffAt ℝ 2 (fun y ↦ fderiv ℝ u y 1) z := hDu.clm_apply contDiffAt_const
  have hζ : ContDiffAt ℝ 2 (fun y ↦ fderiv ℝ u y 1 - e₀) z := hξ.sub contDiffAt_const
  have hD : ∀ w, fderiv ℝ (fun y ↦ fderiv ℝ u y 1 - e₀) z w = fderiv ℝ (fderiv ℝ u) z w 1 :=
    fun w ↦ by
      rw [fderiv_sub_const]
      exact fderiv_clm_apply_const_apply (hDu.differentiableAt (by norm_num)) 1 w
  have hΔ : Δ (fun y ↦ fderiv ℝ u y 1 - e₀) z = Δ (fun y ↦ fderiv ℝ u y 1) z := by
    rw [← Pi.sub_def, hξ.laplacian_sub contDiffAt_const, laplacian_const, Pi.zero_apply,
      sub_zero]
  have hsymm : fderiv ℝ (fderiv ℝ u) z I 1 = fderiv ℝ (fderiv ℝ u) z 1 I :=
    hu.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) I 1
  have hL := norm_laplacian_fderiv_one_le_of_periodic hJe hu hJ hCR hJsq ha hb hc hm hm'
  have hinner := neg_le_of_abs_le
    (abs_real_inner_le_norm (fderiv ℝ u z 1 - e₀) (Δ (fun y ↦ fderiv ℝ u y 1) z))
  rw [hζ.laplacian_norm_sq Complex.orthonormalBasisOneI]
  simp only [Complex.coe_orthonormalBasisOneI, Fin.sum_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, hD, hsymm, hΔ]
  have hX := norm_nonneg (fderiv ℝ u z 1 - e₀)
  have : 0 ≤ m := (norm_nonneg _).trans hm
  nlinarith [mul_le_mul_of_nonneg_left hL hX,
    sq_nonneg (‖fderiv ℝ (fderiv ℝ u) z 1 I‖ - b * m * ‖fderiv ℝ u z 1 - e₀‖),
    sq_nonneg (‖fderiv ℝ (fderiv ℝ u) z 1 1‖ - 2 * a * b * m * ‖fderiv ℝ u z 1 - e₀‖)]

/-- **The energy density of a `J`-holomorphic curve is almost subharmonic.** Let `u : ℂ → V` be
`C³` at `z` and solve the Cauchy--Riemann equation `∂ₜu = J(u) ∂ₛu` near `z`, where `J` is `C²` at
`u z` with `J(u z)² = -1`. If `a`, `b` and `c` bound the norms of `J`, of its derivative and of its
second derivative at `u z`, then

`Δ ‖∂ₛu‖² ≥ -(4ac + 2b² + 8a²b²) ‖∂ₛu‖⁴` at `z`. -/
theorem neg_mul_norm_fderiv_one_pow_four_le_laplacian {a b c : ℝ}
    (hu : ContDiffAt ℝ 3 u z) (hJ : ContDiffAt ℝ 2 J (u z))
    (hCR : ∀ᶠ y in 𝓝 z, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1))
    (hJsq : ∀ v, J (u z) (J (u z) v) = -v) (ha : ‖J (u z)‖ ≤ a)
    (hb : ‖fderiv ℝ J (u z)‖ ≤ b) (hc : ‖iteratedFDeriv ℝ 2 J (u z)‖ ≤ c) :
    -((4 * a * c + 2 * b ^ 2 + 8 * a ^ 2 * b ^ 2) * ‖fderiv ℝ u z 1‖ ^ 4) ≤
      Δ (fun y ↦ ‖fderiv ℝ u y 1‖ ^ 2) z := by
  -- The case `e₀ = 0`, `m = ‖∂ₛu‖` of the translation-invariant inequality.
  have h := neg_mul_norm_fderiv_one_sub_sq_le_laplacian (e₀ := 0) (fun τ x ↦ by simp) hu hJ hCR
    hJsq ha hb hc le_rfl (by rw [sub_zero])
  simp only [sub_zero] at h
  convert h using 2
  ring

/-- **The mean-value inequality for `J`-holomorphic curves.** Let `u : ℂ → V` be `C³` on the open
disk `ball z₀ r`, with `∂ₛu` continuous on its closure, and solve the Cauchy--Riemann equation
`∂ₜu = J(u) ∂ₛu` on the disk. Suppose that on the disk `J` is `C²` along `u`, squares to `-1`, and
`a`, `b`, `c` bound the norms of `J`, of its derivative and of its second derivative along `u`. If
the energy `∫ ‖∂ₛu‖²` over the disk is small, `8 (4ac + 2b² + 8a²b²) ∫ ‖∂ₛu‖² < π`, then
`‖∂ₛu(z₀)‖²` is at most eight times its average over the disk:

`π r² ‖∂ₛu(z₀)‖² ≤ 8 ∫_{B_r(z₀)} ‖∂ₛu‖²`. -/
theorem pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball {z₀ : ℂ} {r a b c : ℝ}
    (hr : 0 ≤ r) (hu : ContDiffOn ℝ 3 u (ball z₀ r))
    (hu' : ContinuousOn (fun y ↦ fderiv ℝ u y 1) (closedBall z₀ r))
    (hCR : ∀ y ∈ ball z₀ r, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1))
    (hJ : ∀ y ∈ ball z₀ r, ContDiffAt ℝ 2 J (u y))
    (hJsq : ∀ y ∈ ball z₀ r, ∀ v, J (u y) (J (u y) v) = -v)
    (ha : ∀ y ∈ ball z₀ r, ‖J (u y)‖ ≤ a) (hb : ∀ y ∈ ball z₀ r, ‖fderiv ℝ J (u y)‖ ≤ b)
    (hc : ∀ y ∈ ball z₀ r, ‖iteratedFDeriv ℝ 2 J (u y)‖ ≤ c)
    (hsmall : 8 * (4 * a * c + 2 * b ^ 2 + 8 * a ^ 2 * b ^ 2) *
      ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 < π) :
    π * r ^ 2 * ‖fderiv ℝ u z₀ 1‖ ^ 2 ≤ 8 * ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 := by
  have hDu : ContDiffOn ℝ 2 (fderiv ℝ u) (ball z₀ r) :=
    hu.fderiv_of_isOpen isOpen_ball (by norm_num)
  have h := mul_le_eight_mul_setIntegral_ball_of_neg_mul_sq_le_laplacian (μ := volume)
    (by simp) (w := fun y ↦ ‖fderiv ℝ u y 1‖ ^ 2) (x₀ := z₀) (r := r)
    (A := 4 * a * c + 2 * b ^ 2 + 8 * a ^ 2 * b ^ 2) ((hDu.clm_apply contDiffOn_const).norm_sq ℝ)
    (hu'.norm.pow 2) (fun _ _ ↦ by positivity)
    (fun y hy ↦ by
      rw [← pow_mul]
      exact neg_mul_norm_fderiv_one_pow_four_le_laplacian
        (hu.contDiffAt (isOpen_ball.mem_nhds hy)) (hJ y hy)
        (eventually_of_mem (isOpen_ball.mem_nhds hy) hCR) (hJsq y hy) (ha y hy) (hb y hy)
        (hc y hy))
    (by simpa [measureReal_def, NNReal.coe_real_pi] using hsmall)
  simpa [measureReal_def, hr, mul_comm, mul_left_comm, mul_assoc] using h

/-- **The mean-value inequality for a compact family of structures.** Let `J p` be structures
depending on a parameter `p` in a normed space, jointly `C²` in `(p, x)` on an open set `W`
containing `C × K` for compact sets `C` and `K`, with `J p (x)² = -1` on `C × K`. There is one
energy threshold `δ > 0` for all `p ∈ C`: every solution `u` of `∂ₜu = J p (u) ∂ₛu` that is `C³`
on the open disk `ball z₀ r`, has `∂ₛu` continuous on its closure, maps the disk into `K` and has
energy `∫ ‖∂ₛu‖² < δ` over it, satisfies `π r² ‖∂ₛu(z₀)‖² ≤ 8 ∫_{B_r(z₀)} ‖∂ₛu‖²`.

Such families arise as the structures `J(z₀, ·)` frozen at the points `z₀` of a compact window of
the domain of an inhomogeneous equation, possibly together with further parameters. -/
theorem exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball_parametric
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {J : P → V → V →L[ℝ] V}
    {W : Set (P × V)} {C : Set P} {K : Set V} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (Function.uncurry J) W) (hC : IsCompact C) (hK : IsCompact K)
    (hCKW : C ×ˢ K ⊆ W) (hJsq : ∀ p ∈ C, ∀ x ∈ K, ∀ v, J p x (J p x v) = -v) :
    ∃ δ > 0, ∀ ⦃p : P⦄, p ∈ C → ∀ ⦃u : ℂ → V⦄ ⦃z₀ : ℂ⦄ ⦃r : ℝ⦄, 0 ≤ r →
      ContDiffOn ℝ 3 u (ball z₀ r) →
      ContinuousOn (fun y ↦ fderiv ℝ u y 1) (closedBall z₀ r) →
      (∀ y ∈ ball z₀ r, fderiv ℝ u y I = J p (u y) (fderiv ℝ u y 1)) →
      (∀ y ∈ ball z₀ r, u y ∈ K) →
      ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 < δ →
      π * r ^ 2 * ‖fderiv ℝ u z₀ 1‖ ^ 2 ≤ 8 * ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 := by
  -- One nonnegative bound for `J p` and its first two derivatives on `K`, uniform in `p ∈ C`.
  obtain ⟨A, hA0, hA⟩ :=
    hJ.exists_nonneg_bound_iteratedFDeriv_uncurry_of_isOpen (n := 2) hW hC hK hCKW
  set B := 4 * A * A + 2 * A ^ 2 + 8 * A ^ 2 * A ^ 2
  refine ⟨π / (8 * (B + 1)), by positivity, fun p hp u z₀ r hr hu hu' hCR huK hE ↦ ?_⟩
  have hI : 0 ≤ ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 := by positivity
  refine pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball hr hu hu' hCR
    (fun y hy ↦ (hA p hp _ (huK y hy)).1) (fun y hy ↦ hJsq p hp _ (huK y hy))
    (fun y hy ↦ by simpa using (hA p hp _ (huK y hy)).2 0 (by norm_num))
    (fun y hy ↦ by simpa [norm_iteratedFDeriv_one] using (hA p hp _ (huK y hy)).2 1 (by norm_num))
    (fun y hy ↦ (hA p hp _ (huK y hy)).2 2 le_rfl) ?_
  rw [lt_div_iff₀ (by positivity)] at hE
  nlinarith

/-- **The mean-value inequality for `J`-holomorphic curves in a compact set.** Let `J` be `C²` on an
open set `W` containing a compact set `K`, with `J(x)² = -1` on `K`. There is an energy threshold
`δ > 0` such that every solution `u` of `∂ₜu = J(u) ∂ₛu` that is `C³` on the open disk
`ball z₀ r`, has `∂ₛu` continuous on its closure, maps the disk into `K` and has energy
`∫ ‖∂ₛu‖² < δ` over it, satisfies `π r² ‖∂ₛu(z₀)‖² ≤ 8 ∫_{B_r(z₀)} ‖∂ₛu‖²`. -/
theorem exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball
    {W K : Set V} (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) :
    ∃ δ > 0, ∀ ⦃u : ℂ → V⦄ ⦃z₀ : ℂ⦄ ⦃r : ℝ⦄, 0 ≤ r → ContDiffOn ℝ 3 u (ball z₀ r) →
      ContinuousOn (fun y ↦ fderiv ℝ u y 1) (closedBall z₀ r) →
      (∀ y ∈ ball z₀ r, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1)) →
      (∀ y ∈ ball z₀ r, u y ∈ K) →
      ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 < δ →
      π * r ^ 2 * ‖fderiv ℝ u z₀ 1‖ ^ 2 ≤ 8 * ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 := by
  obtain ⟨δ, hδ, h⟩ :=
    exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball_parametric
      (J := fun (_ : Unit) ↦ J) (hW.preimage continuous_snd)
      (hJ.comp contDiffOn_snd fun _ hq ↦ hq) isCompact_univ hK
      (fun q hq ↦ hKW hq.2) fun _ _ ↦ hJsq
  exact ⟨δ, hδ, h (Set.mem_univ ())⟩

/-- **The mean-value inequality for `∂ₛu - e₀`.** Let `J` be invariant under the translations
along a vector `e₀`, and let `u : ℂ → V` be `C³` on the open disk `ball z₀ r`, with `∂ₛu`
continuous on its closure, solving `∂ₜu = J(u) ∂ₛu` on the disk. Suppose that on the disk `J` is
`C²` along `u` and squares to `-1`, that `a`, `b`, `c` bound the norms of `J`, of its derivative
and of its second derivative along `u`, and that `m` bounds `‖∂ₛu‖` and `‖∂ₛu - e₀‖`. If the disk
is small, `16 (4ac + 2b² + 8a²b²) m² r² ≤ 1`, then

`π r² ‖∂ₛu(z₀) - e₀‖² ≤ 15 ∫_{B_r(z₀)} ‖∂ₛu - e₀‖²`. -/
theorem pi_mul_sq_mul_norm_fderiv_one_sub_sq_le_fifteen_mul_setIntegral_ball {z₀ : ℂ}
    {r a b c m : ℝ} (hJe : ∀ τ : ℝ, Function.Periodic J (τ • e₀)) (hr : 0 ≤ r)
    (hu : ContDiffOn ℝ 3 u (ball z₀ r))
    (hu' : ContinuousOn (fun y ↦ fderiv ℝ u y 1) (closedBall z₀ r))
    (hCR : ∀ y ∈ ball z₀ r, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1))
    (hJ : ∀ y ∈ ball z₀ r, ContDiffAt ℝ 2 J (u y))
    (hJsq : ∀ y ∈ ball z₀ r, ∀ v, J (u y) (J (u y) v) = -v)
    (ha : ∀ y ∈ ball z₀ r, ‖J (u y)‖ ≤ a) (hb : ∀ y ∈ ball z₀ r, ‖fderiv ℝ J (u y)‖ ≤ b)
    (hc : ∀ y ∈ ball z₀ r, ‖iteratedFDeriv ℝ 2 J (u y)‖ ≤ c)
    (hm : ∀ y ∈ ball z₀ r, ‖fderiv ℝ u y 1‖ ≤ m)
    (hm' : ∀ y ∈ ball z₀ r, ‖fderiv ℝ u y 1 - e₀‖ ≤ m)
    (hsmall : 16 * (4 * a * c + 2 * b ^ 2 + 8 * a ^ 2 * b ^ 2) * m ^ 2 * r ^ 2 ≤ 1) :
    π * r ^ 2 * ‖fderiv ℝ u z₀ 1 - e₀‖ ^ 2 ≤
      15 * ∫ y in ball z₀ r, ‖fderiv ℝ u y 1 - e₀‖ ^ 2 := by
  have hDu : ContDiffOn ℝ 2 (fderiv ℝ u) (ball z₀ r) :=
    hu.fderiv_of_isOpen isOpen_ball (by norm_num)
  have h := mul_le_fifteen_mul_setIntegral_ball_of_neg_mul_le_laplacian (μ := volume)
    (by simp) (w := fun y ↦ ‖fderiv ℝ u y 1 - e₀‖ ^ 2) (x₀ := z₀) (r := r)
    (A := (4 * a * c + 2 * b ^ 2 + 8 * a ^ 2 * b ^ 2) * m ^ 2)
    (((hDu.clm_apply contDiffOn_const).sub contDiffOn_const).norm_sq ℝ)
    ((hu'.sub continuousOn_const).norm.pow 2) (fun _ _ ↦ by positivity)
    (fun y hy ↦ neg_mul_norm_fderiv_one_sub_sq_le_laplacian hJe
        (hu.contDiffAt (isOpen_ball.mem_nhds hy)) (hJ y hy)
        (eventually_of_mem (isOpen_ball.mem_nhds hy) hCR) (hJsq y hy) (ha y hy) (hb y hy)
        (hc y hy) (hm y hy) (hm' y hy))
    (by
      rw [Complex.volume_real_ball z₀ hr, Complex.volume_real_ball 0 zero_le_one]
      nlinarith [Real.pi_pos])
  rwa [Complex.volume_real_ball z₀ hr] at h

/-- **The mean-value inequality for `∂ₛu - e₀` in a compact set.** Let `J` be `C²` on an open set
`W` containing a compact set `K`, with `J(x)² = -1` on `K`, and invariant under the translations
along a vector `e₀`. There is `A ≥ 0` such that every solution `u` of `∂ₜu = J(u) ∂ₛu` that is
`C³` on the open disk `ball z₀ r`, has `∂ₛu` continuous on its closure, maps the disk into `K`, and
has `‖∂ₛu‖ ≤ m` and `‖∂ₛu - e₀‖ ≤ m` on it, satisfies
`π r² ‖∂ₛu(z₀) - e₀‖² ≤ 15 ∫_{B_r(z₀)} ‖∂ₛu - e₀‖²` as soon as `16 A m² r² ≤ 1`. -/
theorem exists_nonneg_forall_pi_mul_sq_mul_norm_fderiv_one_sub_sq_le_fifteen_mul_setIntegral_ball
    {W K : Set V} (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hJe : ∀ τ : ℝ, Function.Periodic J (τ • e₀)) :
    ∃ A, 0 ≤ A ∧ ∀ ⦃u : ℂ → V⦄ ⦃z₀ : ℂ⦄ ⦃r m : ℝ⦄, 0 ≤ r → ContDiffOn ℝ 3 u (ball z₀ r) →
      ContinuousOn (fun y ↦ fderiv ℝ u y 1) (closedBall z₀ r) →
      (∀ y ∈ ball z₀ r, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1)) →
      (∀ y ∈ ball z₀ r, u y ∈ K) →
      (∀ y ∈ ball z₀ r, ‖fderiv ℝ u y 1‖ ≤ m) →
      (∀ y ∈ ball z₀ r, ‖fderiv ℝ u y 1 - e₀‖ ≤ m) →
      16 * A * m ^ 2 * r ^ 2 ≤ 1 →
      π * r ^ 2 * ‖fderiv ℝ u z₀ 1 - e₀‖ ^ 2 ≤
        15 * ∫ y in ball z₀ r, ‖fderiv ℝ u y 1 - e₀‖ ^ 2 := by
  -- One nonnegative bound `C` for `J` and its first two derivatives on `K`.
  obtain ⟨C, hC0, hC⟩ := hJ.exists_nonneg_bound_iteratedFDeriv_of_isOpen (n := 2) hW hK hKW
  refine ⟨4 * C * C + 2 * C ^ 2 + 8 * C ^ 2 * C ^ 2, by positivity,
    fun u z₀ r m hr hu hu' hCR huK hm hm' hsmall ↦ ?_⟩
  exact pi_mul_sq_mul_norm_fderiv_one_sub_sq_le_fifteen_mul_setIntegral_ball hJe hr hu hu' hCR
    (fun y hy ↦ hJ.contDiffAt (hW.mem_nhds (hKW (huK y hy))))
    (fun y hy ↦ hJsq _ (huK y hy))
    (fun y hy ↦ by simpa using hC 0 (by norm_num) _ (huK y hy))
    (fun y hy ↦ by simpa [norm_iteratedFDeriv_one] using hC 1 (by norm_num) _ (huK y hy))
    (fun y hy ↦ hC 2 le_rfl _ (huK y hy)) hm hm' hsmall

/-! ### Linear Cauchy–Riemann equations -/

section Linear

variable {v : ℂ → V} {J B : ℂ → V →L[ℝ] V}

/-- The linear equation `∂ₜv = J ∂ₛv + B v` differentiated once at `z`, in the direction `w`. -/
private theorem fderiv_fderiv_apply_I_eq_of_linear (hv : ContDiffAt ℝ 2 v z)
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
  have h := congrArg (fun L : ℂ →L[ℝ] V ↦ L w)
    (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (f₁ := fun y ↦ fderiv ℝ v y I)
      (f := fun y ↦ J y (fderiv ℝ v y 1) + B y (v y)) heq)
  rw [fderiv_clm_apply_const_apply hDv, fderiv_fun_add (hJ.clm_apply hvs) (hB.clm_apply hvd),
    fderiv_clm_apply hJ hvs, fderiv_clm_apply hB hvd] at h
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    fderiv_clm_apply_const_apply hDv] at h
  rw [h]
  abel

/-- The Laplacian of a solution of `∂ₜv = J ∂ₛv + B v` with `J(z)² = -1`: the second derivatives
of `v` drop out, leaving first-order terms in `v` whose coefficients involve `J`, `B` and their
first derivatives. -/
private theorem laplacian_eq_of_linear (hv : ContDiffAt ℝ 2 v z) (hJ : DifferentiableAt ℝ J z)
    (hB : DifferentiableAt ℝ B z)
    (heq : ∀ᶠ y in 𝓝 z, fderiv ℝ v y I = J y (fderiv ℝ v y 1) + B y (v y))
    (hJsq : ∀ w, J z (J z w) = -w) :
    Δ v z = fderiv ℝ J z I (fderiv ℝ v z 1) + J z (fderiv ℝ J z 1 (fderiv ℝ v z 1)) +
      J z (B z (fderiv ℝ v z 1)) + B z (fderiv ℝ v z I) +
      J z (fderiv ℝ B z 1 (v z)) + fderiv ℝ B z I (v z) := by
  have hsymm : fderiv ℝ (fderiv ℝ v) z I 1 = fderiv ℝ (fderiv ℝ v) z 1 I :=
    hv.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) I 1
  have h₁ := fderiv_fderiv_apply_I_eq_of_linear hv hJ hB heq I
  have h₂ := fderiv_fderiv_apply_I_eq_of_linear hv hJ hB heq 1
  rw [hsymm, h₂] at h₁
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [h₁]
  simp only [map_add, hJsq]
  abel

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
    rw [laplacian_eq_of_linear hv hJ hB heq hJsq]
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
  have h := mul_le_fifteen_mul_setIntegral_ball_of_neg_mul_le_laplacian (μ := volume)
    (by simp) (w := fun y ↦ ‖v y‖ ^ 2) (x₀ := z₀) (r := r)
    (A := ((b + a * b + a * β) ^ 2 + β ^ 2) / 2 + 2 * (a * γ + γ)) (hv.norm_sq ℝ)
    (hvc.norm.pow 2) (fun _ _ ↦ by positivity)
    (fun y hy ↦ neg_mul_norm_sq_le_laplacian_of_fderiv_I_eq
      (hv.contDiffAt (isOpen_ball.mem_nhds hy)) (hJ y hy) (hB y hy)
      (eventually_of_mem (isOpen_ball.mem_nhds hy) heq) (hJsq y hy) (ha y hy) (hb y hy)
      (hβ y hy) (hγ y hy))
    (by
      rw [Complex.volume_real_ball z₀ hr, Complex.volume_real_ball 0 zero_le_one]
      nlinarith [Real.pi_pos])
  rwa [Complex.volume_real_ball z₀ hr] at h

end Linear

section FiniteDimensional

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The mean-value inequality in a finite-dimensional normed space, for a compact family of
structures.** This is
`exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball_parametric`
for a target `F` without an inner product; the constant `8` becomes a constant `A` depending on the
norm of `F`. Let `J p` be structures depending on a parameter `p` in a normed space, jointly `C²` on
an open set `W` containing `C × K` for compact sets `C` and `K`, with `J p (x)² = -1` on `C × K`.
There are an energy threshold `δ > 0` and a constant `A > 0`, the same for all `p ∈ C`, such that
every solution `u` of `∂ₜu = J p (u) ∂ₛu` that is `C³` on the open disk `ball z₀ r`, has `∂ₛu`
continuous on its closure, maps the disk into `K` and has energy `∫ ‖∂ₛu‖² < δ` over it, satisfies
`π r² ‖∂ₛu(z₀)‖² ≤ A ∫_{B_r(z₀)} ‖∂ₛu‖²`.

Such families arise as the coordinate expressions, in a chart of a manifold, of the structures
`J(z₀, ·)` frozen at the points `z₀` of a compact window of a domain. -/
theorem
    exists_pos_exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_mul_setIntegral_ball_parametric
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {J : P → F → F →L[ℝ] F}
    {W : Set (P × F)} {C : Set P} {K : Set F} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (Function.uncurry J) W) (hC : IsCompact C) (hK : IsCompact K)
    (hCKW : C ×ˢ K ⊆ W) (hJsq : ∀ p ∈ C, ∀ x ∈ K, ∀ v, J p x (J p x v) = -v) :
    ∃ δ > 0, ∃ A > 0, ∀ ⦃p : P⦄, p ∈ C → ∀ ⦃u : ℂ → F⦄ ⦃z₀ : ℂ⦄ ⦃r : ℝ⦄, 0 ≤ r →
      ContDiffOn ℝ 3 u (ball z₀ r) →
      ContinuousOn (fun y ↦ fderiv ℝ u y 1) (closedBall z₀ r) →
      (∀ y ∈ ball z₀ r, fderiv ℝ u y I = J p (u y) (fderiv ℝ u y 1)) →
      (∀ y ∈ ball z₀ r, u y ∈ K) →
      ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 < δ →
      π * r ^ 2 * ‖fderiv ℝ u z₀ 1‖ ^ 2 ≤ A * ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 := by
  -- Conjugate `J` by `L = toEuclidean` and apply the inequality in the Euclidean space.
  let L : F ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) := toEuclidean
  set a := ‖(L : F →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F)))‖
  set b := ‖(L.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) →L[ℝ] F)‖
  have hJL : ContDiffOn ℝ 2 (fun q : P × EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) ↦
      (L : F →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) ∘L J q.1 (L.symm q.2) ∘L
        (L.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) →L[ℝ] F))
      (Prod.map id L.symm ⁻¹' W) :=
    contDiffOn_const.clm_comp ((hJ.comp (contDiff_id.prodMap L.symm.contDiff).contDiffOn
      (Set.mapsTo_preimage _ _)).clm_comp contDiffOn_const)
  obtain ⟨δ, hδ, hmean⟩ :=
    exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball_parametric
      (J := fun p x ↦ (L : F →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) ∘L
        J p (L.symm x) ∘L (L.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) →L[ℝ] F))
      (hW.preimage (continuous_id.prodMap L.symm.continuous)) hJL hC (hK.image L.continuous)
      (by rintro ⟨p, _⟩ ⟨hp, x, hx, rfl⟩; simpa using hCKW ⟨hp, hx⟩)
      (by rintro p hp _ ⟨x, hx, rfl⟩ v; simp [hJsq p hp x hx])
  refine ⟨δ / (a ^ 2 + 1), by positivity, 8 * (b ^ 2 * a ^ 2 + 1), by positivity,
    fun p hp u z₀ r hr hu hu' hCR huK hE ↦ ?_⟩
  have hd (y : ℂ) (w : ℂ) : fderiv ℝ (L ∘ u) y w = L (fderiv ℝ u y w) := by
    rw [L.comp_fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  have hLc : ContinuousOn (fun y ↦ L (fderiv ℝ u y 1)) (closedBall z₀ r) := by
    simpa [Function.comp_def] using
      L.toContinuousLinearMap.lipschitzWith.continuous.comp_continuousOn hu'
  -- The Euclidean energy is at most `a²` times the energy in `F`.
  have hEL : ∫ y in ball z₀ r, ‖fderiv ℝ (L ∘ u) y 1‖ ^ 2 ≤
      a ^ 2 * ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 := by
    simpa only [hd, ContinuousLinearEquiv.coe_coe] using
      (L : F →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F))).integral_norm_apply_sq_le
        ((hu'.norm.pow 2).integrableOn_compact (isCompact_closedBall z₀ r)
          |>.mono_set ball_subset_closedBall)
  have h := hmean hp (u := L ∘ u) hr (L.contDiff.comp_contDiffOn hu)
    (by simpa only [hd] using hLc)
    (fun y hy ↦ by simp [hd, hCR y hy])
    (fun y hy ↦ ⟨u y, huK y hy, rfl⟩)
    (by
      refine hEL.trans_lt ?_
      rw [lt_div_iff₀ (by positivity)] at hE
      nlinarith [sq_nonneg a])
  -- Back in `F`, `‖∂ₛu(z₀)‖ ≤ b ‖L ∂ₛu(z₀)‖`.
  have hz₀ : ‖fderiv ℝ u z₀ 1‖ ^ 2 ≤ b ^ 2 * ‖fderiv ℝ (L ∘ u) z₀ 1‖ ^ 2 := by
    rw [hd, ← mul_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simpa using (L.symm : _ →L[ℝ] F).le_opNorm (L (fderiv ℝ u z₀ 1))
  -- `π r² ‖∂ₛu(z₀)‖² ≤ b² π r² ‖L ∂ₛu(z₀)‖² ≤ 8 b² ∫ ‖L ∂ₛu‖² ≤ 8 b² a² ∫ ‖∂ₛu‖²`.
  have h1 := mul_le_mul_of_nonneg_left hz₀ (by positivity : 0 ≤ π * r ^ 2)
  have h2 := mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hEL (by norm_num)))
    (sq_nonneg b)
  nlinarith [(by positivity : 0 ≤ ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2)]

/-- **The mean-value inequality for `J`-holomorphic curves in a finite-dimensional normed space.**
This is `TauCeti.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball`
for a target `F` without an inner product; the constant `8` becomes a constant `A` depending on the
norm of `F`. Let `J` be `C²`
on an open set `W` containing a compact set `K`, with `J(x)² = -1` on `K`. There are an energy
threshold `δ > 0` and a constant `A > 0` such that every solution `u` of `∂ₜu = J(u) ∂ₛu` that is
`C³` on the open disk `ball z₀ r`, has `∂ₛu` continuous on its closure, maps the disk into `K` and
has energy `∫ ‖∂ₛu‖² < δ` over it, satisfies `π r² ‖∂ₛu(z₀)‖² ≤ A ∫_{B_r(z₀)} ‖∂ₛu‖²`. -/
theorem exists_pos_exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_mul_setIntegral_ball
    {J : F → F →L[ℝ] F} {W K : Set F} (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) :
    ∃ δ > 0, ∃ A > 0, ∀ ⦃u : ℂ → F⦄ ⦃z₀ : ℂ⦄ ⦃r : ℝ⦄, 0 ≤ r → ContDiffOn ℝ 3 u (ball z₀ r) →
      ContinuousOn (fun y ↦ fderiv ℝ u y 1) (closedBall z₀ r) →
      (∀ y ∈ ball z₀ r, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1)) →
      (∀ y ∈ ball z₀ r, u y ∈ K) →
      ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 < δ →
      π * r ^ 2 * ‖fderiv ℝ u z₀ 1‖ ^ 2 ≤ A * ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 := by
  obtain ⟨δ, hδ, A, hA, h⟩ :=
    exists_pos_exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_mul_setIntegral_ball_parametric
      (J := fun (_ : Unit) ↦ J) (hW.preimage continuous_snd)
      (hJ.comp contDiffOn_snd fun _ hq ↦ hq) isCompact_univ hK
      (fun q hq ↦ hKW hq.2) fun _ _ ↦ hJsq
  exact ⟨δ, hδ, A, hA, h (Set.mem_univ ())⟩

end FiniteDimensional

end TauCeti
