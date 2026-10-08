/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.MeanValueInequality
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.Varying

/-!
# The mean-value inequality for `J`-holomorphic curves

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
works for all curves with image in `K`. As `∂ₜu = J(u) ∂ₛu`, these bounds control the full
derivative of `u`.

## Main declarations

* `TauCeti.IsJHolomorphicAt.fderiv_I_eq`: a `J`-holomorphic curve from `ℂ` satisfies
  `∂ₜu = J(u) ∂ₛu`.
* `TauCeti.neg_mul_norm_fderiv_one_pow_four_le_laplacian`: the differential inequality
  `Δ ‖∂ₛu‖² ≥ -A ‖∂ₛu‖⁴` for a `J`-holomorphic curve.
* `TauCeti.pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball`: the mean-value
  inequality for `J`-holomorphic curves, with explicit constants.
* `TauCeti.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball`:
  the same with a smallness threshold that is uniform over curves with image in a compact set.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.3 (the mean-value inequality and its
  application to the energy density of `J`-holomorphic curves).
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Filter Topology Complex Metric MeasureTheory Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable {u : ℂ → V} {J : V → V →L[ℝ] V} {z : ℂ}

/-- A curve that is `J'`-holomorphic at `z` for the standard complex structure of `ℂ` satisfies
the Cauchy--Riemann equation in the form `∂ₜu = J'(u) ∂ₛu` used in this file. -/
theorem IsJHolomorphicAt.fderiv_I_eq {J' : V → AlmostComplexStructure V}
    (h : IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ) J' u z) :
    fderiv ℝ u z I = J' (u z) (fderiv ℝ u z 1) := by
  obtain ⟨f', hf', hc⟩ := (isJHolomorphicAt_iff _ _ u z).mp h
  have h1 := LinearMap.congr_fun hc 1
  simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe] at h1
  rw [hf'.fderiv]
  simpa [AlmostComplexStructure.ofComplexModule_apply] using h1

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

/-- The Laplacian of `∂ₛu` is bounded by `‖∂ₛu‖³` and by `‖∂ₛu‖` times the second derivatives
`∂ₛ∂ₛu` and `∂ₛ∂ₜu`, with constants from bounds on `J` and its first two derivatives. -/
private theorem norm_laplacian_fderiv_one_le {a b c : ℝ} (hu : ContDiffAt ℝ 3 u z)
    (hJ : ContDiffAt ℝ 2 J (u z)) (hCR : ∀ᶠ y in 𝓝 z, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1))
    (hJsq : ∀ v, J (u z) (J (u z) v) = -v) (ha : ‖J (u z)‖ ≤ a)
    (hb : ‖fderiv ℝ J (u z)‖ ≤ b) (hc : ‖iteratedFDeriv ℝ 2 J (u z)‖ ≤ c) :
    ‖Δ (fun y ↦ fderiv ℝ u y 1) z‖ ≤
      2 * a * c * ‖fderiv ℝ u z 1‖ ^ 3 +
        2 * b * ‖fderiv ℝ u z 1‖ * ‖fderiv ℝ (fderiv ℝ u) z 1 I‖ +
        4 * a * b * ‖fderiv ℝ u z 1‖ * ‖fderiv ℝ (fderiv ℝ u) z 1 1‖ := by
  have hJu₁ : ∀ w, fderiv ℝ (fun y ↦ J (u y)) z w = fderiv ℝ J (u z) (fderiv ℝ u z w) := fun w ↦ by
    rw [fderiv_fun_comp z (hJ.differentiableAt (by norm_num)) (hu.differentiableAt (by norm_num)),
      ContinuousLinearMap.comp_apply]
  have hJu₂ : ∀ a w, fderiv ℝ (fderiv ℝ fun y ↦ J (u y)) z a w =
      fderiv ℝ (fderiv ℝ J) (u z) (fderiv ℝ u z a) (fderiv ℝ u z w) +
        fderiv ℝ J (u z) (fderiv ℝ (fderiv ℝ u) z a w) :=
    fderiv_fderiv_comp_apply hJ (hu.of_le (by norm_num))
  rw [laplacian_fderiv_one_eq hu hJ hCR hJsq]
  simp only [hJu₁, hJu₂]
  rw [hCR.self_of_nhds]
  set ξ := fderiv ℝ u z 1
  set ξs := fderiv ℝ (fderiv ℝ u) z 1 1
  set ξt := fderiv ℝ (fderiv ℝ u) z 1 I
  set J₀ := J (u z)
  set J₁ := fderiv ℝ J (u z)
  have ha₀ : 0 ≤ a := (norm_nonneg _).trans ha
  have hb₀ : 0 ≤ b := J₁.opNorm_nonneg.trans hb
  have hc₀ : 0 ≤ c := (norm_nonneg _).trans hc
  have hJ₀ : ∀ v, ‖J₀ v‖ ≤ a * ‖v‖ := fun v ↦ (J₀.le_opNorm v).trans (by gcongr)
  have hJ₁ : ∀ x v, ‖J₁ x v‖ ≤ b * ‖x‖ * ‖v‖ := fun x v ↦ (J₁.le_opNorm₂ x v).trans (by gcongr)
  have hJ₂ : ∀ x y v, ‖fderiv ℝ (fderiv ℝ J) (u z) x y v‖ ≤ c * ‖x‖ * ‖y‖ * ‖v‖ := by
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at hc
    exact fun x y v ↦ (ContinuousLinearMap.le_opNorm _ v).trans
      (by gcongr; exact (ContinuousLinearMap.le_opNorm₂ _ x y).trans (by gcongr))
  -- Bound the five terms one by one.
  have h₁ : ‖(2 : ℝ) • J₀ (J₁ ξ ξs)‖ ≤ 2 * (a * (b * ‖ξ‖ * ‖ξs‖)) := by
    rw [norm_smul, Real.norm_two]
    gcongr
    exact (hJ₀ _).trans (by gcongr; exact hJ₁ _ _)
  have h₂ : ‖J₀ ((fderiv ℝ (fderiv ℝ J) (u z) ξ ξ + J₁ ξs) ξ)‖ ≤
      a * (c * ‖ξ‖ * ‖ξ‖ * ‖ξ‖ + b * ‖ξs‖ * ‖ξ‖) := by
    refine (hJ₀ _).trans ?_
    gcongr
    rw [add_apply]
    exact norm_add_le_of_le (hJ₂ _ _ _) (hJ₁ _ _)
  have h₄ : ‖(fderiv ℝ (fderiv ℝ J) (u z) ξ (J₀ ξ) + J₁ ξt) ξ‖ ≤
      c * ‖ξ‖ * (a * ‖ξ‖) * ‖ξ‖ + b * ‖ξt‖ * ‖ξ‖ := by
    rw [add_apply]
    refine norm_add_le_of_le ((hJ₂ _ _ _).trans ?_) (hJ₁ _ _)
    gcongr
    exact hJ₀ ξ
  have h₅ : ‖J₁ (J₀ ξ) ξs‖ ≤ b * (a * ‖ξ‖) * ‖ξs‖ :=
    (hJ₁ _ _).trans (by gcongr; exact hJ₀ ξ)
  refine (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le h₁ h₂)
    (hJ₁ ξ ξt)) h₄) h₅).trans_eq ?_
  ring

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
  have hDu : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (m := 2) (by norm_num)
  have hξ : ContDiffAt ℝ 2 (fun y ↦ fderiv ℝ u y 1) z := hDu.clm_apply contDiffAt_const
  have hD : ∀ w, fderiv ℝ (fun y ↦ fderiv ℝ u y 1) z w = fderiv ℝ (fderiv ℝ u) z w 1 :=
    fderiv_clm_apply_const_apply (hDu.differentiableAt (by norm_num)) 1
  have hsymm : fderiv ℝ (fderiv ℝ u) z I 1 = fderiv ℝ (fderiv ℝ u) z 1 I :=
    hu.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) I 1
  have hL := norm_laplacian_fderiv_one_le hu hJ hCR hJsq ha hb hc
  have hinner := neg_le_of_abs_le
    (abs_real_inner_le_norm (fderiv ℝ u z 1) (Δ (fun y ↦ fderiv ℝ u y 1) z))
  rw [hξ.laplacian_norm_sq Complex.orthonormalBasisOneI]
  simp only [Complex.coe_orthonormalBasisOneI, Fin.sum_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, hD, hsymm]
  have hX := norm_nonneg (fderiv ℝ u z 1)
  nlinarith [mul_le_mul_of_nonneg_left hL hX,
    sq_nonneg (‖fderiv ℝ (fderiv ℝ u) z 1 I‖ - b * ‖fderiv ℝ u z 1‖ ^ 2),
    sq_nonneg (‖fderiv ℝ (fderiv ℝ u) z 1 1‖ - 2 * a * b * ‖fderiv ℝ u z 1‖ ^ 2)]

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
  obtain ⟨a, ha⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn
    ((hJ.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hKW)
  obtain ⟨c, hc⟩ := hK.exists_bound_of_continuousOn
    (((hJ.continuousOn_iteratedFDerivWithin le_rfl hW.uniqueDiffOn).congr
      (iteratedFDerivWithin_of_isOpen 2 hW).symm).mono hKW)
  -- Nonnegative bounds, so that the constant of the differential inequality is nonnegative.
  set A := 4 * max a 0 * max c 0 + 2 * b ^ 2 + 8 * max a 0 ^ 2 * b ^ 2
  have hA : 0 ≤ A := by positivity
  refine ⟨π / (8 * (A + 1)), by positivity, fun u z₀ r hr hu hu' hCR huK hE ↦ ?_⟩
  have hI : 0 ≤ ∫ y in ball z₀ r, ‖fderiv ℝ u y 1‖ ^ 2 := by positivity
  refine pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball hr hu hu' hCR
    (fun y hy ↦ hJ.contDiffAt (hW.mem_nhds (hKW (huK y hy))))
    (fun y hy ↦ hJsq _ (huK y hy)) (fun y hy ↦ (ha _ (huK y hy)).trans (le_max_left _ 0))
    (fun y hy ↦ hb _ (huK y hy)) (fun y hy ↦ (hc _ (huK y hy)).trans (le_max_left _ 0)) ?_
  rw [lt_div_iff₀ (by positivity)] at hE
  nlinarith

end TauCeti
