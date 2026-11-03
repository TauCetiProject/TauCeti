/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import TauCeti.Analysis.Calculus.Bilinear

/-!
# Second-order Taylor expansions

A map `f` between real normed spaces which is `C³` at `x` has the second-order Taylor expansion

  `f x' = f x + Df(x) (x' - x) + ½ D²f(x) (x' - x) (x' - x) + O(‖x' - x‖ ^ 3)`.

The remainder vanishes at `x`, and since the second derivative is symmetric its derivative is
`Df(x') - Df(x) - D²f(x) (x' - x) = O(‖x' - x‖ ^ 2)`, so the estimate is two applications of the
mean value inequality.

Let `u` be a real function on a real inner product space `E`. A second-order Taylor expansion of
`u` at `x` is an expansion

  `u x' = u x + ⟪y, x' - x⟫ + ⟪A (x' - x), x' - x⟫ / 2 + o(‖x' - x‖ ^ 2)`

with `y : E` and an operator `A : E →L[ℝ] E`. Only the quadratic form of `A` is determined by `u`,
so `A` is unique once it is required to be symmetric: two symmetric second-order terms differ by a
symmetric operator whose quadratic form is `o(‖x' - x‖ ^ 2)`, hence zero along every line through
`x`, and a symmetric operator with vanishing quadratic form is zero. No differentiability of `u`
beyond the expansion itself is assumed, so the statement applies to the Alexandrov Hessian of a
convex function.

## Main statements

* `ContDiffAt.isBigO_sub_taylor_two` — the second-order Taylor expansion of a `C³` map, with
  cubic remainder.
* `TauCeti.eq_of_isSymmetric_of_isLittleO` — the symmetric second-order term of a Taylor
  expansion is unique.
-/

public section

namespace TauCeti

open Filter Asymptotics Function
open scoped Topology InnerProductSpace

section Existence

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The second-order Taylor expansion of a `C³` map.** If `f` is `C³` at `x`, then
`f x' = f x + Df(x) (x' - x) + ½ D²f(x) (x' - x) (x' - x) + O(‖x' - x‖ ^ 3)`. -/
theorem _root_.ContDiffAt.isBigO_sub_taylor_two {f : E → F} {x : E} (hf : ContDiffAt ℝ 3 f x) :
    (fun x' ↦ f x' - f x - fderiv ℝ f x (x' - x) -
        (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ f) x (x' - x) (x' - x))
      =O[𝓝 x] fun x' ↦ ‖x' - x‖ ^ 3 := by
  let L := fderiv ℝ f x
  let S := fderiv ℝ (fderiv ℝ f) x
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 3 f y := hf.eventually (by simp)
  have hdf : ∀ {y}, ContDiffAt ℝ 3 f y → DifferentiableAt ℝ (fderiv ℝ f) y := fun hy ↦
    (hy.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hsymm : ∀ v w, S v w = S w v :=
    (hf.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField])).eq
  -- The derivative of the remainder, `Df(y) - Df(x) - D²f(x) (y - x)`, is `O(‖y - x‖ ^ 2)`.
  let h : E → E →L[ℝ] F := fun y ↦ fderiv ℝ f y - L - S (y - x)
  have hS : ∀ y, HasFDerivAt (fun y ↦ S (y - x)) S y := fun y ↦
    S.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)
  have hh : h =O[𝓝 x] fun y ↦ ‖y - x‖ ^ ((1 : ℝ) + 1) := by
    refine isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero zero_le_one ?_ ?_ ?_
    · filter_upwards [hev] with y hy
      exact ((hdf hy).sub_const L).sub (hS y).differentiableAt
    · have hfd : ∀ᶠ y in 𝓝 x, fderiv ℝ h y = fderiv ℝ (fderiv ℝ f) y - S := by
        filter_upwards [hev] with y hy
        exact (((hdf hy).hasFDerivAt.sub_const L).sub (hS y)).fderiv
      have h2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
        ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
          (by norm_num)).differentiableAt (by norm_num)
      refine (h2.isBigO_sub.congr' (hfd.mono fun y hy ↦ hy.symm) EventuallyEq.rfl).trans ?_
      simpa using (isBigO_refl (fun y : E ↦ y - x) (𝓝 x)).norm_right
    · simp [h, L]
  -- The remainder vanishes at `x` and has derivative `h`.
  let g : E → F := fun y ↦ f y - f x - L (y - x) - (2⁻¹ : ℝ) • S (y - x) (y - x)
  have hg' : ∀ {y}, ContDiffAt ℝ 3 f y → HasFDerivAt g (h y) y := by
    intro y hy
    have hq : HasFDerivAt (fun y ↦ (2⁻¹ : ℝ) • S (y - x) (y - x)) (S (y - x)) y := by
      refine (((S.hasFDerivAt_apply_self (y - x)).comp y
        ((hasFDerivAt_id y).sub_const x)).const_smul (2⁻¹ : ℝ)).congr_fderiv
          (ContinuousLinearMap.ext fun v ↦ ?_)
      simp only [smul_apply, ContinuousLinearMap.comp_apply, add_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, hsymm v (y - x)]
      module
    exact ((((hy.differentiableAt (by norm_num)).hasFDerivAt.sub_const (f x)).sub
      (L.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x))).sub hq).congr_fderiv
        (by ext v; simp [h])
  have hg : g =O[𝓝 x] fun y ↦ ‖y - x‖ ^ ((1 : ℝ) + 1 + 1) := by
    refine isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero (by norm_num) ?_ ?_ ?_
    · filter_upwards [hev] with y hy
      exact (hg' hy).differentiableAt
    · refine hh.congr' ?_ EventuallyEq.rfl
      filter_upwards [hev] with y hy
      exact (hg' hy).fderiv.symm
    · simp [g]
  exact hg.congr' EventuallyEq.rfl (.of_forall fun y ↦ by norm_num)

end Existence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The symmetric second-order term of a Taylor expansion is unique.** If the real function `u`
has the second-order expansions
`u x' = u x + ⟪y, x' - x⟫ + ⟪A (x' - x), x' - x⟫ / 2 + o(‖x' - x‖ ^ 2)` and the same with `B`, and
`A` and `B` are symmetric, then `A = B`. -/
theorem eq_of_isSymmetric_of_isLittleO {u : E → ℝ} {x y : E} {A B : E →L[ℝ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hTA : (fun x' => u x' - u x - ⟪y, x' - x⟫_ℝ - ⟪A (x' - x), x' - x⟫_ℝ / 2)
      =o[𝓝 x] fun x' => ‖x' - x‖ ^ 2)
    (hTB : (fun x' => u x' - u x - ⟪y, x' - x⟫_ℝ - ⟪B (x' - x), x' - x⟫_ℝ / 2)
      =o[𝓝 x] fun x' => ‖x' - x‖ ^ 2) :
    A = B := by
  -- The quadratic form of `A - B` is `o(‖x' - x‖ ^ 2)`. Restricted to the line through `x` in a
  -- direction `v` it is `t ^ 2 ⟪(A - B) v, v⟫`, so it vanishes, and a symmetric operator with
  -- vanishing quadratic form is zero.
  have hD : (fun x' => ⟪(A - B) (x' - x), x' - x⟫_ℝ) =o[𝓝 x] fun x' => ‖x' - x‖ ^ 2 := by
    refine ((hTB.sub hTA).const_mul_left 2).congr_left fun x' => ?_
    simp only [sub_apply, inner_sub_left]
    ring
  have hq : ∀ v, ⟪(A - B) v, v⟫_ℝ = 0 := fun v => by
    have hlim : Tendsto (fun t : ℝ => x + t • v) (𝓝[≠] 0) (𝓝 x) :=
      ((continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 x
        (by simp)).mono_left nhdsWithin_le_nhds
    have h := ((hD.comp_tendsto hlim).mul_isBigO (isBigO_refl (fun t : ℝ => (t ^ 2)⁻¹) _))
    refine (isLittleO_const_const_iff (c := ‖v‖ ^ 2)).1 (h.congr' ?_ ?_)
    all_goals
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : t ≠ 0 := ht
      simp only [comp_apply, add_sub_cancel_left, map_smul, real_inner_smul_left,
        real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      field_simp
  have h := (hA.sub hB).inner_map_self_eq_zero.1 (by simpa using hq)
  exact sub_eq_zero.1 (ContinuousLinearMap.coe_injective (by simpa using h))

end TauCeti
