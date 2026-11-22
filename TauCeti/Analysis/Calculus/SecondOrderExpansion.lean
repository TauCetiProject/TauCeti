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

More generally, the expansion holds whenever `f` is twice differentiable near `x` and its second
derivative is Lipschitz at `x`, i.e. `D²f(x') - D²f(x) = O(‖x' - x‖)`. The remainder vanishes at
`x`, and since the second derivative is symmetric its derivative is
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

* `TauCeti.isBigO_sub_taylor_two_of_hasFDerivAt` — the second-order Taylor expansion, with cubic
  remainder, of a twice differentiable map whose second derivative is Lipschitz at the point.
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

/-- **The second-order Taylor expansion with cubic remainder.** If `f` has derivative `f'` and
`f'` has derivative `f''` near `x`, and `f''` is Lipschitz at `x` in the sense that
`f'' y - f'' x = O(‖y - x‖)`, then
`f x' = f x + f' x (x' - x) + ½ f'' x (x' - x) (x' - x) + O(‖x' - x‖ ^ 3)`. -/
theorem isBigO_sub_taylor_two_of_hasFDerivAt {f : E → F} {f' : E → E →L[ℝ] F}
    {f'' : E → E →L[ℝ] E →L[ℝ] F} {x : E} (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hf' : ∀ᶠ y in 𝓝 x, HasFDerivAt f' (f'' y) y)
    (hf'' : (fun y ↦ f'' y - f'' x) =O[𝓝 x] fun y ↦ y - x) :
    (fun x' ↦ f x' - f x - f' x (x' - x) - (2⁻¹ : ℝ) • f'' x (x' - x) (x' - x))
      =O[𝓝 x] fun x' ↦ ‖x' - x‖ ^ 3 := by
  let S := f'' x
  have hsymm : ∀ v w, S v w = S w v :=
    second_derivative_symmetric_of_eventually hf hf'.self_of_nhds
  have hS : ∀ y, HasFDerivAt (fun y ↦ S (y - x)) S y := fun y ↦
    S.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)
  -- The derivative of the remainder, `f' y - f' x - f'' x (y - x)`, is `O(‖y - x‖ ^ 2)`.
  let h : E → E →L[ℝ] F := fun y ↦ f' y - f' x - S (y - x)
  have hh' : ∀ᶠ y in 𝓝 x, HasFDerivAt h (f'' y - S) y := by
    filter_upwards [hf'] with y hy
    exact (hy.sub_const (f' x)).sub (hS y)
  have hh : h =O[𝓝 x] fun y ↦ ‖y - x‖ ^ ((1 : ℝ) + 1) := by
    refine isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero zero_le_one
      (hh'.mono fun y hy ↦ hy.differentiableAt) ?_ (by simp [h])
    refine (hf''.congr' (hh'.mono fun y hy ↦ hy.fderiv.symm) EventuallyEq.rfl).trans ?_
    simpa using (isBigO_refl (fun y : E ↦ y - x) (𝓝 x)).norm_right
  -- The remainder vanishes at `x` and has derivative `h`.
  let g : E → F := fun y ↦ f y - f x - f' x (y - x) - (2⁻¹ : ℝ) • S (y - x) (y - x)
  have hg' : ∀ᶠ y in 𝓝 x, HasFDerivAt g (h y) y := by
    filter_upwards [hf] with y hy
    have hq : HasFDerivAt (fun y ↦ (2⁻¹ : ℝ) • S (y - x) (y - x)) (S (y - x)) y := by
      refine (((S.hasFDerivAt_apply_self (y - x)).comp y
        ((hasFDerivAt_id y).sub_const x)).const_smul (2⁻¹ : ℝ)).congr_fderiv
          (ContinuousLinearMap.ext fun v ↦ ?_)
      simp only [smul_apply, ContinuousLinearMap.comp_apply, add_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, hsymm v (y - x)]
      module
    exact (((hy.sub_const (f x)).sub
      ((f' x).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x))).sub hq).congr_fderiv
        (by ext v; simp [h])
  have hg : g =O[𝓝 x] fun y ↦ ‖y - x‖ ^ ((1 : ℝ) + 1 + 1) := by
    refine isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero (by norm_num)
      (hg'.mono fun y hy ↦ hy.differentiableAt) ?_ (by simp [g])
    exact hh.congr' (hg'.mono fun y hy ↦ hy.fderiv.symm) EventuallyEq.rfl
  exact hg.congr' EventuallyEq.rfl (.of_forall fun y ↦ by norm_num)

/-- **The second-order Taylor expansion of a `C³` map.** If `f` is `C³` at `x`, then
`f x' = f x + Df(x) (x' - x) + ½ D²f(x) (x' - x) (x' - x) + O(‖x' - x‖ ^ 3)`. -/
theorem _root_.ContDiffAt.isBigO_sub_taylor_two {f : E → F} {x : E} (hf : ContDiffAt ℝ 3 f x) :
    (fun x' ↦ f x' - f x - fderiv ℝ f x (x' - x) -
        (2⁻¹ : ℝ) • fderiv ℝ (fderiv ℝ f) x (x' - x) (x' - x))
      =O[𝓝 x] fun x' ↦ ‖x' - x‖ ^ 3 := by
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 3 f y := hf.eventually (by simp)
  refine isBigO_sub_taylor_two_of_hasFDerivAt (hev.mono fun y hy ↦
    (hy.differentiableAt (by norm_num)).hasFDerivAt) (hev.mono fun y hy ↦
      ((hy.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt) ?_
  exact (((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
    (by norm_num)).differentiableAt (by norm_num)).isBigO_sub

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
      (Continuous.tendsto' (by fun_prop) 0 x (by simp)).mono_left nhdsWithin_le_nhds
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
