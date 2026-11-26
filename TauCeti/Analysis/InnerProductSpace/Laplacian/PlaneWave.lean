/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.InnerProductSpace.LinearMap
import TauCeti.Analysis.Calculus.FDeriv.Comp
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Plane-wave derivatives and Laplacian eigenvalues

A plane wave on a real inner product space `F` is a function `x ↦ g ⟪w, x⟫` of one linear
coordinate, constant on the hyperplanes orthogonal to `w`. Its derivative is
`v ↦ ⟪w, v⟫ • g'(⟪w, x⟫)` for every `g`: when `w ≠ 0`, the map `x ↦ ⟪w, x⟫` has a continuous
linear right inverse, so the plane wave is differentiable at `x` exactly when `g` is
differentiable at `⟪w, x⟫`. Its second derivative is `g''(⟪w, x⟫) ⟪w, v⟫ ⟪w, v'⟫`, and on a
finite-dimensional space its Laplacian is `‖w‖² • g''(⟪w, x⟫)`, again for every `g`, with values
in any real normed space. For `g = cos` and `g = sin` these are the Fourier modes
`cos ⟪w, x⟫` and `sin ⟪w, x⟫`, satisfying `Δ f = -‖w‖² f`. The cosine mode is an
eigenfunction of `-Δ` with eigenvalue `‖w‖²`, so `Δ^[r]` multiplies it by `(-‖w‖²) ^ r`; the
sine mode is one when `w ≠ 0`. Each derivative of the cosine mode brings out one factor `⟪w, ·⟫`
and a derivative of `cos`, bounded by `1`, so its `m`-th derivative has norm at most `‖w‖ ^ m`.
The hyperbolic mode `cosh ⟪w, x - x₀⟫` is an eigenfunction of `Δ` with eigenvalue `‖w‖²`.

Adapted from Giada Franz's formalization in
[`ForTauCeti/Analysis/Fourier/Torus/PlaneWave.lean`](https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/master/ForTauCeti/Analysis/Fourier/Torus/PlaneWave.lean).

## Main results

* `TauCeti.fderiv_comp_inner`: the derivative of a plane wave.
* `TauCeti.iteratedFDeriv_two_comp_inner`: the second derivative of a plane wave.
* `TauCeti.norm_iteratedFDeriv_cos_inner_le`: `‖D^m cos ⟪w, ·⟫‖ ≤ ‖w‖ ^ m`.
* `TauCeti.laplacian_comp_inner`: the Laplacian of a plane wave `x ↦ g ⟪w, x⟫` is `‖w‖² • g''`;
  `TauCeti.laplacian_comp_inner_sub` is its shifted form `x ↦ g ⟪w, x - x₀⟫`.
* `TauCeti.laplacian_cos_inner`, `TauCeti.laplacian_sin_inner`: the Laplacian identities for
  the Fourier modes, with the sine eigenfunction interpretation requiring `w ≠ 0`.
* `TauCeti.iterate_laplacian_cos_inner`: `Δ^[r] cos ⟪w, ·⟫ = (-‖w‖²) ^ r cos ⟪w, ·⟫`.
* `TauCeti.laplacian_cosh_inner_sub`: the shifted hyperbolic mode is an eigenfunction of `Δ`.
-/

public section

open InnerProductSpace
open scoped InnerProductSpace Laplacian

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- The derivative of a plane wave `z ↦ g ⟪w, z⟫` is `v ↦ ⟪w, v⟫ • g' ⟪w, y⟫`, with no
differentiability hypothesis on `g`. -/
theorem fderiv_comp_inner (g : ℝ → G) (w y : F) :
    fderiv ℝ (fun z ↦ g ⟪w, z⟫_ℝ) y = (innerSL ℝ w).smulRight (deriv g ⟪w, y⟫_ℝ) := by
  rcases eq_or_ne w 0 with rfl | hw
  · ext v
    simp
  -- `t ↦ t • w / ‖w‖²` is a continuous linear right inverse of `z ↦ ⟪w, z⟫`.
  have hs : Function.RightInverse (ContinuousLinearMap.toSpanSingleton ℝ ((‖w‖ ^ 2)⁻¹ • w))
      (innerSL ℝ w) := fun t ↦ by
    simp [hw]
  have h := (innerSL ℝ w).fderiv_comp_right_of_rightInverse _ hs g y
  simp only [Function.comp_def, coe_innerSL_apply] at h
  ext v
  simp [h, fderiv_eq_smul_deriv]

/-- The second derivative of the plane wave `x ↦ g ⟪w, x⟫` is
`g''(⟪w, x⟫) ⟪w, v⟫ ⟪w, v'⟫`. -/
theorem iteratedFDeriv_two_comp_inner {g : ℝ → ℝ} (w x : F)
    (hg : ContDiffAt ℝ 2 g ⟪w, x⟫_ℝ) (v v' : F) :
    iteratedFDeriv ℝ 2 (fun y ↦ g ⟪w, y⟫_ℝ) x ![v, v'] =
      iteratedDeriv 2 g ⟪w, x⟫_ℝ * ⟪w, v⟫_ℝ * ⟪w, v'⟫_ℝ := by
  obtain ⟨s, hs, hgs⟩ := hg.contDiffOn le_rfl (by norm_num)
  obtain ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp hs
  have h := (innerSL ℝ w).iteratedFDerivWithin_comp_right (hgs.mono hus)
    hu.uniqueDiffOn (hu.preimage (innerSL ℝ w).continuous).uniqueDiffOn hxu (i := 2) le_rfl
  rw [iteratedFDerivWithin_of_isOpen _ (hu.preimage (innerSL ℝ w).continuous) hxu] at h
  simp only [innerSL_apply_apply] at h
  rw [iteratedFDerivWithin_of_isOpen _ hu hxu] at h
  have hcomp : (fun y ↦ g ⟪w, y⟫_ℝ) = g ∘ innerSL ℝ w := by
    simp only [Function.comp_def, innerSL_apply_apply]
  rw [hcomp, h, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  simp only [innerSL_apply_apply, Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, smul_eq_mul]
  ring

/-- The cosine mode `y ↦ cos ⟪w, y⟫` is `cos` composed with the linear form `⟪w, ·⟫`. -/
private theorem cos_inner_eq_comp (w : F) :
    (fun y ↦ Real.cos ⟪w, y⟫_ℝ) = Real.cos ∘ innerSL ℝ w :=
  funext fun y ↦ by rw [Function.comp_apply, innerSL_apply_apply]

/-- The `m`-th derivative of the cosine mode `y ↦ cos ⟪w, y⟫` has norm at most `‖w‖ ^ m`. -/
theorem norm_iteratedFDeriv_cos_inner_le (w x : F) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y ↦ Real.cos ⟪w, y⟫_ℝ) x‖ ≤ ‖w‖ ^ m := by
  rw [cos_inner_eq_comp, (innerSL ℝ w).iteratedFDeriv_comp_right (Real.contDiff_cos (n := m)) x
    le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, innerSL_apply_norm]
  have hcos : ‖iteratedFDeriv ℝ m Real.cos (innerSL ℝ w x)‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact Real.abs_iteratedDeriv_cos_le_one m _
  calc _ ≤ 1 * ‖w‖ ^ m := by gcongr
    _ = ‖w‖ ^ m := one_mul _

variable [FiniteDimensional ℝ F]

/-- **The Laplacian of a plane wave.** For a vector `w` and a function `g : ℝ → G`, the function
`z ↦ g ⟪w, z⟫`, constant on the hyperplanes orthogonal to `w`, has Laplacian `‖w‖² g'' (⟪w, y⟫)`
at `y`, with no differentiability hypothesis on `g`. -/
theorem laplacian_comp_inner (g : ℝ → G) (w y : F) :
    Δ (fun z ↦ g ⟪w, z⟫_ℝ) y = ‖w‖ ^ 2 • deriv (deriv g) ⟪w, y⟫_ℝ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  set Ψ := ContinuousLinearMap.smulRightL ℝ ℝ ℝ F G (innerSL ℝ w)
  have hD : fderiv ℝ (fun z ↦ g ⟪w, z⟫_ℝ) = fun z ↦ Ψ (deriv g ⟪w, z⟫_ℝ) := by
    funext z
    rw [fderiv_comp_inner, ContinuousLinearMap.smulRightL_apply_apply]
  -- `Ψ` has the left inverse given by evaluation at `w / ‖w‖²`, so it commutes with `fderiv`.
  have hΨ : Function.LeftInverse (ContinuousLinearMap.apply ℝ G ((‖w‖ ^ 2)⁻¹ • w)) Ψ :=
    fun a ↦ by simp [Ψ, hw]
  have hD2 := Ψ.fderiv_comp_left_of_leftInverse _ hΨ (fun z ↦ deriv g ⟪w, z⟫_ℝ) y
  rw [Function.comp_def] at hD2
  rw [laplacian_eq_traceL, ContinuousLinearMap.traceL_apply, hD, hD2, fderiv_comp_inner]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, Ψ, ContinuousLinearMap.smulRightL_apply_apply,
    smul_smul, ← Finset.sum_smul]
  rw [← (stdOrthonormalBasis ℝ F).sum_sq_inner_left w]
  simp_rw [sq]

/-- **The Laplacian of a shifted plane wave.** For vectors `w` and `x` and a function
`g : ℝ → G`, the function `z ↦ g ⟪w, z - x⟫` has Laplacian `‖w‖² g'' (⟪w, y - x⟫)` at `y`. -/
theorem laplacian_comp_inner_sub (g : ℝ → G) (w x y : F) :
    Δ (fun z ↦ g ⟪w, z - x⟫_ℝ) y = ‖w‖ ^ 2 • deriv (deriv g) ⟪w, y - x⟫_ℝ := by
  have h := congrFun (laplacian_comp_add_right (fun z ↦ g ⟪w, z⟫_ℝ) (-x)) y
  simp only [← sub_eq_add_neg] at h
  rw [h, laplacian_comp_inner]

/-- The cosine mode `cos ⟪w, ·⟫` is an eigenfunction of `-Δ` with eigenvalue `‖w‖²`. -/
theorem laplacian_cos_inner (w x : F) :
    Δ (fun y ↦ Real.cos ⟪w, y⟫_ℝ) x = -‖w‖ ^ 2 * Real.cos ⟪w, x⟫_ℝ := by
  simp [laplacian_comp_inner, Real.deriv_cos']

/-- **The iterated Laplacians of the cosine mode.** For `w ∈ F` and `r : ℕ`,
`Δ^[r] cos ⟪w, ·⟫ = (-‖w‖ ^ 2) ^ r cos ⟪w, ·⟫`. -/
theorem iterate_laplacian_cos_inner (w : F) (r : ℕ) :
    Δ^[r] (fun y ↦ Real.cos ⟪w, y⟫_ℝ) = fun y ↦ (-‖w‖ ^ 2) ^ r * Real.cos ⟪w, y⟫_ℝ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    have hsmul : (fun y ↦ (-‖w‖ ^ 2) ^ r * Real.cos ⟪w, y⟫_ℝ) =
        (-‖w‖ ^ 2) ^ r • fun y ↦ Real.cos ⟪w, y⟫_ℝ := (rfl)
    rw [hsmul, laplacian_smul _ (by rw [cos_inner_eq_comp]; fun_prop), smul_eq_mul,
      laplacian_cos_inner]
    ring

/-- The sine mode satisfies `Δ (sin ⟪w, ·⟫) = -‖w‖² sin ⟪w, ·⟫`. When `w ≠ 0`, it is
an eigenfunction of `-Δ` with eigenvalue `‖w‖²`. -/
theorem laplacian_sin_inner (w x : F) :
    Δ (fun y ↦ Real.sin ⟪w, y⟫_ℝ) x = -‖w‖ ^ 2 * Real.sin ⟪w, x⟫_ℝ := by
  simp [laplacian_comp_inner, Real.deriv_cos']

/-- The shifted hyperbolic mode `cosh ⟪w, · - x⟫` is an eigenfunction of `Δ` with eigenvalue
`‖w‖²`. -/
theorem laplacian_cosh_inner_sub (w x y : F) :
    Δ (fun z ↦ Real.cosh ⟪w, z - x⟫_ℝ) y = ‖w‖ ^ 2 * Real.cosh ⟪w, y - x⟫_ℝ := by
  simp [laplacian_comp_inner_sub]

end TauCeti
