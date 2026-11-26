/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic

/-!
# Parameter derivatives of holomorphic families

Let `h : E → V → W` be a family of maps from a complex normed space `V` to a complex normed space
`W`, depending on a parameter in a real normed space `E`. If `h` is jointly `C^(k+1)` and each
`h y` is holomorphic, then every parameter derivative `w ↦ D_yᵏ h (y, w)` is again holomorphic in
`w`, as a map into the complex normed space of `k`-multilinear maps on `E`.

For `k = 1` this is the symmetry of mixed second derivatives: the derivative in `w` of
`D_y h (y, w)` in the direction `u` is `D_y (D_w h (y, w) u)`, and `D_w h (y, w)` commutes with
multiplication by `i` for every `y`, hence so does its derivative in `y`. The higher derivatives
follow by induction, since `D_y^(k+1) h` is the derivative in `y` of `D_yᵏ h`.

This is what lets an operator built from point evaluations and fixed holomorphic functions, such
as a finite-rank Runge approximation operator in one variable, be applied to every parameter
derivative of a smooth family of holomorphic functions.

## Main results

* `TauCeti.differentiableAt_fderiv_slice`: the parameter derivative of a jointly `C²` family that
  is holomorphic at `z` for nearby parameters is holomorphic at `z`.
* `TauCeti.differentiableAt_iteratedFDeriv_slice`: the same for the `k`-th parameter derivative of
  a jointly `C^(k+1)` family.
* `ContDiffOn.differentiableOn_iteratedFDeriv_slice`: on open sets, the `k`-th parameter
  derivative of a jointly `C^n` family of holomorphic maps, `k + 1 ≤ n`, is holomorphic.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Chapter I, §1.2 (differentiation of holomorphic families in a parameter).
-/

public section

open Complex Filter Topology

namespace TauCeti

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **Parameter derivatives of holomorphic families are holomorphic.** Let `h : E → V → W` be
jointly `C²` at `(x, z)`, and let `h y` be complex differentiable at `z` for every `y` near `x`.
Then the parameter derivative `w ↦ D_y h (x, w)` is complex differentiable at `z`. -/
theorem differentiableAt_fderiv_slice {h : E → V → W} {x : E} {z : V}
    (hh : ContDiffAt ℝ 2 (Function.uncurry h) (x, z))
    (hz : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ (h y) z) :
    DifferentiableAt ℂ (fun w ↦ fderiv ℝ (fun y ↦ h y w) x) z := by
  -- Put the holomorphic variable first, as the parameter of the mixed-derivative identity.
  have hF : ContDiffAt ℝ (minSmoothness ℝ 2) (fun p : V × E ↦ h p.2 p.1) (z, x) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact hh.comp (z, x) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hD := hasFDerivAt_spatialFDeriv hF
  -- `φ y` is the derivative of `h y` at `z`; it commutes with `I` for `y` near `x`.
  set φ : E → V →L[ℝ] W := fun y ↦ fderiv ℝ (h y) z
  have hφ : DifferentiableAt ℝ φ x :=
    (hh.fderiv (contDiffAt_const (c := z)) (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hφI (u : V) (v : E) : fderiv ℝ φ x v (I • u) = I • fderiv ℝ φ x v u := by
    let T : (V →L[ℝ] W) →L[ℝ] W :=
      ContinuousLinearMap.apply ℝ W (I • u) - I • ContinuousLinearMap.apply ℝ W u
    have h0 : (fun y ↦ T (φ y)) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [hz] with y hy
      simp [T, φ, hy.fderiv_restrictScalars_smul ℝ]
    have hT := (T.hasFDerivAt.comp x hφ.hasFDerivAt).unique
      ((hasFDerivAt_const (0 : W) x).congr_of_eventuallyEq h0)
    simpa [T, sub_eq_zero] using congr($hT v)
  refine (differentiableAt_iff_conjWirtingerDeriv_eq_zero hD.differentiableAt).2 ?_
  ext u v
  simp [conjWirtingerDeriv_apply, hD.fderiv, hφI, φ, smul_smul, mul_assoc]

/-- **Iterated parameter derivatives of holomorphic families are holomorphic.** Let
`h : E → V → W` be jointly `C^(k+1)` at `(x, z)`, and let `h y` be complex differentiable at `z`
for every `y` near `x`. Then the `k`-th parameter derivative `w ↦ D_yᵏ h (x, w)` is complex
differentiable at `z`, as a map into the complex normed space of `k`-multilinear maps on `E`. -/
theorem differentiableAt_iteratedFDeriv_slice {k : ℕ} {h : E → V → W} {x : E} {z : V}
    (hh : ContDiffAt ℝ (k + 1) (Function.uncurry h) (x, z))
    (hz : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ (h y) z) :
    DifferentiableAt ℂ (fun w ↦ iteratedFDeriv ℝ k (fun y ↦ h y w) x) z := by
  induction k generalizing x with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact ContinuousLinearMap.differentiableAt_comp_of_map_smul
      (continuousMultilinearCurryFin0 ℝ E W).symm.toContinuousLinearEquiv.toContinuousLinearMap
      (fun c v ↦ by ext; simp)
      hz.self_of_nhds
  | succ k ih =>
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    -- `H y w = D_yᵏ h (y, w)` is jointly `C²` at `(x, z)`: near `(x, z)` it is the `k`-th
    -- derivative of `h` restricted to the parameter directions.
    let H : E → V → ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) W :=
      fun y w ↦ iteratedFDeriv ℝ k (fun y' ↦ h y' w) y
    have hH : ContDiffAt ℝ 2 (Function.uncurry H) (x, z) := by
      refine ((ContinuousMultilinearMap.compContinuousLinearMapL
        fun _ ↦ ContinuousLinearMap.inl ℝ E V).contDiff.contDiffAt.comp (x, z)
          (hh.iteratedFDeriv_right (m := 2) (i := k) (by norm_cast; omega))).congr_of_eventuallyEq
        ?_
      filter_upwards [hh.eventually (by simp)] with q hq
      exact hq.iteratedFDeriv_prod_left k (by norm_cast; omega)
    -- Near `x`, the induction hypothesis applies at every parameter value.
    have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ (k + 1 + 1) (Function.uncurry h) (y, z) :=
      (continuousAt_id.prodMk continuousAt_const).eventually (hh.eventually (by simp))
    have hHz : DifferentiableAt ℂ (fun w ↦ fderiv ℝ (fun y ↦ H y w) x) z := by
      refine differentiableAt_fderiv_slice (h := H) hH ?_
      filter_upwards [hev, hz.eventually_nhds] with y hy hyz
      exact ih (hy.of_le (by norm_cast; omega)) hyz
    -- Currying the first variable commutes with complex scalars.
    let T : (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) W) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) ↦ E) W :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) W).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap
    have hT (c : ℂ) (L : E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) W) :
        T (c • L) = c • T L := by
      ext m
      simp only [T, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        continuousMultilinearCurryLeftEquiv_symm_apply, smul_apply]
    exact ContinuousLinearMap.differentiableAt_comp_of_map_smul (𝕜 := ℝ) (𝕜' := ℂ)
      (X := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) W)
      (Y := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) ↦ E) W) T hT hHz

/-- **Parameter derivatives of holomorphic families on open sets.** Let `h : E → V → W` be jointly
`C^n` on `s ×ˢ U` for open sets `s` and `U`, with each `h y`, `y ∈ s`, holomorphic on `U`. Then
for `k + 1 ≤ n` and `x ∈ s`, the `k`-th parameter derivative `w ↦ D_yᵏ h (x, w)` is holomorphic
on `U`. -/
theorem _root_.ContDiffOn.differentiableOn_iteratedFDeriv_slice {n : WithTop ℕ∞} {k : ℕ}
    {h : E → V → W} {s : Set E} {U : Set V} (hh : ContDiffOn ℝ n (Function.uncurry h) (s ×ˢ U))
    (hs : IsOpen s) (hU : IsOpen U) (hhU : ∀ y ∈ s, DifferentiableOn ℂ (h y) U)
    (hk : (k + 1 : WithTop ℕ∞) ≤ n) {x : E} (hx : x ∈ s) :
    DifferentiableOn ℂ (fun w ↦ iteratedFDeriv ℝ k (fun y ↦ h y w) x) U := by
  intro z hz
  refine (differentiableAt_iteratedFDeriv_slice
    ((hh.contDiffAt ((hs.prod hU).mem_nhds ⟨hx, hz⟩)).of_le hk) ?_).differentiableWithinAt
  filter_upwards [hs.mem_nhds hx] with y hy
  exact (hhU y hy).differentiableAt (hU.mem_nhds hz)

end TauCeti
