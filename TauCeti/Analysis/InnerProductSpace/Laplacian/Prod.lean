/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# The Laplacian in one variable of a function on a product

Let `f : P × E → F` be a function of a parameter `p` in a real normed space `P` and of a point `z`
of a finite-dimensional real inner product space `E`. Its Laplacian in `z` at fixed `p` is
`Δ (fun y ↦ f (p, y)) z`. When `f` is a family of solutions of an elliptic equation in `z`, the
joint derivatives of `f` in `(p, z)` solve the differentiated equations, because the Laplacian in
`z` commutes with joint differentiation:

* `ContDiffAt.laplacian_comp_prodMk_eq_sum`: for an orthonormal basis `b` of `E`, the Laplacian in
  `z` is the sum `∑ᵢ D²f (p, z) ((0, bᵢ), (0, bᵢ))` of second derivatives of `f` along `P × E`;
* `ContDiffAt.laplacian_comp_prodMk_fderiv`: for `f` of class `C³` at `(p, z)`, the Laplacian
  in `z` of the joint derivative `Df` is the joint derivative of the Laplacian in `z` of `f`,
  since both are traces of the symmetric third derivative;
* `ContDiff.laplacian_comp_prodMk_iteratedFDeriv`: for `f` of class `C^(n+2)`, the same holds for
  the joint iterated derivative `Dⁿ f`.

These are the parametric forms of `ContDiffAt.laplacian_fderiv` and
`ContDiff.laplacian_iteratedFDeriv`, which treat the Laplacian on all variables.
-/

public section

noncomputable section

namespace TauCeti

open Filter Topology InnerProductSpace Laplacian

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The Laplacian in the second variable as a sum of second derivatives.** For `f : P × E → F`
of class `C²` at `(p, z)` and an orthonormal basis `b` of `E`,
`Δ (fun y ↦ f (p, y)) z = ∑ᵢ D²f (p, z) (0, bᵢ) (0, bᵢ)`. -/
theorem _root_.ContDiffAt.laplacian_comp_prodMk_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {f : P × E → F} {p : P} {z : E}
    (hf : ContDiffAt ℝ 2 f (p, z)) :
    Δ (fun y ↦ f (p, y)) z = ∑ i, fderiv ℝ (fderiv ℝ f) (p, z) (0, b i) (0, b i) := by
  have hg : ContDiffAt ℝ 2 (fun y ↦ f (p, y)) z := hf.comp z (contDiff_prodMk_right p).contDiffAt
  have hD : DifferentiableAt ℝ (fderiv ℝ (fun y ↦ f (p, y))) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [laplacian_eq_sum_fderiv_fderiv_apply b hD]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fderiv_clm_apply hD (differentiableAt_const _)]
  simpa using fderiv_fderiv_slice_right_apply hf (b i) (b i)

/-- **The Laplacian in the second variable commutes with the joint derivative.** For
`f : P × E → F` of class `C³` at `(p, z)`, the Laplacian in `z` of `Df` is the joint derivative of
`w ↦ Δ (fun y ↦ f (w.1, y)) w.2`: both are traces of the symmetric third derivative. -/
theorem _root_.ContDiffAt.laplacian_comp_prodMk_fderiv {f : P × E → F} {p : P} {z : E}
    (hf : ContDiffAt ℝ 3 f (p, z)) :
    Δ (fun y ↦ fderiv ℝ f (p, y)) z =
      fderiv ℝ (fun w : P × E ↦ Δ (fun y ↦ f (w.1, y)) w.2) (p, z) := by
  let b := stdOrthonormalBasis ℝ E
  have hDf : ContDiffAt ℝ 2 (fderiv ℝ f) (p, z) := hf.fderiv_right (m := 2) (by norm_num)
  -- Near `(p, z)` the Laplacian in the second variable is the trace along `inr`.
  have hΔ : (fun w : P × E ↦ Δ (fun y ↦ f (w.1, y)) w.2) =ᶠ[𝓝 (p, z)]
      fun w ↦ ∑ i, fderiv ℝ (fderiv ℝ f) w (0, b i) (0, b i) := by
    filter_upwards [hf.eventually (by simp)] with w hw
    exact (hw.of_le (by norm_num)).laplacian_comp_prodMk_eq_sum b
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hl := (hDf.comp z (contDiff_prodMk_right p).contDiffAt).laplacian_CLM_comp_left
    (l := ContinuousLinearMap.apply ℝ F v)
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply] at hl
  rw [← hl, (hDf.clm_apply contDiffAt_const).laplacian_comp_prodMk_eq_sum b, hΔ.fderiv_eq,
    fderiv_sum_fderiv_fderiv_apply hf (by simp) (fun i ↦ (0, b i)) v]

/-- **The Laplacian in the second variable commutes with joint iterated derivatives.** For
`f : P × E → F` of class `C^(n+2)`, the Laplacian in `z` of `Dⁿ f` is the `n`-th joint derivative
of `w ↦ Δ (fun y ↦ f (w.1, y)) w.2`. -/
theorem _root_.ContDiff.laplacian_comp_prodMk_iteratedFDeriv {f : P × E → F} {n : ℕ}
    (hf : ContDiff ℝ (n + 2) f) :
    (fun w : P × E ↦ Δ (fun y ↦ iteratedFDeriv ℝ n f (w.1, y)) w.2) =
      iteratedFDeriv ℝ n (fun w : P × E ↦ Δ (fun y ↦ f (w.1, y)) w.2) := by
  induction n with
  | zero =>
    funext w
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact congrFun (laplacian_CLE_comp_left (f := fun y ↦ f (w.1, y))
      (l := (continuousMultilinearCurryFin0 ℝ (P × E) F).symm.toContinuousLinearEquiv)) w.2
  | succ n ih =>
    have hf' : ContDiff ℝ (n + 2) f := hf.of_le (by norm_cast; omega)
    have h3 : ContDiff ℝ 3 (iteratedFDeriv ℝ n f) :=
      hf.iteratedFDeriv_right (by norm_cast; omega)
    funext w
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    let Ψ := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ P × E) F).symm
    have hg : ContDiffAt ℝ 2 (fun y ↦ fderiv ℝ (iteratedFDeriv ℝ n f) (w.1, y)) w.2 :=
      ((h3.fderiv_right (m := 2) (by norm_num)).comp (contDiff_prodMk_right w.1)).contDiffAt
    have hΨ := hg.laplacian_CLM_comp_left (l := Ψ.toContinuousLinearEquiv.toContinuousLinearMap)
    simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      Function.comp_def] at hΨ
    rw [hΨ, h3.contDiffAt.laplacian_comp_prodMk_fderiv, ih hf']

end TauCeti
