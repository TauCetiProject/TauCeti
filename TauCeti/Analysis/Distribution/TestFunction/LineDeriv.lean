/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Directional derivatives of test functions

Mathlib equips the test functions `𝓓(Ω, F)` with the directional derivative `∂_{v}`. This file
evaluates it pointwise as the classical directional derivative, and shows that two directional
derivatives of a test function commute, `∂_{v} (∂_{w} φ) = ∂_{w} (∂_{v} φ)`, because the second
derivative of a smooth function is symmetric. Moving derivatives between the two sides of an
integration-by-parts identity uses exactly this, for instance to show that weak derivatives
commute. Summing over an orthonormal basis, the Laplacian of a test function commutes with every
directional derivative. Finally, a test function on `Ω` times a function smooth on `Ω` is again a
test function, with the classical product rule for its directional derivatives; this is what lets
a weak derivative be tested against `g φ` when `g` is only smooth inside `Ω`.

## Main declarations

* `TestFunction.lineDerivOp_apply`: `∂_{v} φ` is the classical directional derivative of `φ`.
* `TestFunction.lineDerivOp_one_apply_eq_deriv`: on the real line, `∂_{1} φ` is the derivative
  of `φ`.
* `TestFunction.lineDerivCLM_postcompCLM`: directional derivatives commute with postcomposition
  by a continuous linear map.
* `TestFunction.lineDerivOp_comm` and `TestFunction.lineDeriv_lineDerivOp_comm`: directional
  derivatives of test functions commute.
* `TestFunction.lineDerivOp_laplacianCLM`: the Laplacian of test functions commutes with
  directional derivatives.
* `TestFunction.exists_coe_eq_smul_of_contDiffOn`: the product of a test function on `Ω` with a
  function smooth on `Ω` is a test function on `Ω`.
* `TestFunction.lineDeriv_fun_smul_of_differentiableOn`: its directional derivatives obey the
  product rule.
* `TestFunction.laplacianCLM_apply`: the test-function Laplacian agrees pointwise with the
  classical Laplacian.
-/

public section

namespace TestFunction

open LineDeriv TopologicalSpace
open scoped ContDiff Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- The directional derivative of a test function is its classical directional derivative. -/
@[simp]
theorem lineDerivOp_apply (φ : 𝓓(Ω, F)) (v x : E) : ∂_{v} φ x = lineDeriv ℝ φ x v :=
  lineDerivCLM_apply_of_le le_top

/-- On the real line, the directional derivative of a test function in the direction `1` is its
derivative. -/
theorem lineDerivOp_one_apply_eq_deriv {Ω : Opens ℝ} (φ : 𝓓(Ω, F)) (x : ℝ) :
    ∂_{(1 : ℝ)} φ x = deriv φ x := by
  rw [lineDerivOp_apply, (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv,
    fderiv_apply_one_eq_deriv]

/-- The underlying function of a directional derivative of a test function is its classical
directional derivative. -/
@[simp]
theorem coe_lineDerivCLM (φ : 𝓓(Ω, F)) (v : E) :
    ⇑(lineDerivCLM ℝ v φ : 𝓓(Ω, F)) = fun x ↦ lineDeriv ℝ (φ : E → F) x v :=
  funext fun _ ↦ lineDerivCLM_apply_of_le le_top

/-- Directional derivatives of test functions commute with postcomposition by a continuous linear
map, at every pair of orders. -/
theorem lineDerivCLM_postcompCLM {𝕜 : Type*} [NontriviallyNormedField 𝕜] [Algebra ℝ 𝕜]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] {n k : ℕ∞} {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [IsScalarTower ℝ 𝕜 F'] (L : F →L[𝕜] F') (v : E)
    (φ : 𝓓^{n}(Ω, F)) :
    (lineDerivCLM 𝕜 v (postcompCLM L φ) : 𝓓^{k}(Ω, F')) = postcompCLM L (lineDerivCLM 𝕜 v φ) := by
  ext x
  simp only [lineDerivCLM_eq_fderivCLM, fderivCLM_apply, postcompCLM_apply, Function.comp_apply]
  split_ifs with hk
  · have hn : (n : WithTop ℕ∞) ≠ 0 := by
      have : (0 : ℕ∞) < n := (add_pos_of_right zero_lt_one k).trans_le hk
      exact_mod_cast this.ne'
    have hφ : DifferentiableAt ℝ φ x := (φ.contDiff.differentiable hn).differentiableAt
    have hL := ((L.restrictScalars ℝ).hasFDerivAt.comp x hφ.hasFDerivAt).fderiv
    rw [ContinuousLinearMap.coe_restrictScalars'] at hL
    rw [hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  · simp

/-- Iterated directional derivatives of a test function agree with its iterated Fréchet
derivatives evaluated in those directions. -/
theorem lineDeriv_lineDeriv_eq_fderiv_fderiv (φ : 𝓓(Ω, F)) (v w x : E) :
    lineDeriv ℝ (fun y ↦ lineDeriv ℝ (φ : E → F) y v) x w =
      fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → F) y v) x w := by
  have hφ : ∀ y, lineDeriv ℝ (φ : E → F) y v = fderiv ℝ (φ : E → F) y v := fun y ↦
    (φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv
  simp_rw [hφ]
  exact (((φ.contDiff.fderiv_right (by simp)).clm_apply contDiff_const).differentiable
    one_ne_zero x).lineDeriv_eq_fderiv

/-- **Directional derivatives of test functions commute.** -/
theorem lineDerivOp_comm (φ : 𝓓(Ω, F)) (v w : E) : ∂_{v} (∂_{w} φ) = ∂_{w} (∂_{v} φ) := by
  ext x
  have hd : DifferentiableAt ℝ (fderiv ℝ (φ : E → F)) x :=
    (φ.contDiff.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero x
  rw [lineDerivOp_apply, lineDerivOp_apply]
  simp only [lineDerivOp_eq_lineDerivCLM ℝ]
  rw [coe_lineDerivCLM, coe_lineDerivCLM,
    lineDeriv_lineDeriv_eq_fderiv_fderiv, lineDeriv_lineDeriv_eq_fderiv_fderiv]
  simpa [fderiv_clm_apply hd (differentiableAt_const _)] using
    ((φ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)).eq v w

/-- The classical directional derivative of `∂_{v} φ` in the direction `w` is that of `∂_{w} φ`
in the direction `v`. -/
theorem lineDeriv_lineDerivOp_comm (φ : 𝓓(Ω, F)) (v w x : E) :
    lineDeriv ℝ (∂_{v} φ : 𝓓(Ω, F)) x w = lineDeriv ℝ (∂_{w} φ : 𝓓(Ω, F)) x v := by
  rw [← lineDerivOp_apply, ← lineDerivOp_apply, lineDerivOp_comm]

/-! ### Multiplication by a function smooth on `Ω` -/

/-- **A test function times a function smooth on `Ω` is a test function.** If `g` is smooth on
`Ω`, with no condition off `Ω`, and `φ ∈ 𝓓(Ω, F)`, then `x ↦ g x • φ x` is again a test function
on `Ω`: it is smooth on `Ω` and vanishes on the open complement of `tsupport φ`, and these two
open sets cover `E`. -/
theorem exists_coe_eq_smul_of_contDiffOn {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g Ω) (φ : 𝓓(Ω, F)) :
    ∃ ψ : 𝓓(Ω, F), ⇑ψ = fun x => g x • φ x := by
  have hsmooth : ContDiff ℝ ∞ fun x => g x • φ x := by
    refine contDiff_of_contDiffOn_union_of_isOpen (hg.smul φ.contDiff.contDiffOn)
      ((contDiffOn_const (c := (0 : F))).congr fun x hx => ?_) ?_ Ω.isOpen
      (isClosed_tsupport (φ : E → F)).isOpen_compl
    · simp [image_eq_zero_of_notMem_tsupport (f := (φ : E → F)) hx]
    · exact Set.eq_univ_of_forall fun x => (em (x ∈ tsupport φ)).imp (φ.tsupport_subset ·) id
  exact ⟨⟨fun x => g x • φ x, hsmooth, φ.hasCompactSupport.smul_left,
    (tsupport_smul_subset_right _ _).trans φ.tsupport_subset⟩, rfl⟩

/-- **The product rule for a test function times a function differentiable on `Ω`**:
`∂_v (g φ) = g ∂_v φ + (∂_v g) φ` at every point of `E`. Off `tsupport φ` both sides vanish, so
nothing is needed of `g` outside `Ω`. -/
theorem lineDeriv_fun_smul_of_differentiableOn {g : E → ℝ} (hg : DifferentiableOn ℝ g Ω)
    (φ : 𝓓(Ω, F)) (x v : E) :
    lineDeriv ℝ (fun y => g y • φ y) x v = g x • lineDeriv ℝ φ x v + fderiv ℝ g x v • φ x := by
  have hφx : DifferentiableAt ℝ φ x := φ.contDiff.differentiable (by simp) x
  by_cases hx : x ∈ tsupport φ
  · have hgx : DifferentiableAt ℝ g x :=
      hg.differentiableAt (Ω.isOpen.mem_nhds (φ.tsupport_subset hx))
    rw [(hgx.fun_smul hφx).lineDeriv_eq_fderiv, hφx.lineDeriv_eq_fderiv, fderiv_fun_smul hgx hφx]
    simp
  · -- Near `x` both `φ` and `g φ` vanish identically.
    have hnhds : (tsupport φ)ᶜ ∈ nhds x := (isClosed_tsupport φ).isOpen_compl.mem_nhds hx
    have h0 : (fun y => g y • φ y) =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [hnhds] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    have hφ0 : (φ : E → F) =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [hnhds] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    rw [(((hasFDerivAt_const (0 : F) x).congr_of_eventuallyEq h0).hasLineDerivAt v).lineDeriv,
      (((hasFDerivAt_const (0 : F) x).congr_of_eventuallyEq hφ0).hasLineDerivAt v).lineDeriv,
      image_eq_zero_of_notMem_tsupport hx]
    simp

end TestFunction

namespace TestFunction

open LineDeriv TopologicalSpace
open scoped Distributions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- **The Laplacian of test functions commutes with directional derivatives**:
`∂_{v} (Δφ) = Δ (∂_{v} φ)`. -/
theorem lineDerivOp_laplacianCLM (φ : 𝓓(Ω, F)) (v : E) :
    ∂_{v} (laplacianCLM ℝ E 𝓓(Ω, F) φ) = laplacianCLM ℝ E 𝓓(Ω, F) (∂_{v} φ) := by
  simp only [laplacianCLM_eq_sum (stdOrthonormalBasis ℝ E), lineDerivOp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lineDerivOp_comm, lineDerivOp_comm φ v]

open InnerProductSpace Laplacian in
/-- The test-function Laplacian agrees pointwise with the classical Laplacian. -/
@[simp]
theorem laplacianCLM_apply (φ : 𝓓(Ω, F)) (x : E) :
    (laplacianCLM ℝ E (𝓓(Ω, F)) φ) x = Δ (φ : E → F) x := by
  have hcoe (v : E) : ⇑(lineDerivCLM ℝ v φ : 𝓓(Ω, F)) =
      fun y ↦ fderiv ℝ (φ : E → F) y v := by
    funext y
    rw [lineDerivCLM_eq_fderivCLM, fderivCLM_apply_of_le _ le_top]
  simp only [LineDeriv.laplacianCLM, sum_apply,
    ContinuousLinearMap.comp_apply, lineDerivOpCLM_eq_lineDerivCLM,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [lineDerivCLM_eq_fderivCLM, fderivCLM_apply_of_le _ le_top, hcoe,
    fderiv_clm_apply ((φ.contDiff.fderiv_right (by simp)).differentiable one_ne_zero x)
      (differentiableAt_const _)]
  simp

end TestFunction
