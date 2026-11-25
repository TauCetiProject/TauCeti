/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.DdbarForm.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.DC
import TauCeti.Analysis.Calculus.DifferentialForm.Gradient

/-!
# `i∂∂bar u` from the Levi form agrees with `(1/2) d dᶜ u`

On a complex manifold `M` modelled on `𝓘(ℂ, E)` there are two descriptions of the real
(1,1)-form `i∂∂bar u` of a smooth real function `u`.

* `TauCeti.ddbarForm E u` defines it pointwise from the Levi form: its Hermitian form at `x` is
  `2·L_u(x)`, and `(i∂∂bar u)(v, w) = 2·Im L_u(x)(v, w)`.
* The Dolbeault calculus on complex-valued smooth forms defines `dᶜ = i(∂bar - ∂)`, so that
  `d dᶜ = 2i ∂∂bar` (`TauCeti.SmoothAlmostComplexStructure.mextDerivₗ_dC_ofComplexManifold`), and
  `i∂∂bar u = (1/2) d dᶜ u` for `u` read as a complex-valued `0`-form.

This file proves that the two agree, by comparing their coefficients in the holomorphic chart at
each point. On a function, `dᶜ f = -df ∘ J` for every almost complex structure `J`
(`TauCeti.SmoothAlmostComplexStructure.dC_apply_apply`). In a holomorphic chart, where `J` is
multiplication by `i`, the coordinate expression of `d dᶜ u` is therefore
`(v, w) ↦ D²u(w, i v) - D²u(v, i w)`, while that of `i∂∂bar u` is twice the alternation of the
imaginary part `(D²u(i v, w) - D²u(v, i w)) / 4` of the Levi form; the two agree by the symmetry of
the second derivative.

## Main results

* `TauCeti.ddbarForm_apply_eq_inv_two_smul_mextDerivₗ_dC_apply`: `i∂∂bar u = (1/2) d dᶜ u`,
  evaluated on a pair of tangent vectors.
* `TauCeti.ddbarForm_apply_eq_I_smul_del_delBar_apply`: `i∂∂bar u = i ∂∂bar u`, the latter
  computed with the Dolbeault operators, evaluated on a pair of tangent vectors.
-/

public section

noncomputable section

open Complex Filter Set Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

open SmoothAlmostComplexStructure

/-- In the preferred chart at `x`, the coordinate expression of `dᶜ f` is `w ↦ -dg(i w)`, where `g`
is the coordinate expression of the function `f`. -/
private theorem inChartAt_dC_apply (f : SmoothForm 𝓘(ℝ, E) M ℂ 0) (x : M) {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E) x).target) (w : E) :
    RoughForm.inChartAt ((ofComplexManifold E M).dC f).val x z ![w] =
      -fderiv ℝ (fun z ↦ f.val ((extChartAt 𝓘(ℝ, E) x).symm z) 0) z (Complex.I • w) := by
  set e := extChartAt 𝓘(ℝ, E) x
  set D := mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (range 𝓘(ℝ, E)) z
  have hvec : (fun i : Fin 1 ↦ D (![w] i)) = ![D w] := funext (Fin.forall_fin_one.2 (by simp))
  rw [RoughForm.inChartAt_apply, hvec, dC_apply_apply,
    ofComplexManifold_apply_mfderivWithin_extChartAt_symm hz]
  congr 1
  -- The chain rule for the function composed with the inverse chart.
  have hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) (fun y ↦ f.val y 0) (e.symm z) :=
    (SmoothForm.contMDiff_apply_zero f).mdifferentiableAt (by simp)
  have he : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (range 𝓘(ℝ, E)) z :=
    mdifferentiableWithinAt_extChartAt_symm hz
  have hchain := mvfderiv_comp_mfderivWithin z hf he
    (uniqueMDiffWithinAt_univ 𝓘(ℝ, E) |>.mono (by simp))
  refine (congr($hchain (Complex.I • w))).symm.trans ?_
  simp only [modelWithCornersSelf_coe, range_id, mvfderivWithin_univ]
  exact mvfderiv_eq_fderiv_apply _ z _

/-- The real-linear map `A ↦ (w ↦ A (i • w))` from real covectors to complex-valued ones, through
which the coordinate expression of `dᶜ u` is read off from that of `du`. -/
private def ofRealCompI : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℂ) :=
  (ContinuousLinearMap.compL ℝ E E ℂ).flip (Complex.I • ContinuousLinearMap.id ℝ E) ∘L
    ContinuousLinearMap.compL ℝ E ℝ ℂ ofRealCLM

@[simp]
private theorem ofRealCompI_apply_apply (A : E →L[ℝ] ℝ) (w : E) :
    ofRealCompI A w = (A (Complex.I • w) : ℂ) := by
  simp [ofRealCompI]

/-- A real function which, read in `ℂ`, is a smooth `0`-form, is smooth. -/
private theorem contMDiff_of_apply_zero_eq {u : M → ℝ} (f : SmoothForm 𝓘(ℝ, E) M ℂ 0)
    (hf : ∀ y, f.val y 0 = u y) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ u := by
  have hre : u = fun y ↦ (f.val y 0).re := funext fun y ↦ by rw [hf, ofReal_re]
  rw [hre]
  exact reCLM.contDiff.comp_contMDiff (SmoothForm.contMDiff_apply_zero f)

/-- The coordinate expression in the preferred chart at `x` of a real function which, read in `ℂ`,
is a smooth `0`-form, is `C²` at the centre of the chart. -/
private theorem contDiffAt_two_comp_chartAt_symm {u : M → ℝ} (f : SmoothForm 𝓘(ℝ, E) M ℂ 0)
    (hf : ∀ y, f.val y 0 = u y) (x : M) :
    ContDiffAt ℝ 2 (u ∘ (chartAt E x).symm) (extChartAt 𝓘(ℝ, E) x x) :=
  (((contMDiff_of_apply_zero_eq f hf).contMDiffAt (x := x)).of_le
    (by simp : (2 : WithTop ℕ∞) ≤ ∞)).contDiffAt_comp_chartAt_symm

/-- Near the centre of the preferred chart at `x`, the coordinate expression of `dᶜ f` is the
one-form `w ↦ -dh(i w)`, where `h` is the coordinate expression of the real function `u`. -/
private theorem inChartAt_dC_eventuallyEq {u : M → ℝ} (f : SmoothForm 𝓘(ℝ, E) M ℂ 0)
    (hf : ∀ y, f.val y 0 = u y) (x : M) :
    RoughForm.inChartAt ((ofComplexManifold E M).dC f).val x =ᶠ[𝓝 (extChartAt 𝓘(ℝ, E) x x)]
      fun z ↦ ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
        (-ofRealCompI (fderiv ℝ (u ∘ (chartAt E x).symm) z)) := by
  set e := extChartAt 𝓘(ℝ, E) x
  set h : E → ℝ := u ∘ (chartAt E x).symm
  have hgh : (fun z ↦ f.val (e.symm z) 0) = ofRealCLM ∘ h :=
    funext fun z ↦ by rw [hf]; simp [e, h]
  have htarget : e.target ∈ 𝓝 (e x) := by
    simpa [e] using (chartAt E x).open_target.mem_nhds (mem_chart_target E x)
  have hh1 : ∀ᶠ z in 𝓝 (e x), DifferentiableAt ℝ h z :=
    ((contDiffAt_two_comp_chartAt_symm f hf x).eventually (by simp)).mono
      fun z hz ↦ hz.differentiableAt (by simp)
  filter_upwards [htarget, hh1] with z hz hz'
  ext a
  have ha : a = ![a 0] := funext (Fin.forall_fin_one.2 (by simp))
  rw [ha, inChartAt_dC_apply f x hz, ContinuousAlternatingMap.ofSubsingletonLIE_apply,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, hgh,
    (ofRealCLM.hasFDerivAt.comp z hz'.hasFDerivAt).fderiv]
  simp

/-- **`i∂∂bar u = (1/2) d dᶜ u`.** Let `u` be a real function on a complex manifold which, read as
a complex-valued function, is the smooth `0`-form `f`. Then the real (1,1)-form
`TauCeti.ddbarForm E u`, defined from the Levi form, is half the exterior derivative of `dᶜ f`,
with the normalization `dᶜ = i(∂bar - ∂)`. -/
theorem ddbarForm_apply_eq_inv_two_smul_mextDerivₗ_dC_apply {u : M → ℝ}
    (f : SmoothForm 𝓘(ℝ, E) M ℂ 0) (hf : ∀ y, f.val y 0 = u y) (x : M) (v w : E) :
    (ddbarForm E u x ![v, w] : ℂ) =
      (2 : ℂ)⁻¹ • (mextDerivₗ 𝓘(ℝ, E) 1 ((ofComplexManifold E M).dC f)).val x ![v, w] := by
  set h : E → ℝ := u ∘ (chartAt E x).symm
  set z₀ := extChartAt 𝓘(ℝ, E) x x
  have hhC : ContDiffAt ℝ 2 h z₀ := contDiffAt_two_comp_chartAt_symm f hf x
  have hDh : DifferentiableAt ℝ (fderiv ℝ h) z₀ :=
    (hhC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  set L : E → E →L[ℝ] ℂ := fun z ↦ -ofRealCompI (fderiv ℝ h z)
  have hLd : HasFDerivAt L (-(ofRealCompI ∘L fderiv ℝ (fderiv ℝ h) z₀)) z₀ :=
    (ofRealCompI.hasFDerivAt.comp z₀ hDh.hasFDerivAt).neg
  have hfL (a b : E) : fderiv ℝ L z₀ a b =
      -(fderiv ℝ (fderiv ℝ h) z₀ a (Complex.I • b) : ℂ) := by
    rw [hLd.fderiv]
    simp
  -- Read `d dᶜ f` in the chart at `x`, where `dᶜ f` is the covector field `L`.
  have key := extDeriv_ofSubsingletonLIE_apply_pair hLd.differentiableAt v w
  rw [hfL, hfL] at key
  rw [mextDerivₗ_apply, mextDeriv_eq_extDeriv_inChartAt,
    (inChartAt_dC_eventuallyEq f hf x).extDeriv_eq]
  refine Eq.trans ?_ (congrArg ((2 : ℂ)⁻¹ • ·) key.symm)
  -- Read `i∂∂bar u` through the Levi form, and use the symmetry of the second derivative.
  have hsymm := hhC.isSymmSndFDerivAt (by simp)
  have hz₀ : chartAt E x x = z₀ := by simp [z₀]
  rw [ddbarForm_apply_vecCons, manifoldLeviForm_def, hz₀, im_leviForm_apply, im_leviForm_apply,
    hsymm (Complex.I • v) w, hsymm (Complex.I • w) v]
  push_cast
  ring

/-- **`i∂∂bar u` is `i ∂∂bar` of the Dolbeault calculus.** Let `u` be a real function on a complex
manifold which, read as a complex-valued function, is the smooth `0`-form `f`. Then the real
(1,1)-form `TauCeti.ddbarForm E u`, defined from the Levi form, is `i ∂ ∂bar f`. -/
theorem ddbarForm_apply_eq_I_smul_del_delBar_apply {u : M → ℝ}
    (f : SmoothForm 𝓘(ℝ, E) M ℂ 0) (hf : ∀ y, f.val y 0 = u y) (x : M) (v w : E) :
    (ddbarForm E u x ![v, w] : ℂ) =
      Complex.I • ((ofComplexManifold E M).del ((ofComplexManifold E M).delBar f)).val x
        ![v, w] := by
  rw [ddbarForm_apply_eq_inv_two_smul_mextDerivₗ_dC_apply f hf, mextDerivₗ_dC_ofComplexManifold]
  rw [SmoothForm.smul_toRoughForm, Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_smul]
  congr 1
  field_simp

end TauCeti
