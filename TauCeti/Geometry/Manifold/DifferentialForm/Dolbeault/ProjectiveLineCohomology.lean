/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Cohomology
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ProjectiveLine
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Geometry.Manifold.Complex
import TauCeti.Analysis.Complex.CauchyKernel
import TauCeti.Analysis.Complex.Pompeiu.Basic

/-!
# Dolbeault cohomology of the projective line

On the complex projective line `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)`, the operator `∂bar` on smooth functions
with values in a complex Banach space `F` has kernel the constants and cokernel zero: every smooth
`(0,1)`-form is `∂bar` of a smooth function. So `H^(0,0)_∂bar(ℂℙ¹; F) ≃ F` and
`H^(0,1)_∂bar(ℂℙ¹; F) = 0`, and for `F = ℂ` the index of `∂bar` is `2 - 0 = 2`, the Euler
characteristic of the sphere.

The kernel is the constants because a holomorphic function on a compact connected complex manifold
is constant. For the cokernel, read a `(0,1)`-form `α` in the affine coordinates `t ↦ [t : 1]` and
`s ↦ [1 : s]`, related by `s = 1 / t`. A smooth cutoff splits `α` into two forms whose coefficients
are compactly supported in the coordinate `t` and in the coordinate `s` respectively. For each
piece, with coefficient `c(t) d(conj t)` say, the Cauchy transform `u = T c` solves
`∂bar u = c d(conj t)` on `ℂ` (`HasCompactSupport.conjWirtingerDeriv_cauchyTransform`). Off the
support of `c` it is holomorphic, and it tends to `0` at infinity, so `s ↦ u (1 / s)` has a
removable singularity at `s = 0`. Hence `u` extends by `0` to a smooth function on `ℂℙ¹`. Its
`∂bar` agrees with the piece in the coordinate `t`, which covers a dense open set, hence
everywhere.

## Main declarations

* `TauCeti.SmoothForm.IsOfType.exists_delBar_eq_projectivization`: every smooth `(0,1)`-form on
  `ℂℙ¹` is `∂bar` of a smooth function.
* `TauCeti.SmoothForm.delBar_eq_zero_iff_exists_eq_const_projectivization`: the kernel of `∂bar`
  on smooth functions over `ℂℙ¹` is the constants.
* `TauCeti.dolbeaultCohomology.instSubsingletonProjectivizationZeroOne`: `H^(0,1)_∂bar(ℂℙ¹; F)`
  vanishes.
* `TauCeti.dolbeaultCohomology.zeroZeroEquivProjectivization`: `H^(0,0)_∂bar(ℂℙ¹; F) ≃ F`.
* `TauCeti.dolbeaultCohomology.finrank_zero_zero_sub_finrank_zero_one_projectivization`: the
  index of `∂bar` on complex functions over `ℂℙ¹` is `2`.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0,
  Sections 1 and 2 (the `∂bar`-Poincaré lemma in one variable).
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 1.3 and Section 2.6.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.2.2.
-/

public section

noncomputable section

open Set Filter Function Complex Projectivization Metric Bornology MeasureTheory
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold LinearAlgebra.Projectivization
  ComplexConjugate

namespace TauCeti

open SmoothAlmostComplexStructure ProjectiveLine

/-! ### The affine coordinates -/

namespace ProjectiveLine

private theorem affineParam_zero_notMem_affineOpen {i j : Fin 2} (hij : i ≠ j) :
    affineParam j 0 ∉ affineOpen (K := ℂ) i := by
  rw [affineParam_eq, mk_mem_affineOpen_iff, not_not]
  fin_cases i <;> fin_cases j <;> simp_all

private theorem eq_or_eq_of_ne {i j : Fin 2} (hij : i ≠ j) (k : Fin 2) : k = i ∨ k = j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

/-- A function on the projective line whose compositions with both affine coordinates are smooth
is smooth. -/
private theorem contMDiff_of_contDiff_comp_affineParam {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : ℙ ℂ (Fin 2 → ℂ) → G} (hf : ∀ i, ContDiff ℝ ∞ (f ∘ affineParam i)) :
    ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, G) ∞ f := by
  intro x
  obtain ⟨i, hi⟩ := exists_mem_affineOpen x
  have hchart : ContMDiffAt 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ) ∞
      (affineChart (K := ℂ) (n := 1) i) x := by
    simpa only [modelWithCornersSelf_restrictScalars] using
      ((contMDiffOn_affineChart (𝕜 := ℂ) (n := 1) i ∞).contMDiffAt
        ((isOpen_affineOpen i).mem_nhds hi)).restrictScalars ℝ
  have hG : ContDiff ℝ ∞ fun z : Fin 1 → ℂ ↦ (f ∘ affineParam i) (z 0) :=
    (hf i).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℂ) 0).contDiff
  refine (hG.contMDiff.contMDiffAt.comp x hchart).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_affineOpen i).mem_nhds hi] with y hy
  simp [affineParam_affineChart hy]

/-- Every derivative of an affine coordinate of the projective line is surjective. -/
private theorem surjective_mfderiv_affineParam (i : Fin 2) (t : ℂ) :
    Surjective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) (affineParam i) t) := by
  have h : Module.finrank ℝ ℂ = Module.finrank ℝ (Fin 1 → ℂ) := by
    simp [Module.finrank_pi_fintype]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h
    (f := (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) (affineParam i) t).toLinearMap)).1
    (injective_mfderiv_affineParam i t)

/-- A smooth form on the projective line is determined by its pullback along one affine
coordinate: that coordinate covers all points but one, and the forms are continuous. -/
private theorem mpullback_affineParam_injective {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {k : ℕ} (i : Fin 2) :
    Injective (SmoothForm.mpullback (F := F) (k := k) (affineParam i)
      (contMDiff_affineParam_real i)) := by
  -- First, two forms agreeing after pullback along both coordinates are equal.
  have hboth {α β : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F k}
      (h : ∀ i, SmoothForm.mpullback (affineParam i) (contMDiff_affineParam_real i) α =
        SmoothForm.mpullback (affineParam i) (contMDiff_affineParam_real i) β) : α = β := by
    refine Subtype.ext (funext fun x ↦ ?_)
    obtain ⟨i, hi⟩ := exists_mem_affineOpen x
    obtain ⟨t, rfl⟩ : ∃ t, affineParam i t = x := ⟨_, affineParam_affineChart hi⟩
    ext v
    choose w hw using fun m ↦ surjective_mfderiv_affineParam i t (v m)
    have h' := congrArg (fun γ : SmoothForm 𝓘(ℝ, ℂ) ℂ F k ↦ γ.1 t w) (h i)
    simp only [SmoothForm.mpullback_apply, hw] at h'
    exact h'
  -- Pullbacks along the other coordinate agree off `0`, hence everywhere by continuity.
  intro α β h
  obtain ⟨j, hij⟩ : ∃ j, i ≠ j := by fin_cases i <;> simp
  refine hboth fun l ↦ ?_
  rcases eq_or_eq_of_ne hij l with rfl | rfl
  · exact h
  let Θ (γ : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F k) : ℂ → ℂ [⋀^Fin k]→L[ℝ] F :=
    fun s ↦ (SmoothForm.mpullback (affineParam l) (contMDiff_affineParam_real l) γ).1 s
  have hcont (γ : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F k) : Continuous (Θ γ) :=
    (isSmoothForm_modelSpace_iff.1 (SmoothForm.mpullback _ _ γ).isSmoothForm).continuous
  have hΘ : Θ α = Θ β := (hcont α).ext_on (dense_compl_singleton 0) (hcont β) fun s hs ↦ by
    simp only [Θ]
    rw [coe_mpullback_affineParam_apply_of_ne_zero α hij.symm hs,
      coe_mpullback_affineParam_apply_of_ne_zero β hij.symm hs, h]
  exact Subtype.ext (funext fun s ↦ congrFun hΘ s)

end ProjectiveLine

/-! ### The Cauchy transform near infinity -/

section CauchyTransform

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {c : ℂ → F}

omit [CompleteSpace F] in
private theorem contDiff_cauchyTransform_of_hasCompactSupport (hc : HasCompactSupport c)
    (hs : ContDiff ℝ ∞ c) : ContDiff ℝ ∞ (cauchyTransform c) := by
  rw [cauchyTransform_eq_convolution]
  exact (hc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    Complex.locallyIntegrable_inv hs).const_smul _

private theorem differentiableAt_cauchyTransform_of_notMem_tsupport (hc : HasCompactSupport c)
    (hs : ContDiff ℝ 1 c) {w : ℂ} (hw : w ∉ tsupport c) :
    DifferentiableAt ℂ (cauchyTransform c) w := by
  have h := (differentiableOn_integral_sub_inv_smul_compl hc
    (fun x hx ↦ image_eq_zero_of_notMem_tsupport hx) hs).differentiableAt
    ((isClosed_tsupport c).isOpen_compl.mem_nhds hw)
  rw [show cauchyTransform c = fun x ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (x - z)⁻¹ • c z from
    funext (cauchyTransform_apply c)]
  exact h.const_smul _

omit [CompleteSpace F] in
/-- The Cauchy transform of a compactly supported continuous map tends to `0` at infinity. -/
private theorem tendsto_cauchyTransform_cobounded (hc : HasCompactSupport c) (hs : Continuous c) :
    Tendsto (cauchyTransform c) (cobounded ℂ) (𝓝 0) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set R' := max R 1
  set C := ∫ z, ‖c z‖
  have hint : Integrable fun z ↦ ‖c z‖ := hs.norm.integrable_of_hasCompactSupport hc.norm
  have hbound : ∀ᶠ w in cobounded ℂ,
      ‖cauchyTransform c w‖ ≤ (Real.pi⁻¹ * 2 * C) * ‖w‖⁻¹ := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop (2 * R'))]
      with w hw
    have hR'1 : 1 ≤ R' := le_max_right _ _
    have hw0 : 0 < ‖w‖ := by linarith
    have hpt : ∀ z, ‖(w - z)⁻¹ • c z‖ ≤ 2 * ‖w‖⁻¹ * ‖c z‖ := fun z ↦ by
      by_cases hz : c z = 0
      · simp [hz]
      have hzR : ‖z‖ ≤ R' := by
        have := hR (subset_tsupport c hz)
        rw [mem_closedBall, dist_zero_right] at this
        exact this.trans (le_max_left _ _)
      have hwz : ‖w‖ / 2 ≤ ‖w - z‖ := by
        have := norm_sub_norm_le w z
        linarith
      rw [norm_smul, norm_inv]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [inv_le_comm₀ (by linarith) (by positivity)]
      calc (2 * ‖w‖⁻¹)⁻¹ = ‖w‖ / 2 := by field_simp
        _ ≤ ‖w - z‖ := hwz
    calc ‖cauchyTransform c w‖ = Real.pi⁻¹ * ‖∫ z, (w - z)⁻¹ • c z‖ := by
          rw [cauchyTransform_apply, norm_smul, norm_inv, Complex.norm_real,
            Real.norm_of_nonneg Real.pi_pos.le]
      _ ≤ Real.pi⁻¹ * ∫ z, 2 * ‖w‖⁻¹ * ‖c z‖ := by
          gcongr
          exact norm_integral_le_of_norm_le (hint.const_mul _) (ae_of_all _ hpt)
      _ = (Real.pi⁻¹ * 2 * C) * ‖w‖⁻¹ := by
          rw [integral_const_mul]
          ring
  have hlim : Tendsto (fun w : ℂ ↦ (Real.pi⁻¹ * 2 * C) * ‖w‖⁻¹) (cobounded ℂ) (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_norm_cobounded_atTop).const_mul
      (Real.pi⁻¹ * 2 * C)
  exact squeeze_zero_norm' hbound hlim

omit [NormedSpace ℂ F] [CompleteSpace F] in
private theorem update_comp_inv_eventuallyEq {u : ℂ → F} {s : ℂ} (hs : s ≠ 0) :
    update (fun y ↦ u y⁻¹) 0 0 =ᶠ[𝓝 s] fun y ↦ u y⁻¹ := by
  filter_upwards [eventually_ne_nhds hs] with y hy using update_of_ne hy _ _

/-- **A removable singularity at infinity.** If a smooth map `u` is holomorphic near infinity and
tends to `0` there, then `s ↦ u (1 / s)`, extended by `0` at `s = 0`, is smooth. -/
private theorem contDiff_update_comp_inv {u : ℂ → F} (hu : ContDiff ℝ ∞ u) {R : ℝ}
    (hhol : ∀ w, R < ‖w‖ → DifferentiableAt ℂ u w) (hlim : Tendsto u (cobounded ℂ) (𝓝 0)) :
    ContDiff ℝ ∞ (update (fun s ↦ u s⁻¹) 0 0) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  rcases eq_or_ne s 0 with rfl | hs
  · set r := (max R 1)⁻¹
    have hr : 0 < r := inv_pos.2 (lt_max_of_lt_right one_pos)
    have hd : DifferentiableOn ℂ (update (fun s ↦ u s⁻¹) 0 0) (ball 0 r) := by
      rw [← differentiableOn_compl_singleton_and_continuousAt_iff (ball_mem_nhds 0 hr)]
      refine ⟨fun s hs ↦ ?_, continuousAt_update_same.2 (hlim.comp tendsto_inv₀_nhdsNE_zero)⟩
      have hs0 : s ≠ 0 := hs.2
      have hsr : ‖s‖ < r := by simpa using hs.1
      have hR : R < ‖s⁻¹‖ := by
        rw [norm_inv]
        exact (le_max_left R 1).trans_lt
          ((lt_inv_comm₀ (norm_pos_iff.2 hs0) (lt_max_of_lt_right one_pos)).1 hsr)
      exact (((hhol _ hR).comp s (differentiableAt_inv hs0)).congr_of_eventuallyEq
        (update_comp_inv_eventuallyEq hs0)).differentiableWithinAt
    exact ((hd.contDiffOn isOpen_ball).contDiffAt (ball_mem_nhds 0 hr)).restrict_scalars ℝ
  · exact (hu.contDiffAt.comp s ((contDiffAt_inv ℂ hs).restrict_scalars ℝ)).congr_of_eventuallyEq
      (update_comp_inv_eventuallyEq hs)

end CauchyTransform

/-! ### Solving `∂bar f = β` -/

namespace SmoothForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A one-form of type `(0,1)` on `ℂ` is conjugate-linear. -/
private theorem map_smul_conj_of_isOfType_zero_one {α : ℂ [⋀^Fin 1]→L[ℝ] F}
    (h : α.IsOfType (Complex.I • ContinuousLinearMap.id ℝ ℂ) 0 1) (c v : ℂ) :
    α ![c • v] = conj c • α ![v] := by
  have hI : α ![I • v] = -I • α ![v] :=
    (ContinuousAlternatingMap.isOfType_zero_one_iff α).1 h v
  have hU : c • v = c.re • v + c.im • I • v := by
    conv_lhs => rw [← re_add_im c]
    rw [add_smul, mul_smul, ← coe_algebraMap, algebraMap_smul, algebraMap_smul]
  have hF : conj c • α ![v] = c.re • α ![v] + c.im • -I • α ![v] := by
    conv_lhs => rw [← re_add_im c]
    simp only [map_add, map_mul, conj_ofReal, conj_I, add_smul, mul_smul, Complex.coe_smul,
      mul_neg, neg_smul, smul_neg]
  rw [hU, hF, ← hI, ← ContinuousAlternatingMap.vecCons_smul,
    ← ContinuousAlternatingMap.vecCons_smul, ← ContinuousAlternatingMap.vecCons_add]

variable [CompleteSpace F]

/-- **Solving `∂bar f = β` for a form supported in one affine chart.** Let `β` be a `(0,1)`-form on
the projective line whose coefficient `c(t)` in the affine coordinate `t` of the chart `i` is
compactly supported. Its Cauchy transform `u` solves `∂bar u = c d(conj t)` on `ℂ`, is
holomorphic off the support of `c` and tends to `0` at infinity, so in the other coordinate
`s = 1 / t` it has a removable singularity at `s = 0`. Hence `u`, read in the chart `i` and
extended by `0` at the remaining point, is a smooth function with `∂bar f = β`. -/
private theorem exists_delBar_eq_of_hasCompactSupport
    {β : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F 1}
    (hβ : β.IsOfType (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))) 0 1) (i : Fin 2)
    (hc : HasCompactSupport fun t ↦
      (SmoothForm.mpullback (affineParam i) (contMDiff_affineParam_real i) β).1 t ![(1 : ℂ)]) :
    ∃ f : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F 0,
      (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))).delBar f = β := by
  obtain ⟨j, hij⟩ : ∃ j, i ≠ j := by fin_cases i <;> simp
  set η := SmoothForm.mpullback (affineParam i) (contMDiff_affineParam_real i) β
  set c : ℂ → F := fun t ↦ η.1 t ![(1 : ℂ)]
  have hcs : ContDiff ℝ ∞ c := by
    let Θ : ℂ → ℂ [⋀^Fin 1]→L[ℝ] F := fun y ↦ η.1 y
    have hd : ContDiff ℝ ∞ Θ := isSmoothForm_modelSpace_iff.1 η.isSmoothForm
    exact (ContinuousAlternatingMap.apply ℝ ℂ F ![(1 : ℂ)]).contDiff.comp hd
  set u := cauchyTransform c
  have hu : ContDiff ℝ ∞ u := contDiff_cauchyTransform_of_hasCompactSupport hc hcs
  -- `g` is `u` read in the chart `i`, extended by `0` at the remaining point.
  set g : ℙ ℂ (Fin 2 → ℂ) → F :=
    (affineOpen (K := ℂ) i).indicator fun x ↦ u (affineChart (K := ℂ) (n := 1) i x 0)
  have hgi : g ∘ affineParam i = u := funext fun t ↦ by
    simp [g, indicator_of_mem (affineParam_mem_affineOpen i t), affineChart_affineParam]
  have hgj : g ∘ affineParam j = update (fun s ↦ u s⁻¹) 0 0 := funext fun s ↦ by
    rcases eq_or_ne s 0 with rfl | hs
    · simp [g, indicator_of_notMem (affineParam_zero_notMem_affineOpen hij)]
    · rw [comp_apply, affineParam_inv hij.symm hs, update_of_ne hs]
      simp [g, indicator_of_mem (affineParam_mem_affineOpen i _), affineChart_affineParam]
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hhol (w : ℂ) (hw : R < ‖w‖) : DifferentiableAt ℂ u w := by
    refine differentiableAt_cauchyTransform_of_notMem_tsupport hc (hcs.of_le (by simp))
      fun h ↦ ?_
    have := hR h
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have hg : ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, F) ∞ g :=
    contMDiff_of_contDiff_comp_affineParam fun l ↦ by
      rcases eq_or_eq_of_ne hij l with rfl | rfl
      · rw [hgi]
        exact hu
      · rw [hgj]
        exact contDiff_update_comp_inv hu hhol
          (tendsto_cauchyTransform_cobounded hc hcs.continuous)
  set f : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F 0 :=
    ⟨RoughForm.ofFunction _ g, (isSmoothForm_ofFunction_iff.2 hg).mem_smoothBundleForms⟩
  refine ⟨f, mpullback_affineParam_injective i ?_⟩
  rw [mpullback_delBar _ _ (isPseudoholomorphic_affineParam i)]
  -- In the coordinate `t`, both sides are conjugate-linear with coefficient `c(t) = ∂bar u(t)`.
  have hfun : (fun y ↦ (SmoothForm.mpullback (affineParam i) (contMDiff_affineParam_real i) f).1
      y 0) = u := by
    rw [← hgi]
    funext y
    rw [SmoothForm.mpullback_apply]
    exact RoughForm.ofFunction_apply _ _ _
  refine Subtype.ext (funext fun t ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
  obtain ⟨w, rfl⟩ : ∃ w : ℂ, v = ![w] := ⟨v 0, by ext k; fin_cases k; rfl⟩
  have hη : (η.1 t : ℂ [⋀^Fin 1]→L[ℝ] F).IsOfType (Complex.I • ContinuousLinearMap.id ℝ ℂ) 0 1 := by
    simpa only [toEndomorphism_ofComplexManifold] using
      (hβ.mpullback _ (isPseudoholomorphic_affineParam i)).apply t
  have hη' := map_smul_conj_of_isOfType_zero_one hη w 1
  rw [smul_eq_mul, mul_one] at hη'
  have hW : conjWirtingerDeriv u t w = conj w • conjWirtingerDeriv u t 1 := by
    rw [← (conjWirtingerDeriv u t).map_smulₛₗ, smul_eq_mul, mul_one]
  have hL : ((ofComplexManifold ℂ ℂ).delBar
      (SmoothForm.mpullback (affineParam i) (contMDiff_affineParam_real i) f)).1 t ![w] =
        conj w • c t := by
    refine (delBar_apply_apply _ _ t w).trans ?_
    rw [hfun]
    simp only [ofComplexManifold_apply]
    have e (v : ℂ) : mvfderiv 𝓘(ℝ, ℂ) u t v = fderiv ℝ u t v := mvfderiv_eq_fderiv_apply u t v
    rw [e, e]
    refine (conjWirtingerDeriv_apply u t w).symm.trans ?_
    rw [hW, hc.conjWirtingerDeriv_cauchyTransform (hcs.of_le (by simp))]
  exact hL.trans hη'.symm

/-- A smooth cutoff on the projective line, `1` near `[0 : 1]` and `0` near `[1 : 0]`: in the
coordinate `t` of the chart `1` it is compactly supported, and `1` minus it is compactly supported
in the coordinate `s` of the chart `0`. -/
private theorem exists_cutoff_projectivization :
    ∃ ρ : C^∞⟮𝓘(ℝ, Fin 1 → ℂ), ℙ ℂ (Fin 2 → ℂ); ℝ⟯,
      HasCompactSupport (fun t ↦ ρ (affineParam 1 t)) ∧
        HasCompactSupport (fun s ↦ 1 - ρ (affineParam 0 s)) := by
  let χ : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  let ρ : ℙ ℂ (Fin 2 → ℂ) → ℝ :=
    (affineOpen (K := ℂ) 1).indicator fun x ↦ χ (affineChart (K := ℂ) (n := 1) 1 x 0)
  have h1 : ρ ∘ affineParam 1 = χ := funext fun t ↦ by
    simp [ρ, indicator_of_mem (affineParam_mem_affineOpen 1 t), affineChart_affineParam]
  have h0 (s : ℂ) (hs : s ≠ 0) : ρ (affineParam 0 s) = χ s⁻¹ := by
    rw [affineParam_inv (by decide : (0 : Fin 2) ≠ 1) hs]
    simp [ρ, indicator_of_mem (affineParam_mem_affineOpen 1 _), affineChart_affineParam]
  have h00 : ρ (affineParam 0 0) = 0 :=
    indicator_of_notMem (affineParam_zero_notMem_affineOpen (by decide : (1 : Fin 2) ≠ 0)) _
  have hρ : ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, ℝ) ∞ ρ :=
    contMDiff_of_contDiff_comp_affineParam fun l ↦ by
      rcases eq_or_eq_of_ne (by decide : (0 : Fin 2) ≠ 1) l with rfl | rfl
      · rw [contDiff_iff_contDiffAt]
        intro s
        rcases eq_or_ne s 0 with rfl | hs
        · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
          filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 2⁻¹)] with y hy
          rcases eq_or_ne y 0 with rfl | hy0
          · exact h00
          · rw [comp_apply, h0 y hy0]
            refine χ.zero_of_le_dist ?_
            rw [mem_ball, dist_zero_right] at hy
            rw [dist_zero_right, norm_inv]
            exact (le_inv_comm₀ (norm_pos_iff.2 hy0) (by norm_num : (0 : ℝ) < 2)).1 hy.le
        · refine (χ.contDiff.contDiffAt.comp s
            ((contDiffAt_inv ℂ hs).restrict_scalars ℝ)).congr_of_eventuallyEq ?_
          filter_upwards [eventually_ne_nhds hs] with y hy using h0 y hy
      · simpa [h1] using (χ.contDiff (n := (⊤ : ℕ∞)))
  refine ⟨⟨ρ, hρ⟩, ?_, HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 1) fun s hs ↦ ?_⟩
  · simpa [Function.comp_def] using congrArg HasCompactSupport h1 ▸ χ.hasCompactSupport
  · rw [mem_closedBall, dist_zero_right, not_le] at hs
    have hs0 : s ≠ 0 := norm_pos_iff.1 (one_pos.trans hs)
    change 1 - ρ (affineParam 0 s) = 0
    rw [h0 s hs0, χ.one_of_mem_closedBall, sub_self]
    rw [mem_closedBall, dist_zero_right, norm_inv]
    exact inv_le_one_of_one_le₀ hs.le

/-- **Every `(0,1)`-form on the projective line is `∂bar` of a smooth function.** For a smooth
`(0,1)`-form `α` on `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)` with coefficients in a complex Banach space, there is
a smooth function `f` with `∂bar f = α`. -/
theorem IsOfType.exists_delBar_eq_projectivization
    {α : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F 1}
    (hα : α.IsOfType (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))) 0 1) :
    ∃ f : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F 0,
      (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))).delBar f = α := by
  obtain ⟨ρ, h1, h0⟩ := exists_cutoff_projectivization
  -- Split `α = ρ α + (1 - ρ) α` into pieces supported in the two affine charts.
  have htype (g : C^∞⟮𝓘(ℝ, Fin 1 → ℂ), ℙ ℂ (Fin 2 → ℂ); ℝ⟯) :
      (funSMulₗ g α).IsOfType (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))) 0 1 :=
    isOfType_iff_forall.2 ⟨rfl, fun x ↦ by
      simpa only [coe_funSMulₗ, Complex.coe_smul] using (hα.apply x).smul (g x : ℂ)⟩
  have hcoeff (g : C^∞⟮𝓘(ℝ, Fin 1 → ℂ), ℙ ℂ (Fin 2 → ℂ); ℝ⟯) (l : Fin 2) :
      (fun t ↦ (SmoothForm.mpullback (affineParam l) (contMDiff_affineParam_real l)
        (funSMulₗ g α)).1 t ![(1 : ℂ)]) = fun t ↦ g (affineParam l t) •
          (SmoothForm.mpullback (affineParam l) (contMDiff_affineParam_real l) α).1 t
            ![(1 : ℂ)] := by
    funext t
    simp only [SmoothForm.mpullback_apply, coe_funSMulₗ]
    rfl
  obtain ⟨f₁, hf₁⟩ := exists_delBar_eq_of_hasCompactSupport (htype ρ) 1
    (by rw [hcoeff]; exact h1.smul_right)
  obtain ⟨f₀, hf₀⟩ := exists_delBar_eq_of_hasCompactSupport (htype (1 - ρ)) 0
    (by rw [hcoeff]; exact h0.smul_right)
  refine ⟨f₁ + f₀, ?_⟩
  rw [map_add, hf₁, hf₀]
  refine Subtype.ext (funext fun x ↦ ?_)
  simp [← add_smul]

end SmoothForm

/-! ### Dolbeault cohomology -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace SmoothForm

/-- **The kernel of `∂bar` on functions over the projective line is the constants.** A smooth
function `f` on `ℂℙ¹` satisfies `∂bar f = 0` exactly when it is constant: it is then holomorphic on
a compact connected complex manifold. -/
theorem delBar_eq_zero_iff_exists_eq_const_projectivization
    (f : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F 0) :
    (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))).delBar f = 0 ↔
      ∃ c : F, ∀ x, f.1 x 0 = c := by
  rw [delBar_ofComplexManifold_eq_zero_iff]
  refine ⟨fun h ↦ ?_, fun ⟨c, hc⟩ ↦ ?_⟩
  · obtain ⟨c, hc⟩ := MDifferentiable.exists_eq_const_of_compactSpace h
    exact ⟨c, fun x ↦ congrFun hc x⟩
  · rw [show (fun y ↦ f.1 y 0) = fun _ ↦ c from funext hc]
    exact mdifferentiable_const

end SmoothForm

namespace dolbeaultCohomology

open Dolbeault

variable [CompleteSpace F]

/-- **`H^(0,1)` of the projective line vanishes.** Every `(0,1)`-form on `ℂℙ¹` is `∂bar` of a
smooth function. -/
instance instSubsingletonProjectivizationZeroOne :
    Subsingleton (dolbeaultCohomology (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F 0 1) := by
  refine subsingleton_of_forall_eq 0 fun a ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective 0 1 a
  rw [mk_eq_zero_iff, mem_exactForms_succ]
  obtain ⟨f, hf⟩ := ((((ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))).mem_typeForms 0 1
    φ.1.1).1 φ.1.2)).exists_delBar_eq_projectivization
  exact ⟨⟨f, ((ofComplexManifold _ _).mem_typeForms 0 0 f).2
    (SmoothForm.isOfType_zero_zero f _)⟩, hf⟩

/-- **`H^(0,0)` of the projective line is the space of constants.** The holomorphic functions on
`ℂℙ¹` are constant, so evaluation identifies `H^(0,0)_∂bar(ℂℙ¹; F)` with `F`. -/
def zeroZeroEquivProjectivization :
    dolbeaultCohomology (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F 0 0 ≃ₗ[ℂ] F :=
  zeroZeroEquiv (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F ≪≫ₗ
    { toFun g := g (affineParam 0 0)
      invFun c := ⟨fun _ ↦ c, contMDiff_const⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv g := ContMDiffMap.ext fun x ↦
        (MDifferentiable.apply_eq_of_compactSpace (g.contMDiff.mdifferentiable (by simp)) _ _)
      right_inv _ := rfl }

/-- **The index of `∂bar` on functions over the projective line.** Its kernel `H^(0,0)` is the
constants, of real dimension `2`, and its cokernel `H^(0,1)` vanishes, so the index is
`2 - 0 = 2`, the Euler characteristic of the sphere. -/
theorem finrank_zero_zero_sub_finrank_zero_one_projectivization :
    (Module.finrank ℝ (dolbeaultCohomology (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) ℂ 0 0) : ℤ) -
      Module.finrank ℝ (dolbeaultCohomology (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) ℂ 0 1) = 2 := by
  rw [finrank_real_of_complex, finrank_real_of_complex,
    (zeroZeroEquivProjectivization (F := ℂ)).finrank_eq,
    Module.finrank_zero_of_subsingleton
      (M := dolbeaultCohomology (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) ℂ 0 1)]
  simp

end dolbeaultCohomology

end TauCeti
