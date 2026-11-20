/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.SmoothMultiplication
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Chart
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Transfer
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
import TauCeti.LinearAlgebra.Basis.Basic

/-!
# Smooth real Cauchy–Riemann operators on Sobolev sections

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`.
A smooth real Cauchy–Riemann operator `D` on `V` extends to a bounded operator

`W^{1,p}(Σ, V) → L^p(Σ, Λ^{0,1} ⊗ V)`

from the Sobolev space `TauCeti.SobolevSection A μ p 1` of sections to the Sobolev space
`TauCeti.zeroOneSobolevSections A μ p 0` of `(0,1)`-forms, for every `1 ≤ p ≤ ∞`
(`TauCeti.IsRealCauchyRiemannOperator.sobolevL`). This is McDuff–Salamon's realization of a real
Cauchy–Riemann operator at `k = 1`, for a smooth operator on a closed surface.

In chart `i`, a smooth section `s` with reading `sᵢ` is sent to `∂bar sᵢ + Zᵢ sᵢ`, where `∂bar` is
the complex antilinear part of the derivative and `Zᵢ` is the zeroth-order term of chart `i`
(`TauCeti.FiniteBundleAtlas.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder`).
The realization applies the same formula to the chart data `uᵢ` of a Sobolev section, with the weak
derivative of `uᵢ` in place of the derivative
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevL_ae`).
The zeroth-order term is smooth on a neighbourhood of the compact closure of the chart image, so
multiplication by it is bounded, and the components of the result in each chart are built from the
components of the section with `TauCeti.Wkp.contDiffOnSMulL`.

These chart data are the components of a one-form: on the overlap of two charts, the weak
derivative of `uᵢ'` is computed from that of `uᵢ` by the weak chain rule under the chart transition
and the weak Leibniz rule for the coordinate change `g` of `V`
(`TauCeti.HasWeakFDerivOn.contDiffOn_clm_apply_of_ne_zero`). The term `∂bar g` this produces is
exactly the one by which the zeroth-order terms of the two charts differ
(`TauCeti.FiniteBundleAtlas.complexAntilinearPartL_fderiv_coordChangeL_add_chartZeroOrder`). The
one-form is a `(0,1)`-form because both summands are complex antilinear in every chart. On smooth
sections the realization agrees with `D`
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevL_ofContMDiffSection_ae`).

## Main definitions

* `TauCeti.IsRealCauchyRiemannOperator.sobolevL`: the bounded realization of a smooth real
  Cauchy–Riemann operator from `W^{1,p}` sections to `L^p` `(0,1)`-forms.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevL_ae`: in chart `i` the realization is
  `∂bar uᵢ + Zᵢ uᵢ`, for the weak derivative of the chart data `uᵢ`.
* `TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevL_ofContMDiffSection_ae`: on `C¹`
  sections the realization is `D`.
* `TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevL_sub_ae`: the realizations of two
  smooth real Cauchy–Riemann operators differ by the zeroth-order term `(Zᵢ' - Zᵢ) uᵢ`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1 and C.2.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL complexAntilinearPartL_apply_I_smul)
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

universe u

namespace TauCeti


/-! ### The realization -/


section Realization

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealSobolevCauchyRiemann : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  (μ : Measure ℂ) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)]

namespace IsRealCauchyRiemannOperator

include hD hDs in
/-- The matrix entries of the zeroth-order term of chart `i` are smooth near the closure of the
chart image. -/
private theorem contDiffOn_coeff (i : Fin A.n) (c : Fin (finrank ℝ (ℂ →L[ℝ] F)))
    (j : Fin (finrank ℝ F)) :
    ContDiffOn ℝ ∞ (fun y ↦ (finBasis ℝ (ℂ →L[ℝ] F)).coord c
      (A.chartZeroOrder D i y (finBasis ℝ F j)))
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.triv i).baseSet) := by
  have h := A.contDiffOn_chartZeroOrder hD hDs isOpen_univ i
  rw [inter_univ] at h
  exact ((LinearMap.toContinuousLinearMap ((finBasis ℝ (ℂ →L[ℝ] F)).coord c)).comp
    (ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] F) (finBasis ℝ F j))).contDiff.comp_contDiffOn h

include hD hDs in
/-- Multiplication of the `j`th chart-`i` component by the `(c, j)` entry of the zeroth-order term,
as an `Lᵖ` function on the image of chart `i`. -/
private def zeroOrderL (i : Fin A.n) (c : Fin (finrank ℝ (ℂ →L[ℝ] F))) (j : Fin (finrank ℝ F)) :
    A.sectionChartData.SobolevData μ p 1 →L[ℝ] Lp ℝ p (μ.restrict (A.sectionChartData.image i)) :=
  (Wkp.contDiffOnSMulL (Omega := A.sectionChartData.image i)
    ((A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet).uniqueDiffOn
    (A.isCompact_closure_image i)
    ((A.closure_image_subset_chart_image_closure_dom i).trans
      (A.chart_image_closure_dom_subset i)) 0 (contDiffOn_coeff A hD hDs i c j)).comp
    ((Wkp.lowerOrderL 0).comp ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (finrank ℝ F) ↦ Wkp μ (A.sectionChartData.image i) p 1) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun i : Fin A.sectionChartData.n ↦
        ∀ _ : Fin (finrank ℝ F), Wkp μ (A.sectionChartData.image i) p 1) i)))

include hD hDs in
/-- The `c`th component in chart `i` of the realization, on the image of chart `i`: the `c`th
component of `∂bar uᵢ`, plus the matrix of the zeroth-order term applied to the components of
`uᵢ`. -/
private def chartL (i : Fin A.n) (c : Fin (finrank ℝ (ℂ →L[ℝ] F))) :
    A.sectionChartData.SobolevData μ p 1 →L[ℝ] Lp ℝ p (μ.restrict (A.sectionChartData.image i)) :=
  (((LinearMap.toContinuousLinearMap ((finBasis ℝ (ℂ →L[ℝ] F)).coord c)).comp
      complexAntilinearPartL).compLpL p _).comp (A.sectionChartData.chartDerivL μ p i) +
    ∑ j, zeroOrderL A hD hDs μ p i c j

include hD hDs in
/-- The components of the realization, before restricting to Sobolev sections. -/
private def dataL :
    A.sectionChartData.SobolevData μ p 1 →L[ℝ] A.tangentHom.sectionChartData.SobolevData μ p 0 :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.pi fun c ↦
    (Wkp.restrictL (sectionChartData_image_tangentHom A i).le 0).comp (chartL A hD hDs μ p i c)

/-- The `c`th component in chart `i` of the realization is, almost everywhere on the image of the
chart, the `c`th coordinate of `∂bar uᵢ` plus the matrix of the zeroth-order term applied to the
components of `uᵢ`. -/
private theorem chartL_ae (i : Fin A.n) (c : Fin (finrank ℝ (ℂ →L[ℝ] F)))
    (w : A.sectionChartData.SobolevData μ p 1) :
    (chartL A hD hDs μ p i c w : ℂ → ℝ) =ᵐ[μ.restrict (A.image i)] fun y ↦
      (finBasis ℝ (ℂ →L[ℝ] F)).coord c
          (complexAntilinearPartL (A.sectionChartData.chartDerivL μ p i w y)) +
        ∑ j, (finBasis ℝ (ℂ →L[ℝ] F)).coord c (A.chartZeroOrder D i y (finBasis ℝ F j)) *
          Wkp.value 1 (w i j) y := by
  have hz (j : Fin (finrank ℝ F)) : (zeroOrderL A hD hDs μ p i c j w : ℂ → ℝ)
      =ᵐ[μ.restrict (A.sectionChartData.image i)] fun y ↦ (finBasis ℝ (ℂ →L[ℝ] F)).coord c
        (A.chartZeroOrder D i y (finBasis ℝ F j)) * Wkp.lowerOrderL 0 (w i j) y := by
    have h := Wkp.value_contDiffOnSMulL_ae (mu := μ) (p := p) (Omega := A.sectionChartData.image i)
        ((A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet).uniqueDiffOn
        (A.isCompact_closure_image i)
        ((A.closure_image_subset_chart_image_closure_dom i).trans
          (A.chart_image_closure_dom_subset i)) 0 (contDiffOn_coeff A hD hDs i c j)
        (Wkp.lowerOrderL 0 (w i j))
    rw [Wkp.value_zero, Wkp.value_zero] at h
    exact h
  filter_upwards [Lp.coeFn_add (((((LinearMap.toContinuousLinearMap
      ((finBasis ℝ (ℂ →L[ℝ] F)).coord c)).comp complexAntilinearPartL).compLpL p _).comp
        (A.sectionChartData.chartDerivL μ p i)) w) ((∑ j, zeroOrderL A hD hDs μ p i c j) w),
    ContinuousLinearMap.coeFn_compLpL (p := p) (μ := μ.restrict (A.sectionChartData.image i))
      ((LinearMap.toContinuousLinearMap ((finBasis ℝ (ℂ →L[ℝ] F)).coord c)).comp
        complexAntilinearPartL) (A.sectionChartData.chartDerivL μ p i w),
    Lp.coeFn_finsetSum (μ := μ.restrict (A.sectionChartData.image i)) (p := p) Finset.univ
      fun j ↦ zeroOrderL A hD hDs μ p i c j w,
    ae_all_iff.2 hz] with y h₁ h₂ h₃ h₄
  rw [chartL, add_apply, h₁, Pi.add_apply, ContinuousLinearMap.comp_apply, h₂, sum_apply, h₃,
    Finset.sum_apply]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [Wkp.value_succ, Wkp.value_zero, ← Wkp.lowerOrderL_apply]
  exact h₄ j

/-- **The chart formula of the realization.** In chart `i`, the chart data of the realization of
an order-one tuple `w` are `∂bar uᵢ + Zᵢ uᵢ` almost everywhere, where `uᵢ` are the chart data of
`w` and `∂bar uᵢ` is the complex antilinear part of their weak derivative `chartDerivL`. -/
private theorem chartValueL_dataL_ae (w : A.sectionChartData.SobolevData μ p 1) (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ p 0 i (dataL A hD hDs μ p w)
      =ᵐ[μ.restrict (A.image i)] fun y ↦
        complexAntilinearPartL (A.sectionChartData.chartDerivL μ p i w y) +
          A.chartZeroOrder D i y (A.sectionChartData.chartValueL μ p 1 i w y) := by
  have h₀ := (ae_image_tangentHom_iff A μ i).1
    (A.tangentHom.sectionChartData.chartValueL_apply_ae μ p 0 i (dataL A hD hDs μ p w))
  have hres := (ae_image_tangentHom_iff A μ i).1 <| ae_all_iff.2 fun c ↦
    Wkp.value_restrictL_ae (sectionChartData_image_tangentHom A i).le 0 (chartL A hD hDs μ p i c w)
  filter_upwards [h₀, hres, ae_all_iff.2 fun c ↦ chartL_ae A hD hDs μ p i c w,
    A.sectionChartData.chartValueL_apply_ae μ p 1 i w] with y h₁ h₂ h₃ h₄
  rw [h₁, h₄]
  refine (Finset.sum_congr rfl fun c _ ↦ ?_).trans (Module.Basis.sum_coord_add_smul (finBasis ℝ F)
    (finBasis ℝ (ℂ →L[ℝ] F)) _ (A.chartZeroOrder D i y : F →ₗ[ℝ] ℂ →L[ℝ] F)
    fun j ↦ Wkp.value 1 (w i j) y)
  exact congrArg (· • _) ((h₂ c).trans ((congrArg
    (fun f : Lp ℝ p (μ.restrict (A.sectionChartData.image i)) ↦ (f : ℂ → ℝ) y)
    (Wkp.value_zero (chartL A hD hDs μ p i c w))).trans (h₃ c)))


omit [T2Space M] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- On the overlap of charts `i` and `i'`, the weak derivative of the chart data in chart `i'` of an
order-one Sobolev section is that of `y ↦ g y (uᵢ (τ y))`, by the weak chain and Leibniz rules. -/
private theorem chartDerivL_ae_overlap (w : A.sectionChartData.sobolevSections μ p 1)
    (i i' : Fin A.n) :
    ∀ᵐ y ∂μ.restrict (A.overlap i i'),
      A.sectionChartData.chartDerivL μ p i' w y =
        ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) : F →L[ℝ] F).comp
          ((A.sectionChartData.chartDerivL μ p i w (A.transition i i' y)).comp
            (fderiv ℝ (A.transition i i') y)) +
        (fderiv ℝ (fun z ↦ ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm z) :
          F →L[ℝ] F)) y).flip
          (A.sectionChartData.chartValueL μ p 1 i w (A.transition i i' y)) := by
  let O : Opens ℂ := ⟨A.overlap i i', A.isOpen_overlap i i'⟩
  have hC := A.aeTransition_sectionChartData μ
  have hτ := (A.sectionChartData.hasWeakFDerivOn_chartValueL μ p i w).comp_contDiffOn_diffeo
    (U := O) (A.contDiffOn_transition i i')
    (fun y hy y' hy' h ↦ by rw [← A.transition_transition hy, h, A.transition_transition hy'])
    (fun y hy ↦ by
      rw [A.fderiv_transition hy]
      exact ContinuousLinearEquiv.toLinearEquiv _ |>.isUnit_det'.ne_zero)
    fun y hy ↦ A.overlap_subset_image i' i (A.transition_mem_overlap hy)
  have hcoord := (A.contDiffOn_coordChangeL_transferDomain (n := 1) i i').mono
    (A.overlap_subset_transferDomain i i')
  have hprod := hτ.contDiffOn_clm_apply_of_ne_zero hcoord one_ne_zero
  have hcompat : ∀ᵐ y ∂μ.restrict O, ((A.triv i).coordChangeL ℝ (A.triv i')
      ((A.chart i').symm y) : F →L[ℝ] F)
        (A.sectionChartData.chartValueL μ p 1 i w (A.transition i i' y)) =
      A.sectionChartData.chartValueL μ p 1 i' w y := by
    filter_upwards [(A.sectionChartData.compatible_iff μ p 1).1
      (SectionChartData.compatible_of_mem hC w.property i i'),
      ae_restrict_mem (A.isOpen_overlap i i').measurableSet] with y h hy
    rw [A.sectionChartData_coordChange_of_mem hy, A.sectionChartData_transition_of_mem hy] at h
    exact h.symm
  -- `O` is the overlap as an open set and `A.sectionChartData.image i'` is the image of chart `i'`
  -- as an open set; the type ascription states the inclusion of overlap into image as one of
  -- `Opens ℂ`, which `A.overlap_subset_image` proves for the underlying sets.
  have hO : O ≤ A.sectionChartData.image i' := A.overlap_subset_image i i'
  exact ((A.sectionChartData.hasWeakFDerivOn_chartValueL μ p i' w).mono hO).ae_eq
      (hprod.congr_ae hcompat)

include hD in
omit [T2Space M] in
/-- The pointwise identity behind the compatibility of the realization on overlaps: if
`X' = g ∘ X ∘ dτ + (Dg) v` and `v' = g v`, then `∂bar X' + Z' v' = g ∘ (∂bar X + Z v) ∘ dτ`. -/
private theorem chartData_overlap_eq {i i' : Fin A.n} {y : ℂ} (hy : y ∈ A.overlap i i')
    {X X' : ℂ →L[ℝ] F} {v v' : F}
    (hX : X' = ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) : F →L[ℝ] F).comp
        (X.comp (fderiv ℝ (A.transition i i') y)) +
      (fderiv ℝ (fun z ↦ ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm z) :
        F →L[ℝ] F)) y).flip v)
    (hv : v' = ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) : F →L[ℝ] F) v) :
    complexAntilinearPartL X' + A.chartZeroOrder D i' y v' =
      ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) : F →L[ℝ] F).comp
        ((complexAntilinearPartL X + A.chartZeroOrder D i (A.transition i i' y) v).comp
          (fderiv ℝ (A.transition i i') y)) := by
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  have hcoord := (A.contDiffOn_coordChangeL_transferDomain (n := 1) i i').mono
    (A.overlap_subset_transferDomain i i')
  have hd : DifferentiableAt ℝ (fun z ↦ ((A.triv i).coordChangeL ℝ (A.triv i')
      ((A.chart i').symm z) : F →L[ℝ] F)) y :=
    (hcoord.differentiableOn one_ne_zero y hy).differentiableAt
      ((A.isOpen_overlap i i').mem_nhds hy)
  have hfd : fderiv ℝ (fun z ↦ (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm z) v) y =
      (fderiv ℝ (fun z ↦ ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm z) :
        F →L[ℝ] F)) y).flip v := by
    ext u
    exact fderiv_clm_apply_const_apply hd v u
  have key : complexAntilinearPartL (fderiv ℝ
        (fun z ↦ (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm z) v) y) +
      A.chartZeroOrder D i' y (((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) :
        F →L[ℝ] F) v) =
      ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) : F →L[ℝ] F).comp
        ((A.chartZeroOrder D i (A.transition i i' y) v).comp (fderiv ℝ (A.transition i i') y)) :=
    A.complexAntilinearPartL_fderiv_coordChangeL_add_chartZeroOrder hD hy v
  rw [hX, hv, map_add, A.complexAntilinearPartL_coordChangeL_comp hy, add_assoc, ← hfd, key,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

include hD in
/-- **Compatibility on overlaps.** The chart data of the realization of an order-one Sobolev
section satisfy the cocycle relation of one-forms on the overlap of every two charts: the term
`∂bar g` produced by differentiating the coordinate change `g` of `V` is the difference of the
zeroth-order terms of the two charts. -/
private theorem compatible_dataL (w : A.sectionChartData.sobolevSections μ p 1) (i i' : Fin A.n) :
    A.tangentHom.sectionChartData.Compatible μ p 0 (dataL A hD hDs μ p w) i i' := by
  have hC := A.aeTransition_sectionChartData μ
  have h₁ := ae_restrict_of_ae_restrict_of_subset (A.overlap_subset_image i i')
    (chartValueL_dataL_ae A hD hDs μ p w i')
  have h₂ := (A.sectionChartData.aeTransition_iff.1 hC) (i := i) (i' := i')
    (chartValueL_dataL_ae A hD hDs μ p w i)
  have h₃ := (A.sectionChartData.compatible_iff μ p 1).1
    (SectionChartData.compatible_of_mem hC w.property i i')
  refine (A.tangentHom.sectionChartData.compatible_iff μ p 0).2 ?_
  refine (ae_overlap_tangentHom_iff A μ i i').2 ?_
  filter_upwards [h₁, h₂, h₃, chartDerivL_ae_overlap A μ p w i i',
    ae_restrict_mem (A.isOpen_overlap i i').measurableSet] with y h₁ h₂ h₃ h₄ hy
  rw [A.sectionChartData_transition_of_mem hy] at h₂
  rw [A.sectionChartData_coordChange_of_mem hy, A.sectionChartData_transition_of_mem hy] at h₃
  rw [sectionChartData_transition_tangentHom A hy,
    sectionChartData_coordChange_tangentHom_apply A hy, h₁, h₂]
  exact chartData_overlap_eq A hD hy h₄ h₃

include hD in
/-- The components of the realization of an order-one Sobolev section are those of a one-form. -/
private theorem dataL_mem (w : A.sectionChartData.sobolevSections μ p 1) :
    dataL A hD hDs μ p w ∈ A.tangentHom.sectionChartData.sobolevSections μ p 0 :=
  (SectionChartData.mem_sobolevSections_iff_forall_compatible
    (A.tangentHom.aeTransition_sectionChartData μ)).2 fun i i' ↦
      compatible_dataL A hD hDs μ p w i i'

include hD in
/-- The components of the realization of an order-one Sobolev section are those of a
`(0,1)`-form: both `∂bar uᵢ` and the zeroth-order term are complex antilinear. -/
private theorem dataL_mem_zeroOne (w : A.sectionChartData.sobolevSections μ p 1) :
    (⟨dataL A hD hDs μ p w, dataL_mem A hD hDs μ p w⟩ : SobolevSection A.tangentHom μ p 0) ∈
      zeroOneSobolevSections A μ p 0 := by
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  refine mem_zeroOneSobolevSections_iff.2 fun i ↦ (ae_image_tangentHom_iff A μ i).2 ?_
  filter_upwards [chartValueL_dataL_ae A hD hDs μ p w i,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y h hy v
  have hZ (u : F) : A.chartZeroOrder D i y u (Complex.I • v) =
      -(Complex.I • A.chartZeroOrder D i y u v) := by
    rw [A.chartZeroOrder_apply_eq_coord_tangentHom hD hy]
    exact (A.isZeroOneForm_iff_coord_tangentHom i _ hy).1 (hD.isZeroOneForm _ _) v
  rw [h]
  simp only [add_apply, complexAntilinearPartL_apply_I_smul, hZ, smul_add,
    neg_add]

include hD in
/-- **The realization of a smooth real Cauchy–Riemann operator** `D` as a bounded operator
`W^{1,p}(Σ, V) → L^p(Σ, Λ^{0,1} ⊗ V)`, for `1 ≤ p ≤ ∞`. In chart `i` it sends a Sobolev section
with chart data `uᵢ` to `∂bar uᵢ + Zᵢ uᵢ`, for the weak derivative of `uᵢ` and the zeroth-order term
`Zᵢ` of `D` in chart `i` (`TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevL_ae`); on smooth
sections it is `D`
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevL_ofContMDiffSection_ae`). -/
def sobolevL : SobolevSection A μ p 1 →L[ℝ] zeroOneSobolevSections A μ p 0 :=
  (((dataL A hD hDs μ p).comp (A.sectionChartData.sobolevSections μ p 1).subtypeL).codRestrict
    (A.tangentHom.sectionChartData.sobolevSections μ p 0) (dataL_mem A hD hDs μ p)).codRestrict
      (zeroOneSobolevSections A μ p 0) (dataL_mem_zeroOne A hD hDs μ p)

/-- **The chart formula of the realization.** In chart `i`, the realization of a Sobolev section
with chart data `uᵢ` is `∂bar uᵢ + Zᵢ uᵢ` almost everywhere on the image of the chart, where
`∂bar uᵢ` is the complex antilinear part of any weak derivative `Du` of `uᵢ` and `Zᵢ` is the
zeroth-order term of `D` in chart `i`. -/
theorem chartValueL_sobolevL_ae (w : SobolevSection A μ p 1) {i : Fin A.n}
    {Du : ℂ → ℂ →L[ℝ] F}
    (hDu : HasWeakFDerivOn μ (A.image i) (A.sectionChartData.chartValueL μ p 1 i w) Du) :
    A.tangentHom.sectionChartData.chartValueL μ p 0 i
        ((hD.sobolevL A hDs μ p w : SobolevSection A.tangentHom μ p 0) :
          A.tangentHom.sectionChartData.SobolevData μ p 0)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ complexAntilinearPartL (Du y) +
        A.chartZeroOrder D i y (A.sectionChartData.chartValueL μ p 1 i w y) := by
  filter_upwards [chartValueL_dataL_ae A hD hDs μ p w i,
    (A.sectionChartData.hasWeakFDerivOn_chartValueL μ p i w).ae_eq hDu] with y h hy
  rw [← hy]
  exact h

/-- **Agreement on smooth sections.** The realization of `D` sends the Sobolev section of a `C¹`
section `s` to the `(0,1)`-form whose chart data are the readings of `D s`. -/
theorem chartValueL_sobolevL_ofContMDiffSection_ae (s : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯) (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ p 0 i
        ((hD.sobolevL A hDs μ p (SobolevSection.ofContMDiffSection A μ p 1 s) :
          SobolevSection A.tangentHom μ p 0) : A.tangentHom.sectionChartData.SobolevData μ p 0)
      =ᵐ[μ.restrict (A.image i)] A.tangentHom.coord i (D s) := by
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  have hcoord := SobolevSection.chartValueL_ofContMDiffSection_ae A μ p 1 s i
  have hc : ContDiffOn ℝ 1 (A.coord i s) (A.image i) :=
    (A.contDiffOn_coord s.contMDiff i).mono
      ((A.image_subset_chart_image_closure_dom i).trans (A.chart_image_closure_dom_subset i))
  filter_upwards [chartValueL_sobolevL_ae A hD hDs μ p _
      ((hc.hasWeakFDerivOn_fderiv (μ := μ) (Ω := A.image i)).congr_ae hcoord.symm),
    hcoord, ae_restrict_mem (A.image i).isOpen.measurableSet] with y h hc' hy
  rw [h, hc']
  exact (A.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder hD hy
    ((s.contMDiff _).mdifferentiableAt one_ne_zero)).symm

/-- **Zeroth-order perturbations.** The realizations of two smooth real Cauchy–Riemann operators `D`
and `D'` differ by a zeroth-order term: in chart `i`, the difference sends a Sobolev section with
chart data `uᵢ` to `(Zᵢ' - Zᵢ) uᵢ`, where `Zᵢ` and `Zᵢ'` are the zeroth-order terms of `D` and `D'`.
No derivative of `uᵢ` enters. -/
theorem chartValueL_sobolevL_sub_ae
    {D' : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hD' : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D')
    (hD's : ContMDiffCovariantDerivativeOn F ∞ D' univ) (w : SobolevSection A μ p 1)
    (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ p 0 i
        (((hD'.sobolevL A hD's μ p w - hD.sobolevL A hDs μ p w :
          zeroOneSobolevSections A μ p 0) : SobolevSection A.tangentHom μ p 0) :
            A.tangentHom.sectionChartData.SobolevData μ p 0)
      =ᵐ[μ.restrict (A.image i)] fun y ↦
        (A.chartZeroOrder D' i y - A.chartZeroOrder D i y)
          (A.sectionChartData.chartValueL μ p 1 i w y) := by
  have hDu := A.sectionChartData.hasWeakFDerivOn_chartValueL μ p i w
  have h₃ := (ae_image_tangentHom_iff A μ i).1 (Lp.coeFn_sub
    (A.tangentHom.sectionChartData.chartValueL μ p 0 i
      ((hD'.sobolevL A hD's μ p w : SobolevSection A.tangentHom μ p 0) :
        A.tangentHom.sectionChartData.SobolevData μ p 0))
    (A.tangentHom.sectionChartData.chartValueL μ p 0 i
      ((hD.sobolevL A hDs μ p w : SobolevSection A.tangentHom μ p 0) :
        A.tangentHom.sectionChartData.SobolevData μ p 0)))
  filter_upwards [chartValueL_sobolevL_ae A hD' hD's μ p w hDu,
    chartValueL_sobolevL_ae A hD hDs μ p w hDu, h₃] with y h₁ h₂ h₃
  rw [Submodule.coe_sub, Submodule.coe_sub, map_sub, h₃, Pi.sub_apply, h₁, h₂, sub_apply,
    add_sub_add_left_eq_sub]

end IsRealCauchyRiemannOperator

end Realization

end TauCeti
