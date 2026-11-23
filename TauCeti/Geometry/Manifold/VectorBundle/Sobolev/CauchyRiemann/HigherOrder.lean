/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ChartDeriv
import TauCeti.Analysis.Sobolev.Wkp.SmoothCoefficients

/-!
# Smooth real Cauchy–Riemann operators on higher-order Sobolev sections

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`.
A smooth real Cauchy–Riemann operator `D` on `V` extends to a bounded operator

`W^{k+1,p}(Σ, V) → W^{k,p}(Σ, Λ^{0,1} ⊗ V)`

for every natural number `k` and every `1 ≤ p ≤ ∞`
(`TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL`). This is McDuff–Salamon's realization
`W^{k,q} → W^{k-1,q}` of a real Cauchy–Riemann operator for a smooth operator on a closed surface,
at every order `k ≥ 1`; at `k = 1` it is `TauCeti.IsRealCauchyRiemannOperator.sobolevL`
(`TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL_zero`).

In chart `i` a Sobolev section with chart data `uᵢ` is sent to `∂bar uᵢ + Zᵢ uᵢ`, where `Zᵢ` is the
zeroth-order term of `D` in chart `i`, as at order one. The components of the weak derivative of
`uᵢ` are Sobolev functions of order `k` (`TauCeti.SectionChartData.chartDerivDataL`), and `∂bar`
acts on them by a constant matrix. The zeroth-order term is smooth on a neighbourhood of the
compact closure of the chart image, so multiplication by it is bounded on order-`k` Sobolev
functions (`TauCeti.Wkp.contDiffOnCLMApplyL`). The chart data obtained in this way are, almost
everywhere, those of the order-one realization of the same section, so they are the chart data of
a `(0,1)`-form.

## Main definitions

* `TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL`: the bounded realization of a smooth real
  Cauchy–Riemann operator from `W^{k+1,p}` sections to `W^{k,p}` `(0,1)`-forms.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevSuccL_ae`: in chart `i` the realization
  is `∂bar uᵢ + Zᵢ uᵢ`, for the weak derivative of the chart data `uᵢ`.
* `TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL_zero`: at order one it is the realization
  `TauCeti.IsRealCauchyRiemannOperator.sobolevL`.
* `TauCeti.IsRealCauchyRiemannOperator.zeroOneLowerOrdersL_sobolevSuccL`: the realizations at
  successive orders commute with forgetting the highest weak derivative.
* `TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevSuccL_ofContMDiffSection_ae`: on
  `C^{k+1}` sections the realization is `D`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1 and C.2.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

section HigherOrder

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealSobolevCauchyRiemannHigherOrder : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  (μ : Measure ℂ) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

namespace IsRealCauchyRiemannOperator

include hD hDs in
/-- The zeroth-order operator coefficient in chart `i`, applied at order `k` to the components of
a tuple of order `k + 1`. -/
private def zeroOrderSuccL (i : Fin A.n) :
    A.sectionChartData.SobolevData μ p (k + 1) →L[ℝ]
      (Fin (finrank ℝ (ℂ →L[ℝ] F)) → Wkp μ (A.sectionChartData.image i) p k) :=
  (Wkp.contDiffOnCLMApplyL (Omega := A.sectionChartData.image i)
    ((A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet).uniqueDiffOn
    (A.isCompact_closure_image i)
    ((A.closure_image_subset_chart_image_closure_dom i).trans
      (A.chart_image_closure_dom_subset i)) k (finBasis ℝ F) (finBasis ℝ (ℂ →L[ℝ] F))
    (by simpa only [inter_univ] using A.contDiffOn_chartZeroOrder hD hDs isOpen_univ i)).comp
    ((ContinuousLinearMap.piMap fun _ : Fin (finrank ℝ F) ↦ Wkp.lowerOrderL k).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun i : Fin A.sectionChartData.n ↦
        ∀ _ : Fin (finrank ℝ F), Wkp μ (A.sectionChartData.image i) p (k + 1)) i))

/-- The components of the zeroth-order term are, almost everywhere, those of the operator
coefficient applied to the chart data. -/
private theorem zeroOrderSuccL_apply_ae (i : Fin A.n)
    (w : A.sectionChartData.SobolevData μ p (k + 1)) :
    ∀ᵐ y ∂μ.restrict (A.sectionChartData.image i), ∀ c,
      Wkp.value k (zeroOrderSuccL A hD hDs μ p k i w c) y =
        (finBasis ℝ (ℂ →L[ℝ] F)).repr (A.chartZeroOrder D i y
          (A.sectionChartData.chartValueL μ p (k + 1) i w y)) c := by
  refine ae_all_iff.2 fun c ↦ ?_
  have hvalues :
      (ContinuousLinearMap.piMap fun _ : Fin (finrank ℝ F) ↦ Wkp.lowerOrderL
        (mu := μ) (Omega := A.sectionChartData.image i) (p := p) k)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun i : Fin A.sectionChartData.n ↦
          ∀ _ : Fin (finrank ℝ F), Wkp μ (A.sectionChartData.image i) p (k + 1)) i) w) =
        fun j ↦ Wkp.lowerOrderL k (w i j) := by
    funext j
    simp only [ContinuousLinearMap.coe_piMap', Pi.map_apply]
    -- The explicit chart-data index keeps the native product-space instances aligned.
    exact congrArg (fun u : Fin (finrank ℝ F) → Wkp μ (A.sectionChartData.image i) p (k + 1) ↦
      Wkp.lowerOrderL k (u j)) (ContinuousLinearMap.proj_apply (R := ℝ)
        (φ := fun i : Fin A.sectionChartData.n ↦
          ∀ _ : Fin (finrank ℝ F), Wkp μ (A.sectionChartData.image i) p (k + 1)) i w)
  have hz := Wkp.value_contDiffOnCLMApplyL_ae (mu := μ) (Omega := A.sectionChartData.image i)
    (p := p) (g := A.chartZeroOrder D i)
    ((A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet).uniqueDiffOn
    (A.isCompact_closure_image i)
    ((A.closure_image_subset_chart_image_closure_dom i).trans
      (A.chart_image_closure_dom_subset i)) k (finBasis ℝ F) (finBasis ℝ (ℂ →L[ℝ] F))
    (by simpa only [inter_univ] using A.contDiffOn_chartZeroOrder hD hDs isOpen_univ i)
    (fun j ↦ Wkp.lowerOrderL k (w i j)) c
  filter_upwards [hz, A.sectionChartData.chartValueL_apply_ae μ p (k + 1) i w] with y hy hv
  simp only [zeroOrderSuccL, ContinuousLinearMap.comp_apply, hvalues, hy, hv]
  refine congrArg (fun v ↦ (finBasis ℝ (ℂ →L[ℝ] F)).repr (A.chartZeroOrder D i y v) c) ?_
  exact Finset.sum_congr rfl fun j _ ↦ by rw [Wkp.value_succ, ← Wkp.lowerOrderL_apply]

include hD hDs in
/-- The `c`th component in chart `i` of the realization: the `c`th component of `∂bar uᵢ`, a
constant combination of the components of the weak derivative of `uᵢ`, plus that of the
zeroth-order term applied to `uᵢ`. -/
private def chartSuccL (i : Fin A.n) (c : Fin (finrank ℝ (ℂ →L[ℝ] F))) :
    A.sectionChartData.SobolevData μ p (k + 1) →L[ℝ] Wkp μ (A.sectionChartData.image i) p k :=
  (ContinuousLinearMap.proj c).comp
    ((SectionChartData.fiberMap μ p k complexAntilinearPartL le_rfl).comp
      (A.sectionChartData.chartDerivDataL μ p k i)) +
    (ContinuousLinearMap.proj c).comp (zeroOrderSuccL A hD hDs μ p k i)

include hD hDs in
/-- The components of the realization, before restricting to Sobolev sections. -/
private def dataSuccL :
    A.sectionChartData.SobolevData μ p (k + 1) →L[ℝ]
      A.tangentHom.sectionChartData.SobolevData μ p k :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.pi fun c ↦
    (Wkp.restrictL (sectionChartData_image_tangentHom A i).le k).comp
      (chartSuccL A hD hDs μ p k i c)

/-- The weak derivative of the chart data in chart `i`, assembled from its components. -/
private def chartDeriv (i : Fin A.n) (w : A.sectionChartData.SobolevData μ p (k + 1))
    (y : ℂ) : ℂ →L[ℝ] F :=
  ∑ a, Wkp.value k (A.sectionChartData.chartDerivDataL μ p k i w a) y •
    finBasis ℝ (ℂ →L[ℝ] F) a

/-- **The chart formula of the realization.** In chart `i`, the chart data of the realization of a
tuple `w` of order `k + 1` are `∂bar uᵢ + Zᵢ uᵢ` almost everywhere, where `uᵢ` are the chart data
of `w` and `∂bar uᵢ` is the complex antilinear part of their weak derivative. -/
private theorem chartValueL_dataSuccL_ae (w : A.sectionChartData.SobolevData μ p (k + 1))
    (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ p k i (dataSuccL A hD hDs μ p k w)
      =ᵐ[μ.restrict (A.image i)] fun y ↦
        complexAntilinearPartL (chartDeriv A μ p k i w y) +
          A.chartZeroOrder D i y (A.sectionChartData.chartValueL μ p (k + 1) i w y) := by
  have h₀ := (ae_image_tangentHom_iff A μ i).1
    (A.tangentHom.sectionChartData.chartValueL_apply_ae μ p k i (dataSuccL A hD hDs μ p k w))
  have hres := (ae_image_tangentHom_iff A μ i).1 <| ae_all_iff.2 fun c ↦
    Wkp.value_restrictL_ae (sectionChartData_image_tangentHom A i).le k
      (chartSuccL A hD hDs μ p k i c w)
  have hadd (c : Fin (finrank ℝ (ℂ →L[ℝ] F))) := Wkp.value_add_ae k
    (SectionChartData.fiberMap μ p k complexAntilinearPartL le_rfl
      (A.sectionChartData.chartDerivDataL μ p k i w) c)
    (zeroOrderSuccL A hD hDs μ p k i w c)
  filter_upwards [h₀, hres, ae_all_iff.2 hadd,
    SectionChartData.value_fiberMap_ae μ p k complexAntilinearPartL le_rfl
      (A.sectionChartData.chartDerivDataL μ p k i w),
    zeroOrderSuccL_apply_ae A hD hDs μ p k i w] with y h₁ h₂ h₃ h₄ h₅
  rw [h₁]
  have hc (c : Fin (finrank ℝ (ℂ →L[ℝ] F))) :
      Wkp.value k ((dataSuccL A hD hDs μ p k w) i c) y =
        (LinearMap.toMatrix (finBasis ℝ (ℂ →L[ℝ] F)) (finBasis ℝ (ℂ →L[ℝ] F))
          (complexAntilinearPartL (F := F)).toLinearMap).mulVec
            (fun a ↦ Wkp.value k (A.sectionChartData.chartDerivDataL μ p k i w a) y) c +
        (finBasis ℝ (ℂ →L[ℝ] F)).repr (A.chartZeroOrder D i y
          (A.sectionChartData.chartValueL μ p (k + 1) i w y)) c := by
    have hd : (dataSuccL A hD hDs μ p k w) i c =
        Wkp.restrictL (sectionChartData_image_tangentHom A i).le k
          (chartSuccL A hD hDs μ p k i c w) := rfl
    rw [hd, h₂ c]
    refine (h₃ c).trans ?_
    rw [Pi.add_apply, h₄ c, h₅ c]
  have hL := Matrix.toLin_apply (finBasis ℝ (ℂ →L[ℝ] F)) (finBasis ℝ (ℂ →L[ℝ] F))
    (LinearMap.toMatrix (finBasis ℝ (ℂ →L[ℝ] F)) (finBasis ℝ (ℂ →L[ℝ] F))
      (complexAntilinearPartL (F := F)).toLinearMap) (chartDeriv A μ p k i w y)
  rw [Matrix.toLin_toMatrix, ContinuousLinearMap.coe_coe, chartDeriv,
    (finBasis ℝ (ℂ →L[ℝ] F)).repr_sum_self] at hL
  simp_rw [hc, add_smul, Finset.sum_add_distrib, ← hL, Basis.sum_repr]
  rfl

/-- The order-one Sobolev section underlying a Sobolev section of order `k + 1`. -/
private def toOrderOne (w : SobolevSection A μ p (k + 1)) : SobolevSection A μ p 1 :=
  A.sectionChartData.lowerOrdersL μ p 1 k ((Nat.add_comm k 1) ▸ w)

omit [IsManifold 𝓘(ℂ) ∞ M] [T2Space M] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
private theorem chartValueL_toOrderOne (w : SobolevSection A μ p (k + 1)) (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p 1 i (toOrderOne A μ p k w) =
      A.sectionChartData.chartValueL μ p (k + 1) i w := by
  exact (A.sectionChartData.chartValueL_lowerOrdersL μ p 1 k _ i).trans
    (A.sectionChartData.chartValueL_eqRec μ p (Nat.add_comm k 1) w i)

/-- The chart data of the realization of `w` are, almost everywhere, those of the order-one
realization of `w`. -/
private theorem chartValueL_dataSuccL_ae_sobolevL (w : SobolevSection A μ p (k + 1))
    (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ p k i (dataSuccL A hD hDs μ p k w)
      =ᵐ[μ.restrict (A.image i)] A.tangentHom.sectionChartData.chartValueL μ p 0 i
        ((hD.sobolevL A hDs μ p (toOrderOne A μ p k w) : SobolevSection A.tangentHom μ p 0) :
          A.tangentHom.sectionChartData.SobolevData μ p 0) := by
  have hDu : HasWeakFDerivOn μ (A.image i)
      (A.sectionChartData.chartValueL μ p 1 i (toOrderOne A μ p k w))
      (chartDeriv A μ p k i w) := by
    rw [chartValueL_toOrderOne]
    exact A.sectionChartData.hasWeakFDerivOn_chartValueL_chartDerivDataL μ p k i w
  filter_upwards [chartValueL_dataSuccL_ae A hD hDs μ p k w i,
    chartValueL_sobolevL_ae A hD hDs μ p (toOrderOne A μ p k w) hDu] with y h₁ h₂
  rw [h₁, h₂, chartValueL_toOrderOne]

include hD in
/-- The components of the realization of a Sobolev section of order `k + 1` are those of a
`V`-valued one-form of order `k`. -/
private theorem dataSuccL_mem (w : SobolevSection A μ p (k + 1)) :
    dataSuccL A hD hDs μ p k w ∈ A.tangentHom.sectionChartData.sobolevSections μ p k := by
  obtain ⟨s, hs⟩ := A.tangentHom.sectionChartData.exists_section μ p 0
    (hD.sobolevL A hDs μ p (toOrderOne A μ p k w) : SobolevSection A.tangentHom μ p 0)
  exact (A.tangentHom.sectionChartData.mem_sobolevSections_iff μ p k).2
    ⟨s, fun i ↦ Filter.EventuallyEq.trans ((ae_image_tangentHom_iff A μ i).2
      (chartValueL_dataSuccL_ae_sobolevL A hD hDs μ p k w i)) (hs i)⟩

include hD in
/-- The components of the realization of a Sobolev section of order `k + 1` are those of a
`(0,1)`-form, since they are almost everywhere those of the order-one realization. -/
private theorem dataSuccL_mem_zeroOne (w : SobolevSection A μ p (k + 1)) :
    (⟨dataSuccL A hD hDs μ p k w, dataSuccL_mem A hD hDs μ p k w⟩ :
      SobolevSection A.tangentHom μ p k) ∈ zeroOneSobolevSections A μ p k := by
  have h := mem_zeroOneSobolevSections_iff.1 (hD.sobolevL A hDs μ p (toOrderOne A μ p k w)).property
  refine mem_zeroOneSobolevSections_iff.2 fun i ↦ ?_
  filter_upwards [h i, (ae_image_tangentHom_iff A μ i).2
    (chartValueL_dataSuccL_ae_sobolevL A hD hDs μ p k w i)] with y hy heq v
  rw [heq]
  exact hy v

include hD in
/-- **The realization of a smooth real Cauchy–Riemann operator at order `k + 1`** `D` as a bounded
operator `W^{k+1,p}(Σ, V) → W^{k,p}(Σ, Λ^{0,1} ⊗ V)`, for `1 ≤ p ≤ ∞`. In chart `i` it sends a
Sobolev section with chart data `uᵢ` to `∂bar uᵢ + Zᵢ uᵢ`, for the weak derivative of `uᵢ` and the
zeroth-order term `Zᵢ` of `D` in chart `i`
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevSuccL_ae`). -/
def sobolevSuccL : SobolevSection A μ p (k + 1) →L[ℝ] zeroOneSobolevSections A μ p k :=
  (((dataSuccL A hD hDs μ p k).comp
    (A.sectionChartData.sobolevSections μ p (k + 1)).subtypeL).codRestrict
      (A.tangentHom.sectionChartData.sobolevSections μ p k)
      (dataSuccL_mem A hD hDs μ p k)).codRestrict
    (zeroOneSobolevSections A μ p k) (dataSuccL_mem_zeroOne A hD hDs μ p k)

/-- **The chart formula of the realization.** In chart `i`, the realization of a Sobolev section
of order `k + 1` with chart data `uᵢ` is `∂bar uᵢ + Zᵢ uᵢ` almost everywhere on the image of the
chart, where `∂bar uᵢ` is the complex antilinear part of any weak derivative `Du` of `uᵢ` and `Zᵢ`
is the zeroth-order term of `D` in chart `i`. -/
theorem chartValueL_sobolevSuccL_ae (w : SobolevSection A μ p (k + 1)) {i : Fin A.n}
    {Du : ℂ → ℂ →L[ℝ] F}
    (hDu : HasWeakFDerivOn μ (A.image i) (A.sectionChartData.chartValueL μ p (k + 1) i w) Du) :
    A.tangentHom.sectionChartData.chartValueL μ p k i
        ((hD.sobolevSuccL A hDs μ p k w : SobolevSection A.tangentHom μ p k) :
          A.tangentHom.sectionChartData.SobolevData μ p k)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ complexAntilinearPartL (Du y) +
        A.chartZeroOrder D i y (A.sectionChartData.chartValueL μ p (k + 1) i w y) := by
  filter_upwards [chartValueL_dataSuccL_ae A hD hDs μ p k w i,
    (A.sectionChartData.hasWeakFDerivOn_chartValueL_chartDerivDataL μ p k i w).ae_eq hDu]
    with y h hy
  rw [← hy]
  exact h

/-- **Agreement at order one.** The realization from `W^{1,p}` is
`TauCeti.IsRealCauchyRiemannOperator.sobolevL`. -/
theorem sobolevSuccL_zero : hD.sobolevSuccL A hDs μ p 0 = hD.sobolevL A hDs μ p := by
  refine ContinuousLinearMap.ext fun w ↦ Subtype.ext <|
    SectionChartData.eq_of_chartValueL_ae_eq fun (i : Fin A.n) ↦
      (ae_image_tangentHom_iff A μ i).2 ?_
  have hDu := A.sectionChartData.hasWeakFDerivOn_chartValueL μ p i w
  filter_upwards [chartValueL_sobolevSuccL_ae A hD hDs μ p 0 w hDu,
    chartValueL_sobolevL_ae A hD hDs μ p w hDu] with y h₁ h₂
  rw [h₁, h₂]

/-- **Compatibility with the order.** Forgetting the highest weak derivative of the realization of
a Sobolev section of order `k + 2` gives the realization of the section regarded as one of order
`k + 1`. -/
theorem zeroOneLowerOrdersL_sobolevSuccL (w : SobolevSection A μ p (k + 1 + 1)) :
    zeroOneLowerOrdersL A μ p k 1 (hD.sobolevSuccL A hDs μ p (k + 1) w) =
      hD.sobolevSuccL A hDs μ p k (A.sectionChartData.lowerOrderL μ p (k + 1) w) := by
  refine Subtype.ext <| SectionChartData.eq_of_chartValueL_ae_eq fun (i : Fin A.n) ↦
    (ae_image_tangentHom_iff A μ i).2 ?_
  have hDu := A.sectionChartData.hasWeakFDerivOn_chartValueL_chartDerivDataL μ p (k + 1) i w
  have hlow : A.sectionChartData.chartValueL μ p (k + 1) i
      (A.sectionChartData.lowerOrderL μ p (k + 1) w) =
        A.sectionChartData.chartValueL μ p (k + 1 + 1) i w :=
    A.sectionChartData.chartValueL_coe_lowerOrderL μ p (k + 1) w i
  have hDu' : HasWeakFDerivOn μ (A.image i) (A.sectionChartData.chartValueL μ p (k + 1) i
      (A.sectionChartData.lowerOrderL μ p (k + 1) w)) _ := hlow ▸ hDu
  have hcoe : A.tangentHom.sectionChartData.chartValueL μ p k i
      ((zeroOneLowerOrdersL A μ p k 1 (hD.sobolevSuccL A hDs μ p (k + 1) w) :
        SobolevSection A.tangentHom μ p k) : A.tangentHom.sectionChartData.SobolevData μ p k) =
      A.tangentHom.sectionChartData.chartValueL μ p (k + 1) i
        ((hD.sobolevSuccL A hDs μ p (k + 1) w : SobolevSection A.tangentHom μ p (k + 1)) :
          A.tangentHom.sectionChartData.SobolevData μ p (k + 1)) := by
    rw [coe_zeroOneLowerOrdersL]
    exact A.tangentHom.sectionChartData.chartValueL_lowerOrdersL μ p k 1 _ i
  rw [hcoe]
  filter_upwards [chartValueL_sobolevSuccL_ae A hD hDs μ p (k + 1) w hDu,
    chartValueL_sobolevSuccL_ae A hD hDs μ p k _ hDu'] with y h₁ h₂
  rw [h₁, h₂, hlow]

/-- **Agreement on smooth sections.** The realization of `D` sends the Sobolev section of a
`C^{k+1}` section `s` to the `(0,1)`-form whose chart data are the readings of `D s`. -/
theorem chartValueL_sobolevSuccL_ofContMDiffSection_ae
    (s : Cₛ^((k + 1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); F, V⟯) (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ p k i
        ((hD.sobolevSuccL A hDs μ p k (SobolevSection.ofContMDiffSection A μ p (k + 1) s) :
          SobolevSection A.tangentHom μ p k) : A.tangentHom.sectionChartData.SobolevData μ p k)
      =ᵐ[μ.restrict (A.image i)] A.tangentHom.coord i (D s) := by
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  have hcoord := SobolevSection.chartValueL_ofContMDiffSection_ae A μ p (k + 1) s i
  have hc : ContDiffOn ℝ 1 (A.coord i s) (A.image i) :=
    ((A.contDiffOn_coord s.contMDiff i).of_le (by exact_mod_cast Nat.le_add_left 1 k)).mono
      ((A.image_subset_chart_image_closure_dom i).trans (A.chart_image_closure_dom_subset i))
  filter_upwards [chartValueL_sobolevSuccL_ae A hD hDs μ p k _
      ((hc.hasWeakFDerivOn_fderiv (μ := μ) (Ω := A.image i)).congr_ae hcoord.symm),
    hcoord, ae_restrict_mem (A.image i).isOpen.measurableSet] with y h hc' hy
  rw [h, hc']
  exact (A.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder hD hy
    ((s.contMDiff _).mdifferentiableAt (by simp))).symm

end IsRealCauchyRiemannOperator

end HigherOrder

end TauCeti
