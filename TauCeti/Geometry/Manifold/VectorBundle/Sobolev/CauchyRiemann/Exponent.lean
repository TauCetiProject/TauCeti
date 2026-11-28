/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Fredholm
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Exponent
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.PartitionOfUnity
import TauCeti.Analysis.Fredholm.Regularity
import TauCeti.Analysis.Normed.Module.Annihilator
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.ExtendByZero

/-!
# The cokernel and the index of a smooth real Cauchy–Riemann operator do not depend on `p`

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`
(so `M` is compact). Let `D` be a smooth real Cauchy–Riemann operator on `V`, realized as
`D_p : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` (`TauCeti.IsRealCauchyRiemannOperator.sobolevL`). For
`1 < p ≤ p' < ∞`, the inclusions `j : W^{1,p'} → W^{1,p}` and `ι : L^{p'} → Lᵖ` lowering the
exponent (`TauCeti.SectionChartData.ofExponentLEL`, `TauCeti.zeroOneOfExponentLEL`) satisfy
`D_p ∘ j = ι ∘ D_{p'}` (`TauCeti.IsRealCauchyRiemannOperator.sobolevL_ofExponentLEL`). This file
proves the regularity property of this square: a `W^{1,p}` section `ξ` with `D ξ ∈ L^{p'}` is in
`W^{1,p'}` (`TauCeti.IsRealCauchyRiemannOperator.exists_ofExponentLEL_eq_of_sobolevL_eq`). Since
`ι` has dense range (`TauCeti.denseRange_zeroOneOfExponentLEL`) and `D_p` is Fredholm, the general
comparison `ContinuousLinearMap.IsFredholm.index_eq_of_regularity` and
`LinearMap.cokerEquivOfRegularity` then show that `ι` identifies the cokernels
(`TauCeti.IsRealCauchyRiemannOperator.cokerSobolevLEquiv`) and that the index of `D_p` does not
depend on `p` (`TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_eq_of_exponent`). This is the
cokernel half of McDuff–Salamon, Theorem C.1.10 (i) (regularity of kernel and cokernel), proved as
Theorem C.2.3, for smooth operators on closed surfaces; the kernel half is
`TauCeti.IsRealCauchyRiemannOperator.kerSobolevLEquiv`.

## The argument

Let `Λ` be a continuous functional on `L^{p'}` vanishing on the range of `D_{p'}`. In every chart
it is integration against a covector field solving the adjoint equation weakly
(`TauCeti.exists_memLp_forall_integral_eq_zero_of_annihilator`), which is smooth
(`TauCeti.IsRealCauchyRiemannOperator.exists_contDiffOn_ae_eq_of_forall_integral_eq_zero`), so
bounded on compact sets. Cutting off by a partition of unity, `|Λ w|` is at most a constant times
the `L¹` norm of `w`, in particular times its `Lᵖ` norm
(`TauCeti.IsRealCauchyRiemannOperator.exists_norm_apply_le_of_annihilator`). By Hahn–Banach, `Λ`
is `Λ' ∘ ι` for a continuous functional `Λ'` on `Lᵖ`, and `Λ'` vanishes on the range of `D_p`:
it vanishes on the images of smooth sections, which are dense in `W^{1,p}`. So if `ι y` is in the
range of `D_p`, then `Λ y = 0` for every such `Λ`, and `y` lies in the closed range of `D_{p'}`
(`TauCeti.IsRealCauchyRiemannOperator.mem_range_sobolevL_of_zeroOneOfExponentLEL_mem`). Given
`ξ ∈ W^{1,p}` with `D ξ = ι y`, write `y = D ξ'`; then `ξ - j ξ'` is in the kernel of `D_p`,
which consists of smooth sections.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.sobolevL_ofExponentLEL`: the realizations commute with
  lowering the exponent.
* `TauCeti.IsRealCauchyRiemannOperator.exists_norm_apply_le_of_annihilator`: an annihilator of the
  range at exponent `p'` is bounded in the `Lᵖ` norm for every `p ≤ p'`.
* `TauCeti.IsRealCauchyRiemannOperator.exists_ofExponentLEL_eq_of_sobolevL_eq`: a `W^{1,p}`
  section `ξ` with `D ξ ∈ L^{p'}` is in `W^{1,p'}`.
* `TauCeti.IsRealCauchyRiemannOperator.cokerSobolevLEquiv`: the cokernels at `p ≤ p'` are linearly
  equivalent through lowering the exponent.
* `TauCeti.IsRealCauchyRiemannOperator.finrank_quotient_range_sobolevL_eq`,
  `TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_eq_of_exponent`: the dimension of the
  cokernel and the index do not depend on `1 < p < ∞`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10 (i) and Theorem C.2.3.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold Distributions Topology

namespace TauCeti

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannExponent : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p p' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')]

namespace IsRealCauchyRiemannOperator

/-- **The realizations commute with lowering the exponent.** For `p ≤ p'` and any additive Haar
measure `μ` on the charts, the realization of `D` at exponent `p` of the `W^{1,p}` copy of a
`W^{1,p'}` section `w` is the `Lᵖ` copy of the realization of `D` at exponent `p'` of `w`. -/
theorem sobolevL_ofExponentLEL (μ : Measure ℂ) [μ.IsAddHaarMeasure] (hpp' : p ≤ p')
    (w : SobolevSection A μ p' 1) :
    hD.sobolevL A hDs μ p (A.sectionChartData.ofExponentLEL μ 1 hpp' w) =
      zeroOneOfExponentLEL A μ 0 hpp' (hD.sobolevL A hDs μ p' w) := by
  refine Subtype.ext (SectionChartData.eq_of_chartValueL_ae_eq fun (i : Fin A.n) ↦ ?_)
  refine (ae_image_tangentHom_iff A μ i).2 ?_
  -- Lowering the exponent keeps the chart data, as functions.
  have hw : (A.sectionChartData.chartValueL μ p 1 i
      (A.sectionChartData.ofExponentLEL μ 1 hpp' w) : ℂ → F) =
        A.sectionChartData.chartValueL μ p' 1 i w :=
    SectionChartData.coeFn_chartValueL_ofExponentLEL (C := A.sectionChartData) hpp' w i
  have hDw : (A.tangentHom.sectionChartData.chartValueL μ p 0 i
      (A.tangentHom.sectionChartData.ofExponentLEL μ 0 hpp'
        (hD.sobolevL A hDs μ p' w)) : ℂ → ℂ →L[ℝ] F) =
        A.tangentHom.sectionChartData.chartValueL μ p' 0 i
          (hD.sobolevL A hDs μ p' w : SobolevSection A.tangentHom μ p' 0) :=
    SectionChartData.coeFn_chartValueL_ofExponentLEL (C := A.tangentHom.sectionChartData) hpp'
      _ i
  have hDu := A.sectionChartData.hasWeakFDerivOn_chartValueL μ p' i w
  rw [coe_zeroOneOfExponentLEL, hDw]
  filter_upwards [chartValueL_sobolevL_ae A hD hDs μ p _ (hw ▸ hDu),
    chartValueL_sobolevL_ae A hD hDs μ p' w hDu] with y h₁ h₂
  rw [h₁, h₂, hw]

/-! ### Annihilators of the range are bounded in `L¹` -/

omit [IsManifold 𝓘(ℂ) ∞ M] [T2Space M] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- A point `z` of the image of chart `i` at which `χ` read in chart `i` does not vanish lies in
`Q₀`, if the support of `χ` read in chart `i` lies in `Q₀ ⊆ Aᵢ`. -/
private theorem mem_of_apply_chart_symm_ne_zero {i : Fin A.n} {Q₀ : Set ℂ}
    (hQ₀ : Q₀ ⊆ A.image i) {χ : M → ℝ} (hχ : tsupport χ ⊆ (A.chart i).symm '' Q₀) {z : ℂ}
    (hz : z ∈ A.image i) (hχz : χ ((A.chart i).symm z) ≠ 0) : z ∈ Q₀ := by
  obtain ⟨z₀, hz₀, hzz₀⟩ := hχ (subset_tsupport _ hχz)
  have ht := A.image_subset_target_inter_preimage_baseSet i
  rwa [← (A.chart i).symm.injOn (ht (hQ₀ hz₀)).1 (ht hz).1 hzz₀]

omit [T2Space M] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The pairing of a covector `θ` with the value on `1` of the complex antilinear part of `c • L`
is at most `‖θ‖` times the norm of `ContinuousLinearMap.complexAntilinearPartL`, `|c|` and
`‖L‖`. -/
private theorem norm_apply_complexAntilinearPartL_smul_le (θ : F →L[ℝ] ℝ) (c : ℝ)
    (L : ℂ →L[ℝ] F) : ‖θ (complexAntilinearPartL (c • L) 1)‖ ≤
      ‖θ‖ * (‖(complexAntilinearPartL : (ℂ →L[ℝ] F) →L[ℝ] ℂ →L[ℝ] F)‖ * (|c| * ‖L‖)) := by
  refine (θ.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  refine (ContinuousLinearMap.le_opNorm_of_le _ (norm_one (α := ℂ)).le).trans ?_
  rw [mul_one, ← Real.norm_eq_abs, ← norm_smul]
  exact ContinuousLinearMap.le_opNorm _ _

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- **The bound in one chart.** Let `Q₀ ⊆ Q₁ ⊆ Aᵢ`, let `χ` be a smooth function with
`|χ| ≤ 1` and with support read in chart `i` inside `Q₀`, and let the covector field `θ` represent
`Λ` over `Q₁` and be bounded by `M₀` on `Q₀`. Then `Λ` of the `(0,1)`-projection of `χ w` is at
most `M₀` times the norm of `ContinuousLinearMap.complexAntilinearPartL`, the norm of the chart-`i`
reading at exponent `1`, and the `L¹` norm of `w`. -/
private theorem norm_apply_zeroOnePartSobolevL_le {i : Fin A.n} {Q₀ Q₁ : Opens ℂ}
    (hQ₀₁ : Q₀ ≤ Q₁) (hQ₁ : (Q₁ : Set ℂ) ⊆ A.image i) {χ : M → ℝ}
    (hχs : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ) (hχ : tsupport χ ⊆ (A.chart i).symm '' Q₀)
    (hχ1 : ∀ x, |χ x| ≤ 1) {Λ : zeroOneSobolevSections A volume p' 0 →L[ℝ] ℝ}
    {θ : ℂ → F →L[ℝ] ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (hrep : ∀ w : zeroOneSobolevSections A volume p' 0,
      (w : SobolevSection A.tangentHom volume p' 0) ∈
          SobolevSection.aeZeroOff A.tangentHom volume p' 0 ((A.chart i).symm '' Q₁) →
        Λ w = ∫ z in Q₁, θ z (A.tangentHom.sectionChartData.chartValueL volume p' 0 i
          ((w : SobolevSection A.tangentHom volume p' 0) :
            A.tangentHom.sectionChartData.SobolevData volume p' 0) z 1))
    (hθ : ∀ᵐ z ∂volume.restrict Q₁, z ∈ Q₀ → ‖θ z‖ ≤ M₀)
    (w : SobolevSection A.tangentHom volume p' 0) :
    ‖Λ (zeroOnePartSobolevL A volume p' 0
        (SobolevSection.contMDiffSMulL A.tangentHom volume p' 0 hχs w))‖ ≤
      M₀ * ‖(complexAntilinearPartL : (ℂ →L[ℝ] F) →L[ℝ] ℂ →L[ℝ] F)‖ *
        ‖A.tangentHom.sectionChartData.chartValueL volume 1 0 i‖ *
          ‖A.tangentHom.sectionChartData.ofExponentLEL volume 0 (Fact.out : 1 ≤ p') w‖ := by
  set K := ‖(complexAntilinearPartL : (ℂ →L[ℝ] F) →L[ℝ] ℂ →L[ℝ] F)‖
  set v := A.tangentHom.sectionChartData.chartValueL volume p' 0 i
    (w : A.tangentHom.sectionChartData.SobolevData volume p' 0)
  -- The chart reading of the `L¹` copy of `w` is the chart reading of `w`.
  set u := A.tangentHom.sectionChartData.chartValueL volume 1 0 i
    (A.tangentHom.sectionChartData.ofExponentLEL volume 0 (Fact.out : 1 ≤ p') w :
      A.tangentHom.sectionChartData.SobolevData volume 1 0)
  have hu : (u : ℂ → ℂ →L[ℝ] F) = v :=
    SectionChartData.coeFn_chartValueL_ofExponentLEL (C := A.tangentHom.sectionChartData) _ w i
  have hQ₁t : (Q₁ : Set ℂ) ⊆ A.tangentHom.sectionChartData.image i := by
    rwa [sectionChartData_image_tangentHom]
  have hmem := SobolevSection.aeZeroOff_mono (hχ.trans (image_mono hQ₀₁))
    (zeroOnePartSobolevL_mem_aeZeroOff (SobolevSection.contMDiffSMulL_mem_aeZeroOff hχs w))
  rw [hrep _ hmem]
  have hint : Integrable (fun z ↦ M₀ * K * ‖u z‖) (volume.restrict Q₁) :=
    ((L1.integrable_coeFn u).norm.const_mul _).mono_measure (Measure.restrict_mono hQ₁t le_rfl)
  refine (norm_integral_le_of_norm_le hint ?_).trans ?_
  · filter_upwards [hθ, ae_restrict_of_ae_restrict_of_subset hQ₁t
        (chartValueL_zeroOnePartSobolevL_ae
          (SobolevSection.contMDiffSMulL A.tangentHom volume p' 0 hχs w) i),
      ae_restrict_of_ae_restrict_of_subset hQ₁t
        ((ae_image_tangentHom_iff A volume i).2 ((A.image_tangentHom i).symm ▸
          SobolevSection.chartValueL_contMDiffSMulL_ae hχs w i)),
      ae_restrict_mem Q₁.isOpen.measurableSet] with z hθz h₁ h₂ hz
    rw [h₁, h₂, hu]
    by_cases hχz : χ ((A.tangentHom.chart i).symm z) = 0
    · simp only [hχz, zero_smul, map_zero, zero_apply, norm_zero]
      positivity
    -- Where `χ` does not vanish, `z` lies in `Q₀`, where `θ` is bounded by `M₀`.
    have hzQ₀ := mem_of_apply_chart_symm_ne_zero A ((SetLike.coe_subset_coe.2 hQ₀₁).trans hQ₁)
      hχ (hQ₁ hz) hχz
    refine (norm_apply_complexAntilinearPartL_smul_le _ _ _).trans ?_
    calc ‖θ z‖ * (K * (|χ ((A.tangentHom.chart i).symm z)| * ‖v z‖))
        ≤ M₀ * (K * (1 * ‖v z‖)) := by gcongr; exacts [hθz hzQ₀, hχ1 _]
      _ = M₀ * K * ‖v z‖ := by ring
  · calc ∫ z in Q₁, M₀ * K * ‖u z‖
        = M₀ * K * ∫ z in Q₁, ‖u z‖ := integral_const_mul _ _
      _ ≤ M₀ * K * ∫ z in A.tangentHom.sectionChartData.image i, ‖u z‖ :=
          mul_le_mul_of_nonneg_left (setIntegral_mono_set (L1.integrable_coeFn u).norm
            (.of_forall fun _ ↦ norm_nonneg _) (.of_forall hQ₁t)) (by positivity)
      _ = M₀ * K * ‖u‖ := by rw [L1.norm_eq_integral_norm]
      _ ≤ M₀ * K * (‖A.tangentHom.sectionChartData.chartValueL volume 1 0 i‖ *
          ‖A.tangentHom.sectionChartData.ofExponentLEL volume 0 (Fact.out : 1 ≤ p') w‖) := by
          gcongr
          rw [← Submodule.norm_coe]
          exact ContinuousLinearMap.le_opNorm _ _
      _ = _ := by ring

include hD hDs in
/-- **Annihilators of the range are bounded in `L¹`.** Let `1 < p' < ∞` and `Λ` a continuous
functional on the `L^{p'}` `(0,1)`-forms vanishing on the range of the realization of `D`. There
is a constant `C` with `|Λ w| ≤ C ‖w‖_{L¹}` for every `w`. The covector fields representing `Λ` in
the charts are smooth, hence bounded on compact sets. -/
private theorem exists_norm_apply_le_norm_ofExponentLEL_one (hp' : 1 < p') (hp'_top : p' ≠ ⊤)
    (Λ : zeroOneSobolevSections A volume p' 0 →L[ℝ] ℝ)
    (hΛ : ∀ w, Λ (hD.sobolevL A hDs volume p' w) = 0) :
    ∃ C : ℝ, ∀ w : zeroOneSobolevSections A volume p' 0, ‖Λ w‖ ≤
      C * ‖A.tangentHom.sectionChartData.ofExponentLEL volume 0 (Fact.out : 1 ≤ p')
        (w : SobolevSection A.tangentHom volume p' 0)‖ := by
  have hpq : p'.HolderConjugate p'.conjExponent := .conjExponent hp'.le
  have : Fact (1 ≤ p'.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p'⟩
  have hq : 1 < p'.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt (p := p') (q := p'.conjExponent)).1 hp'_top.lt_top
  obtain ⟨χ, Q₀, Q₁, Q₂, Q₃, hχ, hQ₀, hQ₁, hQ₂, hQ₃, -⟩ := A.exists_nested_chart_sets
  have hQ₁i (i : Fin A.n) : closure (Q₁ i : Set ℂ) ⊆ A.image i :=
    (hQ₁ i).2.trans (subset_closure.trans ((hQ₂ i).trans (subset_closure.trans (hQ₃ i))))
  have hQ₀₁ (i : Fin A.n) : Q₀ i ≤ Q₁ i := subset_closure.trans (hQ₀ i).2
  -- In every chart, the field representing `Λ` over `Q₁` is smooth, hence bounded on `Q₀`.
  choose θ hθ hrep hweak using fun i ↦
    exists_memLp_forall_integral_eq_zero_of_annihilator (q := p'.conjExponent) A hD hDs hp'
      hp'_top Λ hΛ i (hQ₁i i)
  choose g hg hθg using fun i ↦ exists_contDiffOn_ae_eq_of_forall_integral_eq_zero A hD hDs
    (subset_closure.trans (hQ₁i i)) hq (hθ i).memLpLoc (hweak i)
  choose M₀ hM₀ using fun i ↦ (hQ₀ i).1.exists_bound_of_continuousOn
    ((hg i).continuousOn.mono (hQ₀ i).2)
  have hθM (i : Fin A.n) : ∀ᵐ z ∂volume.restrict (Q₁ i), z ∈ Q₀ i → ‖θ i z‖ ≤ max (M₀ i) 0 :=
    (hθg i).mono fun z hz hzQ ↦ hz ▸ (hM₀ i _ (subset_closure hzQ)).trans (le_max_left _ _)
  have hχ1 (i : Fin A.n) (x : M) : |χ i x| ≤ 1 :=
    abs_le.2 ⟨by linarith [χ.nonneg i x], χ.le_one i x⟩
  refine ⟨∑ i, max (M₀ i) 0 * ‖(complexAntilinearPartL : (ℂ →L[ℝ] F) →L[ℝ] ℂ →L[ℝ] F)‖ *
    ‖A.tangentHom.sectionChartData.chartValueL volume 1 0 i‖, fun w ↦ ?_⟩
  -- `w` is the sum of the `(0,1)`-projections of the `χᵢ w`.
  have h1 (x : M) : ∑ i, χ i x = 1 := by
    simpa [finsum_eq_sum_of_fintype] using χ.sum_eq_one (mem_univ x)
  calc ‖Λ w‖ = ‖∑ i, Λ (zeroOnePartSobolevL A volume p' 0
        (SobolevSection.contMDiffSMulL A.tangentHom volume p' 0 (χ i).contMDiff w))‖ := by
        rw [← map_sum,
          sum_zeroOnePartSobolevL_contMDiffSMulL_eq_self (fun i ↦ (χ i).contMDiff) h1]
    _ ≤ _ := (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
        norm_apply_zeroOnePartSobolevL_le A (hQ₀₁ i) (subset_closure.trans (hQ₁i i))
          (χ i).contMDiff (hχ i) (hχ1 i) (le_max_right _ _) (hrep i) (hθM i) w)
    _ = _ := (Finset.sum_mul _ _ _).symm

include hD hDs in
/-- **Annihilators of the range are bounded in `Lᵖ`.** Let `1 < p' < ∞`, `1 ≤ p ≤ p'`, and `Λ` a
continuous functional on the `L^{p'}` `(0,1)`-forms vanishing on the range of the realization of
`D`. There is a constant `C` with `|Λ w| ≤ C ‖w‖_{Lᵖ}` for every `w`: the covector fields
representing `Λ` in the charts are smooth, so `Λ` is even bounded in the `L¹` norm. -/
theorem exists_norm_apply_le_of_annihilator (hp' : 1 < p') (hp'_top : p' ≠ ⊤) (hpp' : p ≤ p')
    (Λ : zeroOneSobolevSections A volume p' 0 →L[ℝ] ℝ)
    (hΛ : ∀ w, Λ (hD.sobolevL A hDs volume p' w) = 0) :
    ∃ C : ℝ, ∀ w, ‖Λ w‖ ≤ C * ‖zeroOneOfExponentLEL A volume 0 hpp' w‖ := by
  obtain ⟨C, hC⟩ := exists_norm_apply_le_norm_ofExponentLEL_one A hD hDs hp' hp'_top Λ hΛ
  set ι₁ := A.tangentHom.sectionChartData.ofExponentLEL volume 0 (Fact.out : 1 ≤ p)
  refine ⟨|C| * ‖ι₁‖, fun w ↦ (hC w).trans ?_⟩
  rw [← SectionChartData.ofExponentLEL_ofExponentLEL (Fact.out : 1 ≤ p) hpp', mul_assoc,
    ← Submodule.norm_coe (zeroOneOfExponentLEL A volume 0 hpp' w), coe_zeroOneOfExponentLEL]
  exact (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (ι₁.le_opNorm _) (abs_nonneg C))

include hD hDs in
/-- **Annihilators extend to lower exponents.** Let `1 ≤ p ≤ p' < ∞` with `p' > 1`, and `Λ` a
continuous functional on the `L^{p'}` `(0,1)`-forms vanishing on the range of the realization of
`D`. Then `Λ = Λ' ∘ ι` for a continuous functional `Λ'` on the `Lᵖ` `(0,1)`-forms vanishing on the
range of the realization of `D` at exponent `p`, where `ι` lowers the exponent. -/
theorem exists_comp_zeroOneOfExponentLEL_eq_of_annihilator (hp' : 1 < p') (hp'_top : p' ≠ ⊤)
    (hpp' : p ≤ p') (Λ : zeroOneSobolevSections A volume p' 0 →L[ℝ] ℝ)
    (hΛ : ∀ w, Λ (hD.sobolevL A hDs volume p' w) = 0) :
    ∃ Λ' : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ,
      (∀ w, Λ' (hD.sobolevL A hDs volume p w) = 0) ∧
        ∀ w, Λ' (zeroOneOfExponentLEL A volume 0 hpp' w) = Λ w := by
  obtain ⟨C, hC⟩ := exists_norm_apply_le_of_annihilator A hD hDs hp' hp'_top hpp' Λ hΛ
  set ι := zeroOneOfExponentLEL A volume 0 hpp'
  -- `Λ` read on the range of `ι` is bounded, so it extends by Hahn–Banach.
  let e := LinearEquiv.ofInjective ι.toLinearMap (zeroOneOfExponentLEL_injective hpp')
  let f := ((Λ : _ →ₗ[ℝ] ℝ).comp e.symm.toLinearMap).mkContinuous C fun y ↦ by
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa [e] using hC x
  obtain ⟨Λ', hΛ', -⟩ := exists_extension_norm_eq _ f
  have hι (w : zeroOneSobolevSections A volume p' 0) : Λ' (ι w) = Λ w := by
    refine (hΛ' (e w)).trans ?_
    simp [f]
  refine ⟨Λ', fun w ↦ ?_, hι⟩
  -- `Λ' ∘ D_p` vanishes on the dense set of smooth sections.
  have hp_top : p ≠ ⊤ := ne_top_of_le_ne_top hp'_top hpp'
  refine congrFun ((SobolevSection.denseRange_ofContMDiffSection A volume p 1 hp_top).equalizer
    (Λ'.comp (hD.sobolevL A hDs volume p)).continuous continuous_const (funext fun s ↦ ?_)) w
  rw [Function.comp_apply, ContinuousLinearMap.comp_apply,
    ← SobolevSection.ofExponentLEL_ofContMDiffSection hpp', sobolevL_ofExponentLEL, hι, hΛ,
    Function.comp_apply]

/-! ### Regularity and the cokernels -/

include hD hDs in
/-- **The range at a higher exponent.** For `1 < p'  < ∞` and `p ≤ p'`, an `L^{p'}` `(0,1)`-form
whose `Lᵖ` copy is in the range of the realization of `D` at exponent `p` is in the range of the
realization at exponent `p'`: every annihilator `Λ` of the range at `p'` is `Λ' ∘ ι` for an
annihilator `Λ'` of the range at `p`, and the range at `p'` is closed. -/
theorem mem_range_sobolevL_of_zeroOneOfExponentLEL_mem (hp' : 1 < p') (hp'_top : p' ≠ ⊤)
    (hpp' : p ≤ p') {y : zeroOneSobolevSections A volume p' 0}
    (hy : zeroOneOfExponentLEL A volume 0 hpp' y ∈ (hD.sobolevL A hDs volume p).range) :
    y ∈ (hD.sobolevL A hDs volume p').range := by
  obtain ⟨ξ, hξ⟩ := hy
  rw [← (isClosed_range_sobolevL A hD hDs hp' hp'_top).submodule_topologicalClosure_eq,
    Submodule.mem_topologicalClosure_iff_forall_dual_eq_zero]
  rintro Λ hΛ
  obtain ⟨Λ', hΛ'D, hΛ'⟩ := exists_comp_zeroOneOfExponentLEL_eq_of_annihilator A hD hDs hp'
    hp'_top hpp' Λ fun w ↦ hΛ _ ⟨w, rfl⟩
  rw [← hΛ', ← hξ]
  exact hΛ'D ξ

include hD hDs in
/-- **Regularity for the exponent** (McDuff–Salamon, Theorem C.1.10 (i), regularity of kernel and
cokernel, proved as Theorem C.2.3, for smooth operators on closed surfaces). For
`1 < p ≤ p' < ∞`, a `W^{1,p}` section `ξ` with `D ξ ∈ L^{p'}` is a `W^{1,p'}` section. By
`TauCeti.IsRealCauchyRiemannOperator.mem_range_sobolevL_of_zeroOneOfExponentLEL_mem`,
`D ξ = D ξ'` for some `W^{1,p'}` section `ξ'`, and `ξ - ξ'` is in the kernel, which consists of
smooth sections. -/
theorem exists_ofExponentLEL_eq_of_sobolevL_eq (hp : 1 < p) (hp'_top : p' ≠ ⊤) (hpp' : p ≤ p')
    {ξ : SobolevSection A volume p 1} {y : zeroOneSobolevSections A volume p' 0}
    (hξ : hD.sobolevL A hDs volume p ξ = zeroOneOfExponentLEL A volume 0 hpp' y) :
    ∃ ξ' : SobolevSection A volume p' 1, A.sectionChartData.ofExponentLEL volume 1 hpp' ξ' = ξ := by
  obtain ⟨ξ₀, hξ₀⟩ := mem_range_sobolevL_of_zeroOneOfExponentLEL_mem A hD hDs
    (hp.trans_le hpp') hp'_top hpp' ⟨ξ, hξ⟩
  rw [ContinuousLinearMap.coe_coe] at hξ₀
  subst hξ₀
  -- `ξ` minus the `W^{1,p}` copy of `ξ₀` is in the kernel, so it is a smooth section.
  have hker : hD.sobolevL A hDs volume p
      (ξ - A.sectionChartData.ofExponentLEL volume 1 hpp' ξ₀) = 0 := by
    rw [map_sub, hξ, sobolevL_ofExponentLEL, sub_self]
  obtain ⟨s, hs, hξs, -⟩ := exists_contMDiff_of_sobolevL_eq_zero A hD hDs hp hker
  refine ⟨ξ₀ + SobolevSection.ofContMDiffSection A volume p' 1 ⟨s, hs.of_le (by simp)⟩, ?_⟩
  rw [map_add, SobolevSection.ofExponentLEL_ofContMDiffSection, ← hξs, add_sub_cancel]

/-- **The cokernel does not depend on the exponent** (McDuff–Salamon, Theorem C.1.10 (i),
regularity of kernel and cokernel, proved as Theorem C.2.3, for smooth operators on closed
surfaces). For `1 < p ≤ p' < ∞`, lowering the exponent induces a linear
equivalence from the cokernel of the realization `W^{1,p'}(M, V) → L^{p'}(M, Λ^{0,1} ⊗ V)` of a
smooth real Cauchy–Riemann operator to the cokernel of its realization
`W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)`
(`TauCeti.IsRealCauchyRiemannOperator.cokerSobolevLEquiv_mk`). -/
def cokerSobolevLEquiv (hp : 1 < p) (hp'_top : p' ≠ ⊤) (hpp' : p ≤ p') :
    (zeroOneSobolevSections A volume p' 0 ⧸ (hD.sobolevL A hDs volume p').range) ≃ₗ[ℝ]
      zeroOneSobolevSections A volume p 0 ⧸ (hD.sobolevL A hDs volume p).range :=
  LinearMap.cokerEquivOfRegularity (sobolevL_ofExponentLEL A hD hDs volume hpp')
    (zeroOneOfExponentLEL_injective hpp')
    (fun _ _ ↦ exists_ofExponentLEL_eq_of_sobolevL_eq A hD hDs hp hp'_top hpp')
    ((isFredholm_sobolevL A hD hDs hp (ne_top_of_le_ne_top hp'_top hpp')).range_sup_range_eq_top
      (denseRange_zeroOneOfExponentLEL A volume 0 hpp'))

/-- The equivalence of cokernels sends the class of `w` to the class of its `Lᵖ` copy. -/
@[simp]
theorem cokerSobolevLEquiv_mk (hp : 1 < p) (hp'_top : p' ≠ ⊤) (hpp' : p ≤ p')
    (w : zeroOneSobolevSections A volume p' 0) :
    cokerSobolevLEquiv A hD hDs hp hp'_top hpp' (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (zeroOneOfExponentLEL A volume 0 hpp' w) :=
  LinearMap.cokerEquivOfRegularity_mk _ _ _ _ w

/-- **The dimension of the cokernel does not depend on the exponent.** -/
theorem finrank_quotient_range_sobolevL_eq (hp : 1 < p) (hp_top : p ≠ ⊤) (hp' : 1 < p')
    (hp'_top : p' ≠ ⊤) :
    finrank ℝ (zeroOneSobolevSections A volume p 0 ⧸ (hD.sobolevL A hDs volume p).range) =
      finrank ℝ (zeroOneSobolevSections A volume p' 0 ⧸ (hD.sobolevL A hDs volume p').range) := by
  rcases le_total p p' with hpp' | hp'p
  · exact (cokerSobolevLEquiv A hD hDs hp hp'_top hpp').finrank_eq.symm
  · exact (cokerSobolevLEquiv A hD hDs hp' hp_top hp'p).finrank_eq

include hD hDs in
/-- For `1 < p ≤ p' < ∞`, the realizations of `D` at `p` and `p'` have the same index. -/
private theorem index_sobolevL_eq_of_le (hp : 1 < p) (hp'_top : p' ≠ ⊤) (hpp' : p ≤ p') :
    (hD.sobolevL A hDs volume p').index = (hD.sobolevL A hDs volume p).index :=
  (isFredholm_sobolevL A hD hDs hp (ne_top_of_le_ne_top hp'_top hpp')).index_eq_of_regularity
    (sobolevL_ofExponentLEL A hD hDs volume hpp')
    (SectionChartData.ofExponentLEL_injective hpp') (zeroOneOfExponentLEL_injective hpp')
    (denseRange_zeroOneOfExponentLEL A volume 0 hpp')
    (fun _ _ ↦ exists_ofExponentLEL_eq_of_sobolevL_eq A hD hDs hp hp'_top hpp')

include hD hDs in
/-- **The index does not depend on the exponent** (McDuff–Salamon, Theorem C.1.10 (i),
regularity of kernel and cokernel, proved as Theorem C.2.3, for smooth operators on closed
surfaces). For `1 < p, p' < ∞`, the realizations
`W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` and `W^{1,p'}(M, V) → L^{p'}(M, Λ^{0,1} ⊗ V)` of a smooth real
Cauchy–Riemann operator have the same Fredholm index. -/
theorem index_sobolevL_eq_of_exponent (hp : 1 < p) (hp_top : p ≠ ⊤) (hp' : 1 < p')
    (hp'_top : p' ≠ ⊤) :
    (hD.sobolevL A hDs volume p).index = (hD.sobolevL A hDs volume p').index := by
  rcases le_total p p' with hpp' | hp'p
  · exact (index_sobolevL_eq_of_le A hD hDs hp hp'_top hpp').symm
  · exact index_sobolevL_eq_of_le A hD hDs hp' hp_top hp'p

end IsRealCauchyRiemannOperator

end TauCeti
