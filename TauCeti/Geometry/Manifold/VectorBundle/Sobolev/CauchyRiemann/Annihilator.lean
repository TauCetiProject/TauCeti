/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Basic
public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Transfer
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Transfer
import TauCeti.MeasureTheory.Function.Lp.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Annihilators of the range of a smooth real Cauchy–Riemann operator

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`
(so `M` is compact). Let `D` be a smooth real Cauchy–Riemann operator on `V` and
`D : W^{1,p}(Σ, V) → Lᵖ(Σ, Λ^{0,1} ⊗ V)` its realization
(`TauCeti.IsRealCauchyRiemannOperator.sobolevL`), for `1 < p < ∞`. The cokernel of `D` is
described by the continuous functionals `Λ` on the `Lᵖ` `(0,1)`-forms that vanish on the range of
`D`. This file shows that such a `Λ` is, in every chart, a weak solution of the adjoint equation:
over every open `Q` with compact closure in the image of chart `i` there is an `L^q` covector field
`θ`, `q` the conjugate exponent, with `∫ θ ((∂bar φ + Zᵢ φ)(1)) = 0` for every test function `φ` on
`Q`, where `Zᵢ` is the zeroth-order term of `D` in chart `i`
(`TauCeti.exists_memLp_forall_integral_eq_zero_of_annihilator`). A `(0,1)`-form is complex
antilinear, so it is determined by its value on `1`, and `θ` pairs with that value. This is the
hypothesis of the planar regularity theorem for annihilators of real Cauchy–Riemann operators
(`TauCeti.memWkpLoc_succ_of_forall_integral_apply_cauchyRiemann_eq_zero`, for `J = i` and
`S = 2 Zᵢ(·)(1)`), which makes `θ` smooth.

The proof extends `Λ` by Hahn–Banach to all chart data of one-forms
(`TauCeti.exists_extension_zeroOneSobolevSections`) and represents the block of every chart `j` by
`L^q` coefficients (the duality `MeasureTheory.Lp.exists_memLp_forall_dual_pi_apply_eq`). A
`(0,1)`-form supported over `Q` has chart-`j` data supported in the part of chart `j` that sees `Q`
(`TauCeti.FiniteBundleAtlas.localizedImage`), where they are the transfer of its chart-`i` data
(`TauCeti.FiniteBundleAtlas.restrictL_eq_transferL`). So `Λ` restricted to such forms is a
continuous functional of the chart-`i` data over `Q`, again represented by `L^q` coefficients. A
test function `φ` on `Q` is the reading of a smooth section `ξ`
(`TauCeti.FiniteBundleAtlas.exists_contMDiff_eqOn_coord`), and `Λ (D ξ) = 0` is the weak equation.

## Main results

* `TauCeti.FiniteBundleAtlas.closure_localizedImage_subset_transferDomain`: the localized image of
  a relatively compact `Q` lies, with its closure, in the transfer domain of charts `i` and `j`.
* `TauCeti.FiniteBundleAtlas.exists_contMDiff_eqOn_coord`: a smooth function with compact support
  in a chart image is the reading of a smooth section, supported over its support.
* `TauCeti.exists_extension_zeroOneSobolevSections`: functionals on `Lᵖ` `(0,1)`-forms extend to
  all chart data of one-forms.
* `TauCeti.exists_memLp_forall_integral_eq_zero_of_annihilator`: an annihilator of the range of
  `D` is, in every chart, an `L^q` weak solution of the adjoint equation.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.2.3 (the cokernel step).
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace Complex
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold Distributions Topology

namespace TauCeti

namespace FiniteBundleAtlas

section Localization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  {G : Type*} [TopologicalSpace G] {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, TopologicalSpace (W x)] [FiberBundle G W] (B : FiniteBundleAtlas ℂ M G W)

/-- The points of the image of chart `j` whose preimage lies in the domain of chart `i` and is
read in chart `i` inside `Q`: the part of chart `j` that sees data supported over `Q`. -/
def localizedImage (i j : Fin B.n) (Q : Opens ℂ) : Opens ℂ :=
  ⟨(B.image j : Set ℂ) ∩ (B.chart j).symm ⁻¹' (B.dom i ∩ B.chart i ⁻¹' Q), by
    refine (B.continuousOn_chart_symm j).isOpen_inter_preimage (B.image j).isOpen ?_
    exact ((B.chart i).continuousOn.mono (B.dom_subset_chart_source i)).isOpen_inter_preimage
      (B.isOpen_dom i) Q.isOpen⟩

variable {B}

theorem mem_localizedImage {i j : Fin B.n} {Q : Opens ℂ} {y : ℂ} :
    y ∈ B.localizedImage i j Q ↔ y ∈ B.image j ∧ (B.chart j).symm y ∈ B.dom i ∧
      B.chart i ((B.chart j).symm y) ∈ Q :=
  Iff.rfl

theorem localizedImage_subset_overlap (i j : Fin B.n) (Q : Opens ℂ) :
    (B.localizedImage i j Q : Set ℂ) ⊆ B.overlap i j := by
  rintro y ⟨hy, hi, -⟩
  refine B.mem_overlap.2 ⟨(B.chart j).symm y, ⟨hi, B.symm_mem_dom hy⟩, ?_⟩
  exact (B.chart j).right_inv (B.closure_image_subset_target j (subset_closure hy))

theorem isCompact_closure_localizedImage (i j : Fin B.n) (Q : Opens ℂ) :
    IsCompact (closure (B.localizedImage i j Q : Set ℂ)) :=
  (B.isCompact_closure_image j).of_isClosed_subset isClosed_closure
    (closure_mono inter_subset_left)

theorem mapsTo_localizedImage (i j : Fin B.n) (Q : Opens ℂ) :
    MapsTo ((B.chart j).symm ≫ₕ B.chart i) (B.localizedImage i j Q) Q :=
  fun _ hy ↦ hy.2.2

/-- Over a relatively compact `Q ⊆ A.image i`, the closure of the localized image lies in the
domain on which data are transferred from chart `i` to chart `j`. -/
theorem closure_localizedImage_subset_transferDomain [T2Space M] {i j : Fin B.n} {Q : Opens ℂ}
    (hQc : IsCompact (closure (Q : Set ℂ))) (hQi : closure (Q : Set ℂ) ⊆ B.image i) :
    closure (B.localizedImage i j Q : Set ℂ) ⊆ B.transferDomain i j := by
  -- The points of `M` read in chart `i` inside `closure Q` form a compact subset of `dom i`.
  set K := (B.chart i).symm '' closure (Q : Set ℂ)
  have hK : IsCompact K := hQc.image_of_continuousOn ((B.continuousOn_chart_symm i).mono hQi)
  have hKi : K ⊆ B.dom i := by
    rintro _ ⟨z, hz, rfl⟩
    exact B.symm_mem_dom (hQi hz)
  have hS : IsClosed (closure (B.image j : Set ℂ) ∩ (B.chart j).symm ⁻¹' K) :=
    ((B.chart j).continuousOn_symm.mono
      (B.closure_image_subset_target j)).preimage_isClosed_of_isClosed isClosed_closure hK.isClosed
  have hPS : (B.localizedImage i j Q : Set ℂ) ⊆
      closure (B.image j : Set ℂ) ∩ (B.chart j).symm ⁻¹' K := by
    intro y hy
    obtain ⟨hyj, hyi, hyQ⟩ := mem_localizedImage.1 hy
    refine ⟨subset_closure hyj, B.chart i ((B.chart j).symm y), subset_closure hyQ, ?_⟩
    exact (B.chart i).left_inv (B.dom_subset_chart_source i hyi)
  refine (closure_minimal hPS hS).trans fun y hy ↦ ?_
  · obtain ⟨x, hx, rfl⟩ := B.closure_image_subset_chart_image_closure_dom j hy.1
    have hxs : x ∈ (B.chart j).source := B.closure_dom_subset_source j hx
    have hxK := hy.2
    rw [mem_preimage, (B.chart j).left_inv hxs] at hxK
    refine B.mem_transferDomain.2 ⟨(B.chart j).map_source hxs, ?_⟩
    rw [(B.chart j).left_inv hxs]
    exact ⟨B.dom_subset_chart_source i (hKi hxK), B.closure_dom_subset_baseSet j hx,
      B.dom_subset_baseSet i (hKi hxK)⟩

/-- A point of the image of chart `j` outside the localized image does not come from a point of
`Q` read in chart `i`. -/
theorem symm_notMem_image_of_notMem_localizedImage {i j : Fin B.n} {Q : Opens ℂ} {K : Set ℂ}
    (hKQ : K ⊆ Q) (hQi : (Q : Set ℂ) ⊆ B.image i) {y : ℂ} (hy : y ∈ B.image j)
    (hyP : y ∉ B.localizedImage i j Q) : (B.chart j).symm y ∉ (B.chart i).symm '' K := by
  rintro ⟨z, hz, hzy⟩
  have hzi : z ∈ B.image i := hQi (hKQ hz)
  refine hyP (mem_localizedImage.2 ⟨hy, hzy ▸ B.symm_mem_dom hzi, ?_⟩)
  rw [← hzy, (B.chart i).right_inv (B.closure_image_subset_target i (subset_closure hzi))]
  exact hKQ hz

end Localization

section TestSection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)

/-- **Smooth sections from chart functions.** A smooth function `φ` with compact support inside
the image of chart `i` is the reading in chart `i` of a smooth section, supported over the image
of the support of `φ` under the inverse chart. -/
theorem exists_contMDiff_eqOn_coord {i : Fin A.n} {φ : ℂ → F} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφi : tsupport φ ⊆ A.image i) :
    ∃ ξ : Π x, V x, ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (T% ξ) ∧
      EqOn (A.coord i ξ) φ (A.image i) ∧
      closure {x | ξ x ≠ 0} ⊆ (A.chart i).symm '' tsupport φ := by
  have := A.compactSpace
  set K := (A.chart i).symm '' tsupport φ
  have hK : IsCompact K := hφc.image_of_continuousOn ((A.continuousOn_chart_symm i).mono hφi)
  have hKi : K ⊆ A.dom i := by
    rintro _ ⟨z, hz, rfl⟩
    exact A.symm_mem_dom (hφi hz)
  obtain ⟨U, hUo, hKU, hUi, -⟩ := exists_open_between_and_isCompact_closure hK (A.isOpen_dom i) hKi
  obtain ⟨ψ, hψ1, hψ0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, ℂ) (n := (⊤ : ℕ∞))
    hK.isClosed (hKU.trans (interior_maximal subset_closure hUo))
  have hψi : tsupport ψ ⊆ A.dom i :=
    (closure_minimal (fun x (hx : x ∈ Function.support ψ) ↦ by_contra fun h ↦ hx (hψ0 x h))
      isClosed_closure).trans hUi
  have hψK : ∀ x ∈ K, ψ x = 1 := fun x hx ↦ hψ1.self_of_nhdsSet x hx
  refine ⟨fun x ↦ ψ x • A.chartSection i φ x, A.contMDiff_smul_chartSection ψ.contMDiff hψi
    hφ.contDiffOn, fun y hy ↦ ?_, closure_minimal (fun x hx ↦ ?_) hK.isClosed⟩
  · rw [A.coord_fun_smul i _ _ hy, coord_chartSection φ hy]
    by_cases hφy : φ y = 0
    · rw [hφy, smul_zero]
    · rw [hψK _ ⟨y, subset_tsupport φ hφy, rfl⟩, one_smul]
  · by_contra hxK
    refine hx ?_
    simp only
    rw [chartSection_eq_zero fun hxi ↦ ?_, smul_zero]
    by_contra hφx
    refine hxK ⟨A.chart i x, subset_tsupport φ hφx, ?_⟩
    exact (A.chart i).left_inv (A.dom_subset_chart_source i hxi)

end TestSection

end FiniteBundleAtlas

end TauCeti

namespace TauCeti

open SmoothAlmostComplexStructure FiniteBundleAtlas

section Annihilator

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannAnnihilator : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- **Extending functionals on Sobolev `(0,1)`-forms.** A continuous functional on the `Lᵖ`
`(0,1)`-forms extends, by Hahn–Banach, to the space of all chart data of `V`-valued one-forms. -/
theorem exists_extension_zeroOneSobolevSections
    (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ) :
    ∃ Λ' : A.tangentHom.sectionChartData.SobolevData volume p 0 →L[ℝ] ℝ,
      ∀ w : zeroOneSobolevSections A volume p 0,
        Λ' ((w : SobolevSection A.tangentHom volume p 0) :
          A.tangentHom.sectionChartData.SobolevData volume p 0) = Λ w := by
  obtain ⟨g₁, hg₁, -⟩ := exists_extension_norm_eq (zeroOneSobolevSections A volume p 0) Λ
  obtain ⟨g₂, hg₂, -⟩ := exists_extension_norm_eq
    (A.tangentHom.sectionChartData.sobolevSections volume p 0) g₁
  exact ⟨g₂, fun w ↦ (hg₂ _).trans (hg₁ w)⟩

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] [FiniteDimensional ℝ F] in
/-- A continuous functional on the chart data of one-forms is the sum over the charts of its
restrictions to the chart blocks. -/
private theorem apply_eq_sum_single
    (Λ' : A.tangentHom.sectionChartData.SobolevData volume p 0 →L[ℝ] ℝ)
    (v : A.tangentHom.sectionChartData.SobolevData volume p 0) :
    Λ' v = ∑ j, Λ' (Pi.single j (v j)) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  exact map_sum Λ' _ _

variable {q : ℝ≥0∞} [hq₁ : Fact (1 ≤ q)] [hpq : p.HolderConjugate q]

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] [FiniteDimensional ℝ F] in
/-- **Chartwise representation.** For `1 < p < ∞`, the restriction of a continuous functional on
the chart data of one-forms to the block of chart `j` is integration against an `L^q` field of
coefficients, one for each component. -/
private theorem exists_memLp_apply_single_eq (hp : 1 < p) (hp_top : p ≠ ⊤)
    (Λ' : A.tangentHom.sectionChartData.SobolevData volume p 0 →L[ℝ] ℝ)
    (j : Fin A.tangentHom.sectionChartData.n) :
    ∃ H : ℂ → EuclideanSpace ℝ (Fin (finrank ℝ (ℂ →L[ℝ] F))),
      MemLp H q (volume.restrict (A.tangentHom.sectionChartData.image j)) ∧
      ∀ g : Fin (finrank ℝ (ℂ →L[ℝ] F)) →
          Lp ℝ p (volume.restrict (A.tangentHom.sectionChartData.image j : Set ℂ)),
        Λ' (Pi.single j g) = ∑ c, ∫ x in A.tangentHom.sectionChartData.image j, H x c * g c x := by
  obtain ⟨H, hH, -, hΛ⟩ := MeasureTheory.Lp.exists_memLp_forall_dual_pi_apply_eq (p := q) (q := p)
    hp hp_top (EuclideanSpace.basisFun (Fin (finrank ℝ (ℂ →L[ℝ] F))) ℝ)
    (Λ'.comp (ContinuousLinearMap.single ℝ
      (fun j ↦ Fin (finrank ℝ (ℂ →L[ℝ] F)) →
        Wkp volume (A.tangentHom.sectionChartData.image j) p 0) j))
  exact ⟨H, hH, fun g ↦ by simpa [EuclideanSpace.inner_single_right] using hΛ g⟩

include hq₁ hpq in
/-- **Localizing a functional to one chart.** Let `Q` be open with compact closure in the image of
chart `i`, and `1 < p < ∞`. There is a continuous functional `ℓ` on chart-`i` data over `Q` such
that every continuous functional `Λ'` on the chart data of one-forms agrees with `ℓ` on the
`Lᵖ` one-forms supported over `Q`: on those whose chart-`j` data vanish off the localized image,
`Λ' w = ℓ (w_i|_Q)`. -/
private theorem exists_localization (hp : 1 < p) (hp_top : p ≠ ⊤)
    (Λ' : A.tangentHom.sectionChartData.SobolevData volume p 0 →L[ℝ] ℝ)
    (i : Fin A.tangentHom.sectionChartData.n) {Q : Opens ℂ} (hQc : IsCompact (closure (Q : Set ℂ)))
    (hQi : closure (Q : Set ℂ) ⊆ A.tangentHom.image i)
    (hQ : Q ≤ A.tangentHom.sectionChartData.image i) :
    ∃ ℓ : (Fin (finrank ℝ (ℂ →L[ℝ] F)) → Wkp volume Q p 0) →L[ℝ] ℝ,
      ∀ w ∈ A.tangentHom.sectionChartData.sobolevSections volume p 0,
        (∀ (j : Fin A.tangentHom.sectionChartData.n) c,
          ∀ᵐ y ∂volume.restrict (A.tangentHom.sectionChartData.image j : Set ℂ),
          y ∉ A.tangentHom.localizedImage i j Q → Wkp.value 0 (w j c) y = 0) →
        Λ' w = ℓ fun c ↦ Wkp.restrictL hQ 0 (w i c) := by
  choose H hH hΛ using exists_memLp_apply_single_eq (q := q) A hp hp_top Λ'
  -- The localized images and the transfer of chart-`i` data to them.
  set P : Fin A.tangentHom.sectionChartData.n → Opens ℂ := fun j ↦ A.tangentHom.localizedImage i j Q
  have hPj (j : Fin A.tangentHom.sectionChartData.n) :
      P j ≤ A.tangentHom.sectionChartData.image j := fun _ hy ↦ hy.1
  have hPc (j : Fin A.tangentHom.sectionChartData.n) :=
    A.tangentHom.isCompact_closure_localizedImage i j Q
  have hPD (j : Fin A.tangentHom.sectionChartData.n) :=
    A.tangentHom.closure_localizedImage_subset_transferDomain (j := j) hQc hQi
  have hPQ (j : Fin A.tangentHom.sectionChartData.n) := A.tangentHom.mapsTo_localizedImage i j Q
  -- The coefficients of chart `j`, restricted to its localized image.
  set G : (j : Fin A.tangentHom.sectionChartData.n) → Fin (finrank ℝ (ℂ →L[ℝ] F)) →
      Lp ℝ q (volume.restrict (P j : Set ℂ)) :=
    fun j c ↦ (((hH j).continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) c)).mono_measure
      (Measure.restrict_mono (hPj j) le_rfl)).toLp _
  refine ⟨∑ j, ∑ c, (MeasureTheory.Lp.toDual ℝ _ q p (G j c)).comp
    ((ContinuousLinearMap.proj c).comp (A.tangentHom.transferL volume p 0 i j (hPc j) (hPD j)
      (hPQ j))), fun w hw hvan ↦ ?_⟩
  rw [apply_eq_sum_single A Λ' w]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hΛ j]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have htr := A.tangentHom.restrictL_eq_transferL volume p 0 hw
    (A.tangentHom.localizedImage_subset_overlap i j Q) (hPc j) (hPD j) hQ (hPQ j) c
  rw [MeasureTheory.Lp.toDual_apply]
  erw [← htr]
  -- Pass from the chart image to the localized image, where the data are the restricted data.
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
    (A.tangentHom.sectionChartData.image j).isOpen.measurableSet.nullMeasurableSet (hPj j) ?_]
  · refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (((hH j).continuousLinearMap_comp
        (EuclideanSpace.proj (𝕜 := ℝ) c)).mono_measure (Measure.restrict_mono (hPj j) le_rfl)),
      Wkp.value_restrictL_ae (hPj j) 0 (w j c)] with y hy₁ hy₂
    simp only [G]
    rw [hy₁]
    rw [Wkp.value_zero, Wkp.value_zero] at hy₂
    exact (congrArg (fun t ↦ (EuclideanSpace.proj (𝕜 := ℝ) c) (H j y) * t) hy₂).symm
  · have h := (ae_restrict_iff' (A.tangentHom.sectionChartData.image j).isOpen.measurableSet).1
      (hvan j c)
    filter_upwards [h] with y hy hyd
    rw [← Wkp.value_zero (w j c), hy hyd.1 hyd.2, mul_zero]

omit [FiniteDimensional ℝ F] [IsScalarTower ℝ ℂ F] in
/-- A complex antilinear real-linear map `L : ℂ → F` is `w ↦ conj w • L 1`, written with real and
imaginary parts: `L = Re ⊗ L 1 - Im ⊗ i L 1`. -/
private theorem eq_smulRightL_of_antilinear {L : ℂ →L[ℝ] F}
    (hL : ∀ v, L (Complex.I • v) = -(Complex.I • L v)) :
    L = StrongDual.smulRightL ℝ ℂ F reCLM (L 1) -
      StrongDual.smulRightL ℝ ℂ F imCLM (Complex.I • L 1) := by
  refine ContinuousLinearMap.ext fun w ↦ ?_
  have hw : w = w.re • (1 : ℂ) + w.im • (Complex.I • (1 : ℂ)) := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hw, map_add, map_smul, map_smul, hL]
  simp [sub_eq_add_neg, smul_neg]

/-- The `c`-th component, in the basis `Module.finBasis ℝ (ℂ →L[ℝ] F)`, of the complex antilinear
map with value `v` on `1`. -/
private def oneComponentL (c : Fin (finrank ℝ (ℂ →L[ℝ] F))) : F →L[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap ((finBasis ℝ (ℂ →L[ℝ] F)).coord c)).comp
    (StrongDual.smulRightL ℝ ℂ F reCLM -
      (StrongDual.smulRightL ℝ ℂ F imCLM).comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I))

/-- A complex antilinear map is read off its value on `1`. -/
private theorem oneComponentL_apply_one {L : ℂ →L[ℝ] F}
    (hL : ∀ v, L (Complex.I • v) = -(Complex.I • L v)) (c : Fin (finrank ℝ (ℂ →L[ℝ] F))) :
    oneComponentL c (L 1) = (finBasis ℝ (ℂ →L[ℝ] F)).repr L c := by
  conv_rhs => rw [eq_smulRightL_of_antilinear hL]
  simp [oneComponentL]

variable {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)

include hD hDs in
/-- The chart data of the realization of a smooth section `ξ` read, in chart `j`, as the components
of the reading of `D ξ`. -/
private theorem value_sobolevL_ae (ξ : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯) (j : Fin A.n)
    (c : Fin (finrank ℝ (ℂ →L[ℝ] F))) :
    (Wkp.value 0 (((hD.sobolevL A hDs volume p (SobolevSection.ofContMDiffSection A volume p 1 ξ) :
        SobolevSection A.tangentHom volume p 0) :
          A.tangentHom.sectionChartData.SobolevData volume p 0) j c) : ℂ → ℝ)
      =ᵐ[volume.restrict (A.image j)]
        fun y ↦ (finBasis ℝ (ℂ →L[ℝ] F)).repr (A.tangentHom.coord j (D ξ) y) c := by
  have h1 := IsRealCauchyRiemannOperator.chartValueL_sobolevL_ofContMDiffSection_ae A hD hDs
    volume p ξ j
  have hmem (y : ℂ) (hy : y ∈ A.image j) : y ∈ A.tangentHom.image j := by
    rwa [A.image_tangentHom]
  have h2 : A.tangentHom.sectionChartData.chartValueL volume p 0 j
      ((hD.sobolevL A hDs volume p (SobolevSection.ofContMDiffSection A volume p 1 ξ) :
        SobolevSection A.tangentHom volume p 0) :
          A.tangentHom.sectionChartData.SobolevData volume p 0)
      =ᵐ[volume.restrict (A.tangentHom.sectionChartData.image j)]
        A.tangentHom.sectionChartData.coord j (D ξ) := by
    refine (ae_image_tangentHom_iff A volume j).2 ?_
    filter_upwards [h1, ae_restrict_mem (A.image j).isOpen.measurableSet] with y hy hyi
    rw [hy, A.tangentHom.sectionChartData_coord_of_mem (D ξ) (hmem y hyi)]
  refine (ae_image_tangentHom_iff A volume j).1 ?_
  filter_upwards [SectionChartData.value_ae_eq_repr_coord h2 c,
    ae_restrict_mem (A.tangentHom.sectionChartData.image j).isOpen.measurableSet] with y hy hyi
  rw [hy, A.tangentHom.sectionChartData_coord_of_mem (D ξ) hyi]

include hD in
omit [T2Space M] in
/-- On the image of chart `i`, the reading of `D ξ` for a section `ξ` read as `φ` in chart `i` is
`∂bar φ + Zᵢ φ`. -/
private theorem coord_tangentHom_eq_of_eqOn {i : Fin A.n} {ξ : Π x, V x}
    (hξ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (T% ξ)) {φ : ℂ → F}
    (hξi : EqOn (A.coord i ξ) φ (A.image i)) {z : ℂ} (hz : z ∈ A.image i) :
    A.tangentHom.coord i (D ξ) z =
      complexAntilinearPartL (fderiv ℝ φ z) + A.chartZeroOrder D i z (φ z) := by
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  have hev : A.coord i ξ =ᶠ[𝓝 z] φ :=
    Filter.eventuallyEq_of_mem ((A.image i).isOpen.mem_nhds hz) hξi
  refine (A.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder hD hz
    ((hξ _).mdifferentiableAt (by simp))).trans ?_
  rw [hev.fderiv_eq, hξi hz]

include hD hDs in
/-- The chart data of the realization of a smooth section supported over `Q`, read in chart `i`,
vanish off the localized images. -/
private theorem value_sobolevL_eq_zero_of_notMem_localizedImage {i : Fin A.n} {Q : Opens ℂ}
    (hQi : (Q : Set ℂ) ⊆ A.tangentHom.image i) {K : Set ℂ} (hKQ : K ⊆ Q) (ξ : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯)
    (hξK : closure {x | ξ x ≠ 0} ⊆ (A.chart i).symm '' K)
    (j : Fin A.tangentHom.sectionChartData.n) (c : Fin (finrank ℝ (ℂ →L[ℝ] F))) :
    ∀ᵐ y ∂volume.restrict (A.tangentHom.sectionChartData.image j : Set ℂ),
      y ∉ A.tangentHom.localizedImage i j Q →
        Wkp.value 0 (((hD.sobolevL A hDs volume p
          (SobolevSection.ofContMDiffSection A volume p 1 ξ) :
            SobolevSection A.tangentHom volume p 0) :
              A.tangentHom.sectionChartData.SobolevData volume p 0) j c) y = 0 := by
  refine (ae_image_tangentHom_iff A volume j).2 ?_
  filter_upwards [value_sobolevL_ae A (p := p) hD hDs ξ j c,
    ae_restrict_mem (A.image j).isOpen.measurableSet] with y hy hyj hyP
  have hz : A.tangentHom.coord (j : Fin A.n) (D ξ) y = 0 :=
    A.tangentHom.coord_eq_zero (A.image_tangentHom j ▸ hyj)
      (hD.apply_eq_zero_of_notMem_closure fun h ↦
        symm_notMem_image_of_notMem_localizedImage (B := A.tangentHom) hKQ hQi
          (A.image_tangentHom j ▸ hyj) hyP (hξK h))
  rw [hy]
  exact (congrArg (fun v ↦ (finBasis ℝ (ℂ →L[ℝ] F)).repr v c) hz).trans (by simp)

include hD hDs hq₁ hpq in
/-- **Annihilators of the range are weak solutions of the adjoint equation, in a chart.** Let
`1 < p < ∞`, `q` the conjugate exponent, and `Λ` a continuous functional on the `Lᵖ` `(0,1)`-forms
vanishing on the range of the realization `W^{1,p}(Σ, V) → Lᵖ(Σ, Λ^{0,1} ⊗ V)` of a smooth real
Cauchy–Riemann operator `D`. For every open `Q` with compact closure in the image of chart `i`,
there is an `L^q` covector field `θ` on `Q` with `∫ θ ((∂bar φ + Zᵢ φ)(1)) = 0` for every test
function `φ` on `Q`, where `Zᵢ` is the zeroth-order term of `D` in chart `i`. -/
theorem exists_memLp_forall_integral_eq_zero_of_annihilator (hp : 1 < p) (hp_top : p ≠ ⊤)
    (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ)
    (hΛ : ∀ w, Λ (hD.sobolevL A hDs volume p w) = 0) (i : Fin A.n) {Q : Opens ℂ}
    (hQc : IsCompact (closure (Q : Set ℂ))) (hQi : closure (Q : Set ℂ) ⊆ A.image i) :
    ∃ θ : ℂ → F →L[ℝ] ℝ, MemLp θ q (volume.restrict Q) ∧
      ∀ φ : 𝓓(Q, F), ∫ z, θ z ((complexAntilinearPartL (fderiv ℝ (φ : ℂ → F) z) +
        A.chartZeroOrder D i z ((φ : ℂ → F) z)) 1) = 0 := by
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  obtain ⟨Λ', hΛ'⟩ := exists_extension_zeroOneSobolevSections A Λ
  have hQi' : closure (Q : Set ℂ) ⊆ A.tangentHom.image i := by rwa [A.image_tangentHom]
  have hQ : Q ≤ A.tangentHom.sectionChartData.image i := fun y hy ↦ hQi' (subset_closure hy)
  obtain ⟨ℓ, hℓ⟩ := exists_localization (q := q) A hp hp_top Λ' i hQc hQi' hQ
  obtain ⟨H, hH, -, hHℓ⟩ := MeasureTheory.Lp.exists_memLp_forall_dual_pi_apply_eq (p := q) (q := p)
    (μ := volume.restrict (Q : Set ℂ)) hp hp_top
    (EuclideanSpace.basisFun (Fin (finrank ℝ (ℂ →L[ℝ] F))) ℝ)
    (ℓ : StrongDual ℝ (Fin (finrank ℝ (ℂ →L[ℝ] F)) → Lp ℝ p (volume.restrict (Q : Set ℂ))))
  have hHc (c) : MemLp (fun z ↦ EuclideanSpace.proj (𝕜 := ℝ) c (H z)) q
      (volume.restrict (Q : Set ℂ)) :=
    hH.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) c)
  -- The coefficient field, assembled by a fixed continuous linear map.
  let T : EuclideanSpace ℝ (Fin (finrank ℝ (ℂ →L[ℝ] F))) →L[ℝ] F →L[ℝ] ℝ :=
    ∑ c, (EuclideanSpace.proj (𝕜 := ℝ) c).smulRight (oneComponentL c)
  have hθ : MemLp (fun z ↦ T (H z)) q (volume.restrict (Q : Set ℂ)) :=
    hH.continuousLinearMap_comp T
  refine ⟨_, hθ, fun φ ↦ ?_⟩
  -- The smooth section read as `φ` in chart `i`, and its image under `D`.
  have hφQ : tsupport (φ : ℂ → F) ⊆ A.image i :=
    φ.tsupport_subset.trans fun y hy ↦ hQi (subset_closure hy)
  obtain ⟨ξ, hξ, hξi, hξK⟩ := A.exists_contMDiff_eqOn_coord (i := i) φ.contDiff
    φ.hasCompactSupport hφQ
  let ξ₁ : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯ := ⟨ξ, hξ.of_le (by simp)⟩
  have hw0 := hΛ (SobolevSection.ofContMDiffSection A volume p 1 ξ₁)
  rw [← hΛ'] at hw0
  -- Its chart data vanish off the localized images, so `Λ` only sees chart `i` over `Q`.
  have hvan := value_sobolevL_eq_zero_of_notMem_localizedImage A (p := p) hD hDs
    (fun y hy ↦ hQi' (subset_closure hy)) φ.tsupport_subset ξ₁ hξK
  rw [hℓ _ (Submodule.coe_mem _) hvan, hHℓ] at hw0
  simp only [EuclideanSpace.inner_basisFun_real] at hw0
  have hQimg : (Q : Set ℂ) ⊆ A.image i := fun y hy ↦ hQi (subset_closure hy)
  -- On the chart image, the integrand reads `D ξ` in chart `i`, a complex antilinear map.
  have hT (z : ℂ) (hz : z ∈ A.image i) : T (H z) ((complexAntilinearPartL
      (fderiv ℝ (φ : ℂ → F) z) + A.chartZeroOrder D i z ((φ : ℂ → F) z)) 1) =
        ∑ c, H z c * (finBasis ℝ (ℂ →L[ℝ] F)).repr (A.tangentHom.coord i (D ξ₁) z) c := by
    have hanti := (A.isZeroOneForm_iff_coord_tangentHom i (D ξ₁) hz).1 (hD.isZeroOneForm _ _)
    rw [← coord_tangentHom_eq_of_eqOn A hD hξ hξi hz]
    simp only [T, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply]
    exact Finset.sum_congr rfl fun c _ ↦ congrArg (_ * ·) (oneComponentL_apply_one hanti c)
  -- Off `Q` the test function and its derivative vanish.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (Q : Set ℂ)) fun z hz ↦ by
    have hzφ : z ∉ tsupport (φ : ℂ → F) := fun h ↦ hz (φ.tsupport_subset h)
    simp [fderiv_of_notMem_tsupport ℝ hzφ, image_eq_zero_of_notMem_tsupport hzφ]]
  refine Eq.trans ?_ ((integral_finsetSum _ fun c _ ↦
    (hHc c).integrable_mul (Lp.memLp _)).trans hw0)
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 fun c ↦ (Wkp.value_restrictL_ae hQ 0 _).trans
      (ae_restrict_of_ae_restrict_of_subset hQimg (value_sobolevL_ae A (p := p) hD hDs ξ₁ i c)),
    ae_restrict_mem Q.isOpen.measurableSet] with z hzc hzQ
  refine (hT z (hQimg hzQ)).trans ?_
  simp only [Pi.mul_apply]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [← Wkp.value_zero (Wkp.restrictL hQ 0 _), hzc c]
  rfl

end Annihilator

end TauCeti
