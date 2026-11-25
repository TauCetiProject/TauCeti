/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Basic
public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.AEZeroOff
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.ChartSection
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Transfer
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
`D`.

Every continuous functional `Λ` on the `Lᵖ` `(0,1)`-forms is, over every open `Q` with closure in
the image of chart `i`, integration against an `L^q` covector field `θ`, `q` the conjugate
exponent: `Λ w = ∫_Q θ (wᵢ(1))` for every `w` vanishing off the points of `Q`, where `wᵢ` is the
chart-`i` reading of `w` (`TauCeti.exists_memLp_forall_eq_setIntegral_of_mem_aeZeroOff`). A
`(0,1)`-form is complex antilinear, so it is determined by its value on `1`, and `θ` pairs with
that value. If `Λ` vanishes on the range of `D`, then `θ` is a weak solution of the adjoint
equation: `∫ θ ((∂bar φ + Zᵢ φ)(1)) = 0` for every test function `φ` on `Q`, where `Zᵢ` is the
zeroth-order term of `D` in chart `i`
(`TauCeti.exists_memLp_forall_integral_eq_zero_of_annihilator`).
This is the hypothesis of the planar regularity theorem for annihilators of real Cauchy–Riemann
operators (`TauCeti.memWkpLoc_succ_of_forall_integral_apply_cauchyRiemann_eq_zero`, for `J = i`
and `S = 2 Zᵢ(·)(1)`), which makes `θ` smooth.

The proof extends `Λ` by Hahn–Banach to all chart data of one-forms
(`TauCeti.exists_extension_zeroOneSobolevSections`) and represents the block of every chart `j` by
`L^q` coefficients (the duality `MeasureTheory.Lp.exists_memLp_forall_dual_pi_apply_eq`). A
one-form supported over `Q` has chart-`j` data supported in the part of chart `j` that sees `Q`
(`TauCeti.FiniteBundleAtlas.localizedImage`), where they are the transfer of its chart-`i` data
(`TauCeti.FiniteBundleAtlas.restrictL_eq_transferL`). So `Λ` restricted to such forms is a
continuous functional of the chart-`i` data over `Q`, again represented by `L^q` coefficients. A
test function `φ` on `Q` is the reading of a smooth section `ξ`
(`TauCeti.FiniteBundleAtlas.exists_contMDiff_eqOn_coord`), and `Λ (D ξ) = 0` is the weak equation.

## Main results

* `TauCeti.exists_extension_zeroOneSobolevSections`: functionals on `Lᵖ` `(0,1)`-forms extend to
  all chart data of one-forms.
* `TauCeti.exists_memLp_forall_eq_setIntegral_of_mem_aeZeroOff`: a continuous functional on the
  `Lᵖ` `(0,1)`-forms is, over a relatively compact open set of a chart image, integration against
  an `L^q` covector field.
* `TauCeti.exists_memLp_forall_integral_eq_zero_of_annihilator`: for an annihilator of the range
  of `D`, that covector field is a weak solution of the adjoint equation.

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
/-- **Localizing a functional to one chart.** Let `Q` be open with closure in the image of chart
`i`, and `1 < p < ∞`. For a continuous functional `Λ'` on the chart data of one-forms, there is a
continuous functional `ℓ` on chart-`i` data over `Q` with `Λ' w = ℓ (w_i|_Q)` for every `Lᵖ`
one-form `w` whose chart-`j` data vanish off the localized image, for every chart `j`. -/
private theorem exists_localization (hp : 1 < p) (hp_top : p ≠ ⊤)
    (Λ' : A.tangentHom.sectionChartData.SobolevData volume p 0 →L[ℝ] ℝ)
    (i : Fin A.tangentHom.sectionChartData.n) {Q : Opens ℂ}
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
      P j ≤ A.tangentHom.sectionChartData.image j :=
    A.tangentHom.localizedImage_le_image i j Q
  have hPc (j : Fin A.tangentHom.sectionChartData.n) :=
    A.tangentHom.isCompact_closure_localizedImage i j Q
  have hPD (j : Fin A.tangentHom.sectionChartData.n) :=
    A.tangentHom.closure_localizedImage_subset_transferDomain (j := j) hQi
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
  -- `transferL` is valued in `Wkp _ _ p 0`, which the composite with `Lp.toDual` reads as `Lp`
  -- (`Wkp _ _ p 0` is `Lp` by definition, see `Wkp.value_zero`), so the occurrence is behind
  -- that identification and `erw` is needed to see it.
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
  conv_rhs => rw [L.eq_reCLM_smulRight_sub_imCLM_smulRight_of_antilinear hL]
  simp [oneComponentL]

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The chart data of a one-form vanishing off the points read in chart `i` inside `Q` vanish, in
every chart `j`, off the localized image. -/
private theorem value_eq_zero_of_mem_aeZeroOff {i : Fin A.n} {Q : Opens ℂ}
    (hQi : (Q : Set ℂ) ⊆ A.tangentHom.image i) {w : SobolevSection A.tangentHom volume p 0}
    (hw : w ∈ SobolevSection.aeZeroOff A.tangentHom volume p 0 ((A.chart i).symm '' Q))
    (j : Fin A.tangentHom.sectionChartData.n) (c : Fin (finrank ℝ (ℂ →L[ℝ] F))) :
    ∀ᵐ y ∂volume.restrict (A.tangentHom.sectionChartData.image j : Set ℂ),
      y ∉ A.tangentHom.localizedImage i j Q →
        Wkp.value 0 ((w : A.tangentHom.sectionChartData.SobolevData volume p 0) j c) y = 0 := by
  filter_upwards [SobolevSection.mem_aeZeroOff.1 hw j,
    A.tangentHom.sectionChartData.chartValueL_apply_ae volume p 0 j w,
    ae_restrict_mem (A.tangentHom.sectionChartData.image j).isOpen.measurableSet]
    with y hy hsum hyj hyP
  have h0 := hy (symm_notMem_image_of_notMem_localizedImage subset_rfl hQi hyj hyP)
  rw [hsum] at h0
  simpa [Finsupp.single_apply] using congrArg (fun v ↦ (finBasis ℝ (ℂ →L[ℝ] F)).repr v c) h0

include hq₁ hpq in
/-- **Local representation of functionals on `(0,1)`-forms.** Let `1 < p < ∞`, `q` the conjugate
exponent, and `Λ` a continuous functional on the `Lᵖ` `(0,1)`-forms. For every open `Q` with
closure in the image of chart `i`, there is an `L^q` covector field `θ` on `Q` with
`Λ w = ∫_Q θ (wᵢ(1))` for every `(0,1)`-form `w` vanishing almost everywhere off the points of `M`
read in chart `i` inside `Q`, where `wᵢ` is the chart-`i` reading of `w`. -/
theorem exists_memLp_forall_eq_setIntegral_of_mem_aeZeroOff (hp : 1 < p) (hp_top : p ≠ ⊤)
    (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ) (i : Fin A.n) {Q : Opens ℂ}
    (hQi : closure (Q : Set ℂ) ⊆ A.image i) :
    ∃ θ : ℂ → F →L[ℝ] ℝ, MemLp θ q (volume.restrict Q) ∧
      ∀ w : zeroOneSobolevSections A volume p 0,
        (w : SobolevSection A.tangentHom volume p 0) ∈
            SobolevSection.aeZeroOff A.tangentHom volume p 0 ((A.chart i).symm '' Q) →
          Λ w = ∫ z in Q, θ z (A.tangentHom.sectionChartData.chartValueL volume p 0 i
            ((w : SobolevSection A.tangentHom volume p 0) :
              A.tangentHom.sectionChartData.SobolevData volume p 0) z 1) := by
  obtain ⟨Λ', hΛ'⟩ := exists_extension_zeroOneSobolevSections A Λ
  have hQi' : closure (Q : Set ℂ) ⊆ A.tangentHom.image i := by rwa [A.image_tangentHom]
  have hQ : Q ≤ A.tangentHom.sectionChartData.image i := fun y hy ↦ hQi' (subset_closure hy)
  obtain ⟨ℓ, hℓ⟩ := exists_localization (q := q) A hp hp_top Λ' i hQi' hQ
  obtain ⟨H, hH, -, hHℓ⟩ := MeasureTheory.Lp.exists_memLp_forall_dual_pi_apply_eq (p := q) (q := p)
    (μ := volume.restrict (Q : Set ℂ)) hp hp_top
    (EuclideanSpace.basisFun (Fin (finrank ℝ (ℂ →L[ℝ] F))) ℝ)
    (ℓ : StrongDual ℝ (Fin (finrank ℝ (ℂ →L[ℝ] F)) → Lp ℝ p (volume.restrict (Q : Set ℂ))))
  -- The `c`-th coefficient `z ↦ H z c` is `EuclideanSpace.proj c ∘ H`.
  have hHc (c) : MemLp (fun z ↦ H z c) q (volume.restrict (Q : Set ℂ)) :=
    hH.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) c)
  -- The coefficient field, assembled by a fixed continuous linear map.
  let T : EuclideanSpace ℝ (Fin (finrank ℝ (ℂ →L[ℝ] F))) →L[ℝ] F →L[ℝ] ℝ :=
    ∑ c, (EuclideanSpace.proj (𝕜 := ℝ) c).smulRight (oneComponentL c)
  refine ⟨fun z ↦ T (H z), hH.continuousLinearMap_comp T, fun w hw ↦ ?_⟩
  -- `Λ w` only sees the chart-`i` data of `w` over `Q`, represented by `H`.
  rw [← hΛ', hℓ _ (Submodule.coe_mem _) (value_eq_zero_of_mem_aeZeroOff A
    (fun y hy ↦ hQi' (subset_closure hy)) hw), hHℓ]
  simp only [EuclideanSpace.inner_basisFun_real]
  refine (integral_finsetSum _ fun c _ ↦ (hHc c).integrable_mul (Lp.memLp _)).symm.trans
    (integral_congr_ae ?_)
  -- Almost everywhere on `Q`, the chart-`i` data of `w` are complex antilinear, with components
  -- the values of its chart-`i` entries.
  have hQs : (Q : Set ℂ) ⊆ A.tangentHom.sectionChartData.image i := hQ
  filter_upwards [ae_all_iff.2 fun c ↦ Wkp.value_restrictL_ae hQ 0
      (((w : SobolevSection A.tangentHom volume p 0) :
        A.tangentHom.sectionChartData.SobolevData volume p 0) i c),
    ae_restrict_of_ae_restrict_of_subset hQs (mem_zeroOneSobolevSections_iff.1 w.prop i),
    ae_restrict_of_ae_restrict_of_subset hQs
      (A.tangentHom.sectionChartData.chartValueL_apply_ae volume p 0 i
        ((w : SobolevSection A.tangentHom volume p 0) :
          A.tangentHom.sectionChartData.SobolevData volume p 0))] with z hzc hza hzs
  simp only [T, Pi.mul_apply, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul,
    PiLp.proj_apply]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [oneComponentL_apply_one hza c, hzs, ← Wkp.value_zero (Wkp.restrictL hQ 0 _), hzc c]
  simp [Finsupp.single_apply]

variable {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)

include hD hDs in
/-- The chart data of the realization of a smooth section `ξ` are, in chart `j`, the reading of
`D ξ`. -/
private theorem chartValueL_sobolevL_ae (ξ : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯) (j : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL volume p 0 j
      ((hD.sobolevL A hDs volume p (SobolevSection.ofContMDiffSection A volume p 1 ξ) :
        SobolevSection A.tangentHom volume p 0) :
          A.tangentHom.sectionChartData.SobolevData volume p 0)
      =ᵐ[volume.restrict (A.tangentHom.sectionChartData.image j)]
        A.tangentHom.coord j (D ξ) :=
  (ae_image_tangentHom_iff A volume j).2
    (IsRealCauchyRiemannOperator.chartValueL_sobolevL_ofContMDiffSection_ae A hD hDs volume p ξ j)

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

include hD hDs hq₁ hpq in
/-- **Annihilators of the range are weak solutions of the adjoint equation, in a chart.** Let
`1 < p < ∞`, `q` the conjugate exponent, and `Λ` a continuous functional on the `Lᵖ` `(0,1)`-forms
vanishing on the range of the realization `W^{1,p}(Σ, V) → Lᵖ(Σ, Λ^{0,1} ⊗ V)` of a smooth real
Cauchy–Riemann operator `D`. Let `Q` be open with closure in the image of chart `i`. Then the
`L^q` covector field `θ` on `Q` representing `Λ` over `Q`, `Λ w = ∫_Q θ (wᵢ(1))` for every
`(0,1)`-form `w` vanishing off the points read in chart `i` inside `Q`, satisfies
`∫ θ ((∂bar φ + Zᵢ φ)(1)) = 0` for every test function `φ` on `Q`, where `Zᵢ` is the zeroth-order
term of `D` in chart `i`. -/
theorem exists_memLp_forall_integral_eq_zero_of_annihilator (hp : 1 < p) (hp_top : p ≠ ⊤)
    (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ)
    (hΛ : ∀ w, Λ (hD.sobolevL A hDs volume p w) = 0) (i : Fin A.n) {Q : Opens ℂ}
    (hQi : closure (Q : Set ℂ) ⊆ A.image i) :
    ∃ θ : ℂ → F →L[ℝ] ℝ, MemLp θ q (volume.restrict Q) ∧
      (∀ w : zeroOneSobolevSections A volume p 0,
        (w : SobolevSection A.tangentHom volume p 0) ∈
            SobolevSection.aeZeroOff A.tangentHom volume p 0 ((A.chart i).symm '' Q) →
          Λ w = ∫ z in Q, θ z (A.tangentHom.sectionChartData.chartValueL volume p 0 i
            ((w : SobolevSection A.tangentHom volume p 0) :
              A.tangentHom.sectionChartData.SobolevData volume p 0) z 1)) ∧
      ∀ φ : 𝓓(Q, F), ∫ z, θ z ((complexAntilinearPartL (fderiv ℝ (φ : ℂ → F) z) +
        A.chartZeroOrder D i z ((φ : ℂ → F) z)) 1) = 0 := by
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  obtain ⟨θ, hθ, hrep⟩ :=
    exists_memLp_forall_eq_setIntegral_of_mem_aeZeroOff (q := q) A hp hp_top Λ i hQi
  refine ⟨θ, hθ, hrep, fun φ ↦ ?_⟩
  -- The smooth section read as `φ` in chart `i`.
  have hQimg : (Q : Set ℂ) ⊆ A.image i := fun y hy ↦ hQi (subset_closure hy)
  have hQs : (Q : Set ℂ) ⊆ A.tangentHom.sectionChartData.image i := by
    have h : (Q : Set ℂ) ⊆ A.tangentHom.image i := by rw [A.image_tangentHom]; exact hQimg
    exact h
  obtain ⟨ξ, hξ, hξi, hξK⟩ := A.exists_contMDiff_eqOn_coord (i := i) φ.contDiff
    φ.hasCompactSupport (φ.tsupport_subset.trans hQimg)
  let ξ₁ : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯ := ⟨ξ, hξ.of_le (by simp)⟩
  -- `D ξ` vanishes off the points of `Q`, so `Λ (D ξ)` is the integral of `θ` against its reading.
  have hmem : (hD.sobolevL A hDs volume p (SobolevSection.ofContMDiffSection A volume p 1 ξ₁) :
      SobolevSection A.tangentHom volume p 0) ∈
        SobolevSection.aeZeroOff A.tangentHom volume p 0 ((A.chart i).symm '' Q) :=
    SobolevSection.mem_aeZeroOff_of_ae_eq_coord (fun j ↦ chartValueL_sobolevL_ae A hD hDs ξ₁ j)
      fun x hx ↦ hD.apply_eq_zero_of_notMem_closure fun h ↦
        hx (image_mono φ.tsupport_subset (hξK h))
  have hw0 := hΛ (SobolevSection.ofContMDiffSection A volume p 1 ξ₁)
  rw [hrep _ hmem] at hw0
  -- Off `Q` the test function and its derivative vanish.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (Q : Set ℂ)) fun z hz ↦ by
    have hzφ : z ∉ tsupport (φ : ℂ → F) := fun h ↦ hz (φ.tsupport_subset h)
    simp [fderiv_of_notMem_tsupport ℝ hzφ, image_eq_zero_of_notMem_tsupport hzφ]]
  -- On `Q`, the reading of `D ξ` in chart `i` is `∂bar φ + Zᵢ φ`.
  refine Eq.trans (integral_congr_ae ?_) hw0
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hQs
      (chartValueL_sobolevL_ae A (p := p) hD hDs ξ₁ i),
    ae_restrict_mem Q.isOpen.measurableSet] with z hz hzQ
  rw [hz, coord_tangentHom_eq_of_eqOn A hD (ξ := ξ₁) hξ hξi (hQimg hzQ)]

end Annihilator

end TauCeti
