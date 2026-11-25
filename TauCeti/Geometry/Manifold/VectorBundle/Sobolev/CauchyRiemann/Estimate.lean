/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Basic
import TauCeti.Analysis.Complex.Wirtinger.InteriorEstimate
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# The elliptic estimate for smooth real Cauchy–Riemann operators on closed surfaces

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre, smooth as a real vector bundle, with a finite bundle atlas `A` (so
`M` is compact). Let `D` be a smooth real Cauchy–Riemann operator on `V` and `1 < p < ∞`. This
file proves the elliptic estimate

`‖ξ‖_{W^{1,p}} ≤ C (‖D ξ‖_{Lᵖ} + ‖ξ‖_{Lᵖ})`

for every `ξ ∈ W^{1,p}(Σ, V)`, where `D ξ` is the bounded realization
`TauCeti.IsRealCauchyRiemannOperator.sobolevL : W^{1,p}(Σ, V) → L^p(Σ, Λ^{0,1} ⊗ V)` and
`‖ξ‖_{Lᵖ}` is the norm of `ξ` in `W^{0,p}(Σ, V)`
(`TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevL_add_norm`). The `Lᵖ` term
cannot be dropped: a nonzero element of the kernel of `D`, such as a constant function for `∂bar`
on the trivial line bundle, has `D ξ = 0`.

## The argument

Choose a smooth partition of unity `χᵢ` subordinate to the chart domains of `A`, and smooth
cutoffs `ψᵢ` equal to one on the support of `χᵢ` with support inside the domain of chart `i`.
Then `ξ = ∑ᵢ χᵢ ξ`, and `χᵢ ξ = ψᵢ (χᵢ ξ)` is controlled in `W^{1,p}(Σ, V)` by its chart-`i`
components (`TauCeti.SobolevSection.exists_norm_contMDiffSMulL_le`). Each chart-`i` component is
controlled by the `Lᵖ` norms of the chart data and of their weak derivative
(`TauCeti.SectionChartData.norm_le_mul_norm_chartValueL_add_norm_chartDerivL`).

For a smooth section `s`, the reading of `χᵢ s` in chart `i` is `χ' u`, where `u` is the reading
of `s` and `χ'` that of `χᵢ`. The set `K` of points of the chart image where `χ'` can be nonzero
is compact, and the product rule bounds the derivative of `χ' u` by that of `u` on `K` and by
`u` itself (`TauCeti.eLpNorm_fderiv_le_of_eqOn_smul`). In the chart, `D s` reads as
`\bar∂u + Zᵢ u` for a zeroth-order term `Zᵢ` bounded on the chart image, so the interior estimate
for `\bar∂`
(`TauCeti.exists_eLpNorm_fderiv_le_of_norm_sub_complexAntilinearPartL_le`, from
`TauCeti.exists_eLpNorm_fderiv_le_of_norm_sub_conjWirtingerDeriv_le`) bounds the derivative of `u`
on `K` by the readings of `D s` and `s` on the chart image
(`TauCeti.IsRealCauchyRiemannOperator.exists_eLpNorm_coord_smul_add_eLpNorm_fderiv_le`).

Both sides of the estimate are continuous on `W^{1,p}(Σ, V)`, and smooth sections are dense there
for finite `p` (`TauCeti.SobolevSection.dense_ofContMDiffSection_contMDiff`), so the estimate
extends from smooth sections to all of `W^{1,p}(Σ, V)`.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.exists_eLpNorm_coord_smul_add_eLpNorm_fderiv_le`: the
  estimate in one chart, for smooth sections cut off inside the chart domain.
* `TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevL_add_norm`: the elliptic
  estimate on `W^{1,p}(Σ, V)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.2 (the elliptic estimate for real
  Cauchy–Riemann operators on closed surfaces) and Appendix B.4 (the interior Calderón–Zygmund
  estimate for `\bar∂`).
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

section Global

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannEstimate : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace IsRealCauchyRiemannOperator

include hD hDs in
/-- **The elliptic estimate in a chart.** Let `χ` be a smooth function whose support has closure
in the domain of chart `i`. For `1 < p < ∞` there is a constant `C` such that the reading `v` of
`χ s` in chart `i`, for every smooth section `s`, satisfies
`‖v‖_{Lᵖ} + ‖dv‖_{Lᵖ} ≤ C (‖(D s)ᵢ‖_{Lᵖ} + ‖sᵢ‖_{Lᵖ})` on the image of the chart, where `dv` is the
real derivative `fderiv ℝ v`, and `sᵢ` and `(D s)ᵢ` are the readings of `s` and of `D s`. -/
theorem exists_eLpNorm_coord_smul_add_eLpNorm_fderiv_le (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) {i : Fin A.n} {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ)
    (hχi : tsupport χ ⊆ A.dom i) :
    ∃ C : ℝ≥0, ∀ s : Π x, V x,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F x (s x)) →
      eLpNorm (A.coord i fun x ↦ χ x • s x) p (volume.restrict (A.image i)) +
          eLpNorm (fderiv ℝ (A.coord i fun x ↦ χ x • s x)) p (volume.restrict (A.image i)) ≤
        C * (eLpNorm (A.tangentHom.coord i (D s)) p (volume.restrict (A.image i)) +
          eLpNorm (A.coord i s) p (volume.restrict (A.image i))) := by
  have := A.compactSpace
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  set U : Set ℂ := (A.image i : Set ℂ)
  have hU : IsOpen U := (A.image i).isOpen
  have hcl : closure U ⊆ (A.chart i).target := A.closure_image_subset_target i
  set K : Set ℂ := A.chart i '' tsupport χ
  have hK : IsCompact K := (isClosed_tsupport χ).isCompact.image_of_continuousOn
    ((A.chart i).continuousOn.mono (hχi.trans (A.dom_subset_chart_source i)))
  have hKU : K ⊆ U := fun y hy ↦ A.mem_image.2 (image_mono hχi hy)
  set χ' : ℂ → ℝ := fun y ↦ χ ((A.chart i).symm y)
  obtain ⟨B, L, hBL⟩ := A.exists_bound_comp_chart_symm (hχ.of_le (by exact_mod_cast le_top)) i
  obtain ⟨Z, hZ⟩ := A.exists_norm_chartZeroOrder_apply_le hD hDs i
  obtain ⟨C₀, hC₀⟩ := exists_eLpNorm_fderiv_le_of_norm_sub_complexAntilinearPartL_le (F := F) hp
    hp_top hU hK hKU Z.toNNReal
  refine ⟨B * C₀ + L + B, fun s hs ↦ ?_⟩
  set u := A.coord i s
  have hu : ContDiffOn ℝ ∞ u U :=
    ((contDiffOn_trivialization_comp_chart_symm_of_contMDiff hs
      (IsManifold.chart_mem_maximalAtlas _) (A.triv i)).congr fun y _ ↦ A.coord_def i s y).mono
        ((A.image_subset_chart_image_closure_dom i).trans (A.chart_image_closure_dom_subset i))
  -- In chart `i`, `D s` is `\bar∂ u + Zᵢ u`.
  have hDs' := hC₀ u (A.tangentHom.coord i (D s)) hu fun z hz ↦ by
    rw [A.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder hD hz
      ((hs _).mdifferentiableAt (by simp)), add_sub_cancel_left]
    exact (hZ z (subset_closure hz) _).trans (by gcongr; exact Real.le_coe_toNNReal Z)
  -- The reading of `χ s` is `χ' u` on the chart image, and `χ'` vanishes off `K`.
  have hχK : ∀ z ∈ U, z ∉ K → χ' z = 0 := fun z hz hzK ↦ by
    by_contra h
    exact hzK ⟨_, subset_tsupport _ h, (A.chart i).right_inv (hcl (subset_closure hz))⟩
  have hvU : EqOn (A.coord i fun x ↦ χ x • s x) (fun y ↦ χ' y • u y) U :=
    fun y hy ↦ A.coord_fun_smul i χ s hy
  have hχ'U : DifferentiableOn ℝ χ' U :=
    ((A.contDiffOn_comp_chart_symm hχ i).mono (subset_closure.trans hcl)).differentiableOn (by simp)
  set G := eLpNorm (A.tangentHom.coord i (D s)) p (volume.restrict U)
  set Y := eLpNorm u p (volume.restrict U)
  have h₁ : eLpNorm (A.coord i fun x ↦ χ x • s x) p (volume.restrict U) ≤ B * Y := by
    rw [eLpNorm_congr_ae ((ae_restrict_mem hU.measurableSet).mono fun y hy ↦ hvU hy)]
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((hχ'U.continuousOn.smul hu.continuousOn
      ).aestronglyMeasurable hU.measurableSet) ?_ p).trans_eq (by rw [ENNReal.ofReal_coe_nnreal])
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    simpa [norm_smul] using mul_le_mul_of_nonneg_right (hBL z hz).1 (norm_nonneg (u z))
  have h₂ := eLpNorm_fderiv_le_of_eqOn_smul (μ := volume) (Fact.out : 1 ≤ p) hU hK.measurableSet
    hKU hχ'U (hu.differentiableOn (by simp)) hvU (fun z hz ↦ (hBL z hz).1) (fun z hz ↦ (hBL z hz).2)
    hχK
  calc _ ≤ B * Y + (B * (C₀ * (G + Y)) + L * Y) := add_le_add h₁ (h₂.trans (by gcongr))
    _ ≤ B * (G + Y) + (B * (C₀ * (G + Y)) + L * (G + Y)) := by gcongr <;> exact le_add_self
    _ = ((B * C₀ + L + B : ℝ≥0) : ℝ≥0∞) * (G + Y) := by
        push_cast
        ring

include hD hDs in
/-- The chart estimate
`TauCeti.IsRealCauchyRiemannOperator.exists_eLpNorm_coord_smul_add_eLpNorm_fderiv_le` in terms of
the chart data of the Sobolev sections of a `C¹` section `s` and of `χ s`. -/
private theorem norm_chartValueL_add_norm_chartDerivL_le (s : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯) {i : Fin A.n}
    {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ) {c : ℝ≥0}
    (h : eLpNorm (A.coord i fun x ↦ χ x • s x) p (volume.restrict (A.image i)) +
        eLpNorm (fderiv ℝ (A.coord i fun x ↦ χ x • s x)) p (volume.restrict (A.image i)) ≤
      c * (eLpNorm (A.tangentHom.coord i (D s)) p (volume.restrict (A.image i)) +
        eLpNorm (A.coord i s) p (volume.restrict (A.image i)))) :
    ‖A.sectionChartData.chartValueL volume p 1 i (SobolevSection.contMDiffSMulL A volume p 1 hχ
        (SobolevSection.ofContMDiffSection A volume p 1 s))‖ +
      ‖A.sectionChartData.chartDerivL volume p i (SobolevSection.contMDiffSMulL A volume p 1 hχ
        (SobolevSection.ofContMDiffSection A volume p 1 s))‖ ≤
      c * (‖A.tangentHom.sectionChartData.chartValueL volume p 0 i
          (hD.sobolevL A hDs volume p (SobolevSection.ofContMDiffSection A volume p 1 s) :
            SobolevSection A.tangentHom volume p 0)‖ +
        ‖A.sectionChartData.chartValueL volume p 0 i (A.sectionChartData.lowerOrderL volume p 0
          (SobolevSection.ofContMDiffSection A volume p 1 s))‖) := by
  set w := SobolevSection.ofContMDiffSection A volume p 1 s
  set v := SobolevSection.contMDiffSMulL A volume p 1 hχ w
  have hv := SobolevSection.chartValueL_contMDiffSMulL_ae_coord hχ
    (SobolevSection.chartValueL_ofContMDiffSection_ae A volume p 1 s) i
  have hc : ContDiffOn ℝ 1 (A.coord i fun x ↦ χ x • s x) (A.image i) :=
    (A.contDiffOn_coord ((hχ.of_le (by exact_mod_cast le_top)).smul_section s.contMDiff) i).mono
      ((A.image_subset_chart_image_closure_dom i).trans (A.chart_image_closure_dom_subset i))
  have hd := (A.sectionChartData.hasWeakFDerivOn_chartValueL volume p i v).ae_eq
    ((hc.hasWeakFDerivOn_fderiv (μ := volume) (Ω := A.image i)).congr_ae hv.symm)
  have hu := SobolevSection.chartValueL_ofContMDiffSection_ae A volume p 1 s i
  rw [← A.sectionChartData.chartValueL_coe_lowerOrderL volume p 0 w i] at hu
  have e₁ : eLpNorm (A.sectionChartData.chartValueL volume p 1 i v) p
      (volume.restrict (A.image i)) =
        eLpNorm (A.coord i fun x ↦ χ x • s x) p (volume.restrict (A.image i)) :=
    eLpNorm_congr_ae hv
  have e₂ : eLpNorm (A.sectionChartData.chartDerivL volume p i v) p
      (volume.restrict (A.image i)) =
        eLpNorm (fderiv ℝ (A.coord i fun x ↦ χ x • s x)) p (volume.restrict (A.image i)) :=
    eLpNorm_congr_ae hd
  have e₃ : eLpNorm (A.tangentHom.sectionChartData.chartValueL volume p 0 i
      (hD.sobolevL A hDs volume p w : SobolevSection A.tangentHom volume p 0)) p
      (volume.restrict (A.tangentHom.sectionChartData.image i : Set ℂ)) =
        eLpNorm (A.tangentHom.coord i (D s)) p (volume.restrict (A.image i)) := by
    rw [eLpNorm_congr_ae ((ae_image_tangentHom_iff A volume i).2
      (hD.chartValueL_sobolevL_ofContMDiffSection_ae A hDs volume p s i)),
      sectionChartData_image_tangentHom]
  have hCs := (congrArg₂ (· + ·) e₁ e₂).trans_le (h.trans_eq
    (congrArg₂ (fun a b ↦ (c : ℝ≥0∞) * (a + b)) e₃ (eLpNorm_congr_ae hu)).symm)
  simp only [Lp.norm_def]
  rw [← ENNReal.toReal_add (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _),
    ← ENNReal.toReal_add (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _), ← ENNReal.coe_toReal,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.add_ne_top.2 ⟨Lp.eLpNorm_ne_top _, Lp.eLpNorm_ne_top _⟩)) hCs

include hD hDs in
/-- **The chart estimate in Sobolev norms, for smooth sections.** For a smooth `χ` whose support
has closure in the domain of chart `i`, the chart-`i` components of `χ w`, for the Sobolev section
`w` of a smooth section, are bounded in `W^{1,p}` by a multiple of
`‖D w‖_{Lᵖ} + ‖w‖_{Lᵖ}`. -/
private theorem exists_norm_contMDiffSMulL_component_le (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {i : Fin A.n} {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ) (hχi : tsupport χ ⊆ A.dom i) :
    ∃ C : ℝ, ∀ s : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F x (s x)) →
      ‖(SobolevSection.contMDiffSMulL A volume p 1 hχ
          (SobolevSection.ofContMDiffSection A volume p 1 s) :
            A.sectionChartData.SobolevData volume p 1) i‖ ≤
        C * (‖hD.sobolevL A hDs volume p (SobolevSection.ofContMDiffSection A volume p 1 s)‖ +
          ‖A.sectionChartData.lowerOrderL volume p 0
            (SobolevSection.ofContMDiffSection A volume p 1 s)‖) := by
  obtain ⟨Cc, hCc⟩ := hD.exists_eLpNorm_coord_smul_add_eLpNorm_fderiv_le A hDs hp hp_top hχ hχi
  set cB : ℝ := ∑ j, ‖LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)‖
  set T := A.tangentHom.sectionChartData.chartValueL volume p 0 i
  set S := A.sectionChartData.chartValueL volume p 0 i
  refine ⟨cB * (Cc * (‖T‖ + ‖S‖)), fun s hs ↦ ?_⟩
  set w := SobolevSection.ofContMDiffSection A volume p 1 s
  set v := SobolevSection.contMDiffSMulL A volume p 1 hχ w
  have hchart := norm_chartValueL_add_norm_chartDerivL_le A hD hDs s hχ (hCc s hs)
  set X := ‖hD.sobolevL A hDs volume p w‖
  set Y := ‖A.sectionChartData.lowerOrderL volume p 0 w‖
  have hT : ‖T (hD.sobolevL A hDs volume p w : SobolevSection A.tangentHom volume p 0)‖ ≤
      ‖T‖ * X := T.le_opNorm _
  have hS : ‖S (A.sectionChartData.lowerOrderL volume p 0 w)‖ ≤ ‖S‖ * Y := S.le_opNorm _
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by positivity
  calc ‖(v : A.sectionChartData.SobolevData volume p 1) i‖
      ≤ cB * (‖A.sectionChartData.chartValueL volume p 1 i v‖ +
          ‖A.sectionChartData.chartDerivL volume p i v‖) := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j ↦
          (A.sectionChartData.norm_le_mul_norm_chartValueL_add_norm_chartDerivL volume p i v
            j).trans ?_
        gcongr
        exact Finset.single_le_sum (f := fun j ↦
          ‖LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)‖)
          (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j)
    _ ≤ cB * (Cc * ((‖T‖ + ‖S‖) * (X + Y))) := by
        gcongr
        refine hchart.trans ?_
        gcongr
        nlinarith [norm_nonneg T, norm_nonneg S]
    _ = cB * (Cc * (‖T‖ + ‖S‖)) * (X + Y) := by ring

include hD hDs in
/-- **The elliptic estimate for a smooth real Cauchy–Riemann operator on a closed surface.** Let
`D` be a smooth real Cauchy–Riemann operator on a complex vector bundle `V` over a compact
boundaryless complex curve, with a finite bundle atlas `A`, and let `1 < p < ∞`. There is a
constant `C` such that every `ξ ∈ W^{1,p}(Σ, V)` satisfies
`‖ξ‖_{W^{1,p}} ≤ C (‖D ξ‖_{Lᵖ} + ‖ξ‖_{Lᵖ})`, where `D ξ` is the realization
`TauCeti.IsRealCauchyRiemannOperator.sobolevL` and `‖ξ‖_{Lᵖ}` is the norm of `ξ` in
`W^{0,p}(Σ, V)`. -/
theorem exists_norm_le_norm_sobolevL_add_norm (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ, ∀ w : SobolevSection A volume p 1,
      ‖w‖ ≤ C * (‖hD.sobolevL A hDs volume p w‖ +
        ‖A.sectionChartData.lowerOrderL volume p 0 w‖) := by
  have := A.compactSpace
  -- A partition of unity subordinate to the chart domains, and cutoffs equal to one on its
  -- supports.
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ A.dom
    A.isOpen_dom (by rw [A.iUnion_dom])
  have hχ1 (x : M) : ∑ i, χ i x = 1 := by
    simpa [finsum_eq_sum_of_fintype] using χ.sum_eq_one (mem_univ x)
  choose ψ hψ _ hψi hψ1 using fun i ↦
    (isClosed_tsupport (χ i)).exists_contMDiff_tsupport_subset_eq_one_iff (I := 𝓘(ℝ, ℂ))
      (A.isOpen_dom i) (hχ i)
  choose Cψ hCψ using fun i ↦
    SobolevSection.exists_norm_contMDiffSMulL_le (μ := volume) (p := p) (k := 1) (hψ i) (hψi i)
  choose Cc hCc using fun i ↦
    exists_norm_contMDiffSMulL_component_le A hD hDs hp hp_top (χ i).contMDiff (hχ i)
  set C := ∑ i, max (Cψ i) 0 * max (Cc i) 0
  refine ⟨C, fun w ↦ ?_⟩
  -- The estimate is a closed condition, so it suffices to prove it on the dense set of smooth
  -- sections.
  have hc₁ : Continuous fun w : SobolevSection A volume p 1 ↦ ‖hD.sobolevL A hDs volume p w‖ :=
    (continuous_norm (E := zeroOneSobolevSections A volume p 0)).comp
      (hD.sobolevL A hDs volume p).continuous
  have hc₂ : Continuous fun w : SobolevSection A volume p 1 ↦
      ‖A.sectionChartData.lowerOrderL volume p 0 w‖ :=
    continuous_norm.comp (A.sectionChartData.lowerOrderL volume p 0).continuous
  have hP : IsClosed {w : SobolevSection A volume p 1 | ‖w‖ ≤ C *
      (‖hD.sobolevL A hDs volume p w‖ + ‖A.sectionChartData.lowerOrderL volume p 0 w‖)} :=
    isClosed_le continuous_norm (continuous_const.mul (hc₁.add hc₂))
  have hdense := SobolevSection.dense_ofContMDiffSection_contMDiff (A := A) (μ := volume)
    (p := p) (k := 1) hp_top
  refine hP.closure_subset_iff.2 ?_ (hdense.closure_eq ▸ mem_univ w)
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_ofPred_eq]
  set w := SobolevSection.ofContMDiffSection A volume p 1 s
  set X := ‖hD.sobolevL A hDs volume p w‖ + ‖A.sectionChartData.lowerOrderL volume p 0 w‖
  calc ‖w‖ = ‖∑ i, SobolevSection.contMDiffSMulL A volume p 1 (χ i).contMDiff w‖ := by
        rw [SobolevSection.sum_contMDiffSMulL_eq_self_of_sum_eq_one _ hχ1]
    _ ≤ ∑ i, ‖SobolevSection.contMDiffSMulL A volume p 1 (χ i).contMDiff w‖ := norm_sum_le _ _
    _ ≤ ∑ i, max (Cψ i) 0 * max (Cc i) 0 * X := Finset.sum_le_sum fun i _ ↦ ?_
    _ = C * X := by rw [Finset.sum_mul]
  set v := SobolevSection.contMDiffSMulL A volume p 1 (χ i).contMDiff w
  have hvi := hCc i s hs
  calc ‖v‖ = ‖SobolevSection.contMDiffSMulL A volume p 1 (hψ i) v‖ := by
        rw [SobolevSection.contMDiffSMulL_contMDiffSMulL_of_eqOn _ (hψ i) fun _ h ↦ (hψ1 i _).1 h]
    _ ≤ Cψ i * ‖(v : A.sectionChartData.SobolevData volume p 1) i‖ := hCψ i v
    _ ≤ max (Cψ i) 0 * ‖(v : A.sectionChartData.SobolevData volume p 1) i‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max (Cψ i) 0 * (max (Cc i) 0 * X) := by
        gcongr
        exact hvi.trans (by gcongr; exact le_max_left _ _)
    _ = max (Cψ i) 0 * max (Cc i) 0 * X := by ring

end IsRealCauchyRiemannOperator

end Global

end TauCeti
