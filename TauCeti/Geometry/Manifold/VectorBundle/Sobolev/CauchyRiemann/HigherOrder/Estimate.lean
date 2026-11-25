/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.HigherOrder.Basic
public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Complex.Wirtinger.Regularity.ZerothOrder
import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound.ContDiff
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density
import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Chart
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# The higher-order elliptic estimate for smooth real Cauchy–Riemann operators

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre, smooth as a real vector bundle, with a finite bundle atlas `A` (so
`M` is compact). Let `D` be a smooth real Cauchy–Riemann operator on `V` and `1 < p < ∞`. This
file proves the elliptic estimate at every order `k`:

`‖ξ‖_{W^{k+1,p}} ≤ C (‖D ξ‖_{W^{k,p}} + ‖ξ‖_{Lᵖ})`

for every `ξ ∈ W^{k+1,p}(Σ, V)`, where `D ξ` is the bounded realization
`TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL : W^{k+1,p}(Σ, V) → W^{k,p}(Σ, Λ^{0,1} ⊗ V)`
and `‖ξ‖_{Lᵖ}` is the norm of `ξ` with all derivatives forgotten
(`TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevSuccL_add_norm`). Its case
`k = 0` gives `TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevL_add_norm`.

## The argument

The estimate one order up, `‖ξ‖_{W^{k+1,p}} ≤ C (‖D ξ‖_{W^{k,p}} + ‖ξ‖_{W^{k,p}})`
(`TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevSuccL_add_norm_lowerOrderL`),
is proved by localization. A partition of unity `χᵢ` subordinate to the chart domains splits a
smooth section `s`, and `χᵢ s` is controlled by its chart-`i` components. In chart `i` the reading
`u` of `s` satisfies `g = ∂bar u + Zᵢ u` for the reading `g` of `D s` and the zeroth-order term
`Zᵢ`. The interior estimate for `∂bar`
(`TauCeti.exists_eLpNormWkp_le_of_hasWeakConjWirtingerDerivOn`) bounds `u` in `W^{k+1,p}` near
the support of the cutoff by `∂bar u` in `W^{k,p}` and `u` in `Lᵖ`.
With the zeroth-order term this becomes a bound by `‖g‖_{W^{k,p}} + ‖u‖_{W^{k,p}}`
(`TauCeti.exists_eLpNormWkp_le_of_eqOn_complexAntilinearPartL_add`,
`TauCeti.IsRealCauchyRiemannOperator.exists_eLpNormWkp_coord_smul_le`). The Leibniz bound
`TauCeti.eLpNormWkp_bilin_le` handles the cutoff. For smooth readings the `W^{k,p}` norms of
functions and the norms of chart components are comparable
(`TauCeti.SectionChartData.exists_eLpNormWkp_le_of_chartValueL_ae_eq`,
`TauCeti.SectionChartData.exists_ofReal_norm_le_eLpNormWkp_of_chartValueL_ae_eq`). Smooth
sections are dense, and both sides are continuous, so the estimate extends to all of
`W^{k+1,p}(Σ, V)`. Induction on `k`, with the compatibility of the realizations with forgetting
derivatives (`TauCeti.IsRealCauchyRiemannOperator.zeroOneLowerOrdersL_sobolevSuccL`), lowers the
`W^{k,p}` norm of `ξ` on the right to its `Lᵖ` norm.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.exists_eLpNormWkp_coord_smul_le`: the estimate in one chart,
  for smooth sections cut off inside the chart domain.
* `TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevSuccL_add_norm_lowerOrderL`: the
  estimate one order up.
* `TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevSuccL_add_norm`: the elliptic
  estimate on `W^{k+1,p}(Σ, V)` at every order.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.2 (the elliptic estimate for real
  Cauchy–Riemann operators) and Appendix B.4 (the interior estimates for `∂bar`).
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

/-! ### The estimate in one chart -/

section Global

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannHigherOrderEstimate : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace IsRealCauchyRiemannOperator

omit [T2Space M] in
include hD in
/-- The chart formula for `D` on a smooth section `s`: on the image of chart `i`, the reading of
`D s` is `∂bar u + Zᵢ u` for the reading `u` of `s`. -/
private theorem coord_tangentHom_eq (i : Fin A.n) {s : Π x, V x}
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F x (s x)))
    {z : ℂ} (hz : z ∈ A.image i) :
    A.tangentHom.coord i (D s) z = complexAntilinearPartL (fderiv ℝ (A.coord i s) z) +
      A.chartZeroOrder D i z (A.coord i s z) :=
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  A.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder hD hz
    ((hs _).mdifferentiableAt (by simp))

include hD hDs in
/-- For a smooth section `s`, the reading of `D s` in chart `i` is `Cᵏ` on the image of the chart:
it is `∂bar u + Zᵢ u` for the smooth reading `u` of `s`. -/
private theorem contDiffOn_coord_tangentHom (k : ℕ) (i : Fin A.n) {s : Π x, V x}
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F x (s x))) :
    ContDiffOn ℝ k (A.tangentHom.coord i (D s)) (A.image i) := by
  set O : Set ℂ := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.triv i).baseSet
  have hu : ContDiffOn ℝ (k + 1 : ℕ) (A.coord i s) O :=
    A.contDiffOn_coord (hs.of_le ENat.LEInfty.out) i
  have hf : ContDiffOn ℝ k (fun z ↦ complexAntilinearPartL (fderiv ℝ (A.coord i s) z) +
      A.chartZeroOrder D i z (A.coord i s z)) O :=
    (complexAntilinearPartL.contDiff.comp_contDiffOn
      (hu.fderiv_of_isOpen ((A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet)
        (by push_cast; exact le_rfl))).add
      (((A.contDiffOn_chartZeroOrder_of_univ hD hDs i).of_le ENat.LEInfty.out).clm_apply
        (hu.of_le (by exact_mod_cast Nat.le_succ k)))
  exact (hf.mono (A.image_subset_target_inter_preimage_baseSet i)).congr fun _ hz ↦
    coord_tangentHom_eq A hD i hs hz

include hD hDs in
/-- **The higher-order elliptic estimate in a chart.** Let `χ` be a smooth function whose support
has closure in the domain of chart `i`. For `1 < p < ∞` and every `k` there is a constant `C` such
that, for every smooth section `s`, the reading of `χ s` in chart `i` satisfies
`‖(χ s)ᵢ‖_{W^{k+1,p}} ≤ C (‖(D s)ᵢ‖_{W^{k,p}} + ‖sᵢ‖_{W^{k,p}})` on the image of the chart. -/
theorem exists_eLpNormWkp_coord_smul_le (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ) {i : Fin A.n}
    {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ) (hχi : tsupport χ ⊆ A.dom i) :
    ∃ C : ℝ≥0, ∀ s : Π x, V x,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F x (s x)) →
      eLpNormWkp p (A.image i) (k + 1) (A.coord i fun x ↦ χ x • s x) ≤
        C * (eLpNormWkp p (A.image i) k (A.tangentHom.coord i (D s)) +
          eLpNormWkp p (A.image i) k (A.coord i s)) := by
  have := A.compactSpace
  set U : Set ℂ := (A.image i : Set ℂ)
  have hU : IsOpen U := (A.image i).isOpen
  set O : Set ℂ := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.triv i).baseSet
  have hUO : closure U ⊆ O :=
    A.closure_image_subset_target_inter_preimage_baseSet i
  have hcl : closure U ⊆ (A.chart i).target := A.closure_image_subset_target i
  set K : Set ℂ := A.chart i '' tsupport χ
  have hK : IsCompact K := (isClosed_tsupport χ).isCompact.image_of_continuousOn
    ((A.chart i).continuousOn.mono (hχi.trans (A.dom_subset_chart_source i)))
  set χ' : ℂ → ℝ := fun y ↦ χ ((A.chart i).symm y)
  have hχ' : ContDiffOn ℝ ∞ χ' (A.chart i).target := A.contDiffOn_comp_chart_symm hχ i
  have hχK : ∀ z ∈ U, z ∉ K → χ' z = 0 := fun z hz hzK ↦ by
    by_contra h
    exact hzK ⟨_, subset_tsupport _ h, (A.chart i).right_inv (hcl (subset_closure hz))⟩
  obtain ⟨W, hKW, hWU, C₀, hC₀⟩ := exists_eLpNormWkp_le_of_eqOn_complexAntilinearPartL_add
    (F := F) hp hp_top k hU ((A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet)
    (A.isCompact_closure_image i) hUO hK (fun y hy ↦ A.mem_image.2 (image_mono hχi hy))
    ((A.contDiffOn_chartZeroOrder_of_univ hD hDs i).of_le ENat.LEInfty.out)
  obtain ⟨c, hc0, hc⟩ := (hχ'.of_le ENat.LEInfty.out).exists_nonneg_bound_iteratedFDeriv_of_isOpen
    (n := k + 1) (A.chart i).open_target (A.isCompact_closure_image i) hcl
  set B : ℝ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℝ
  refine ⟨((k + 1 : ℕ) + 1 : ℝ≥0) * (‖B‖₊ * ⟨c, hc0⟩ * 2 ^ (k + 1)) * C₀, fun s hs ↦ ?_⟩
  have hu : ContDiffOn ℝ (k + 1 : ℕ) (A.coord i s) O :=
    A.contDiffOn_coord (hs.of_le ENat.LEInfty.out) i
  have hW := hC₀ _ _ (hu.mono (subset_closure.trans hUO)) fun _ hz ↦
    coord_tangentHom_eq A hD i hs hz
  -- Localize the reading of `χ s` to `W`, where the interior estimate applies.
  rw [eLpNormWkp_congr_ae (show (A.coord i fun x ↦ χ x • s x) =ᵐ[volume.restrict U]
      fun y ↦ B (χ' y) (A.coord i s y) from (ae_restrict_mem hU.measurableSet).mono
        fun y hy ↦ A.coord_fun_smul i χ s hy), ENNReal.coe_mul, mul_assoc]
  refine (eLpNormWkp_bilin_le (Fact.out : 1 ≤ p) B hU W.isOpen hWU (c := ⟨c, hc0⟩)
    ((hχ'.of_le ENat.LEInfty.out).mono (subset_closure.trans hcl))
    (hu.mono (subset_closure.trans hUO))
    (fun x hx l hl ↦ hc l hl x (subset_closure (hWU hx))) fun x hx l _ ↦ ?_).trans
    (by gcongr)
  -- Off `K` the product vanishes near `x`.
  have hev : (fun y ↦ B (χ' y) (A.coord i s y)) =ᶠ[nhds x] 0 := by
    filter_upwards [(hU.sdiff hK.isClosed).mem_nhds ⟨hx.1, fun h ↦ hx.2 (hKW h)⟩] with y hy
    simp [B, hχK y hy.1 hy.2]
  rw [(hev.iteratedFDeriv ℝ l).eq_of_nhds, iteratedFDeriv_zero, Pi.zero_apply]

include hD hDs in
/-- For a smooth section `s` with Sobolev section `w`, the `W^{k,p}` norms of the readings of `D s`
and of `s` in chart `i` are bounded by a multiple of `‖D w‖_{W^{k,p}} + ‖w‖_{W^{k,p}}`. -/
private theorem exists_eLpNormWkp_coord_le (k : ℕ) (i : Fin A.n) :
    ∃ c : ℝ≥0, ∀ s : Cₛ^((k + 1 : ℕ) : ℕ∞ω)⟮𝓘(ℝ, ℂ); F, V⟯,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F x (s x)) →
      eLpNormWkp p (A.image i) k (A.tangentHom.coord i (D s)) +
          eLpNormWkp p (A.image i) k (A.coord i s) ≤
        c * (ENNReal.ofReal ‖hD.sobolevSuccL A hDs volume p k
            (SobolevSection.ofContMDiffSection A volume p (k + 1) s)‖ +
          ENNReal.ofReal ‖A.sectionChartData.lowerOrderL volume p k
            (SobolevSection.ofContMDiffSection A volume p (k + 1) s)‖) := by
  obtain ⟨c₂, hc₂⟩ :=
    A.tangentHom.sectionChartData.exists_eLpNormWkp_le_of_chartValueL_ae_eq (p := p) k
  obtain ⟨c₃, hc₃⟩ := A.sectionChartData.exists_eLpNormWkp_le_of_chartValueL_ae_eq (p := p) k
  refine ⟨c₂ + c₃, fun s hs ↦ ?_⟩
  set w := SobolevSection.ofContMDiffSection A volume p (k + 1) s
  set Dw := hD.sobolevSuccL A hDs volume p k w
  set w₀ := A.sectionChartData.lowerOrderL volume p k w
  have h₂ := hc₂ (i := i) (w := ((Dw : SobolevSection A.tangentHom volume p k) :
      A.tangentHom.sectionChartData.SobolevData volume p k))
    (by rw [sectionChartData_image_tangentHom]; exact contDiffOn_coord_tangentHom A hD hDs k i hs)
    ((ae_image_tangentHom_iff A volume i).2
      (chartValueL_sobolevSuccL_ofContMDiffSection_ae A hD hDs volume p k s i))
  rw [sectionChartData_image_tangentHom] at h₂
  have h₃ := hc₃ (i := i) (w := (w₀ : A.sectionChartData.SobolevData volume p k))
    (((A.contDiffOn_coord (s.contMDiff) i).of_le (by exact_mod_cast Nat.le_succ k)).mono
      (A.image_subset_target_inter_preimage_baseSet i))
    ((A.sectionChartData.chartValueL_coe_lowerOrderL volume p k w i).symm ▸
      SobolevSection.chartValueL_ofContMDiffSection_ae A volume p (k + 1) s i)
  -- The norm of the chart-`i` components is at most the norm of the tuple.
  have hDw : ‖((Dw : SobolevSection A.tangentHom volume p k) :
      A.tangentHom.sectionChartData.SobolevData volume p k) i‖ ≤ ‖Dw‖ :=
    (norm_le_pi_norm ((Dw : SobolevSection A.tangentHom volume p k) :
      A.tangentHom.sectionChartData.SobolevData volume p k) i).trans_eq
        ((Submodule.norm_coe _).trans (Submodule.norm_coe Dw))
  have hw₀ : ‖(w₀ : A.sectionChartData.SobolevData volume p k) i‖ ≤ ‖w₀‖ :=
    (norm_le_pi_norm (w₀ : A.sectionChartData.SobolevData volume p k) i).trans_eq
      (Submodule.norm_coe w₀)
  calc _ ≤ c₂ * ENNReal.ofReal ‖Dw‖ + c₃ * ENNReal.ofReal ‖w₀‖ :=
        add_le_add (h₂.trans (by gcongr)) (h₃.trans (by gcongr))
    _ ≤ c₂ * ENNReal.ofReal ‖Dw‖ + c₃ * ENNReal.ofReal ‖w₀‖ +
        (c₂ * ENNReal.ofReal ‖w₀‖ + c₃ * ENNReal.ofReal ‖Dw‖) := le_self_add
    _ = _ := by
        push_cast
        ring

include hD hDs in
/-- **The chart estimate in Sobolev norms, for smooth sections.** For a smooth `χ` whose support
has closure in the domain of chart `i`, the chart-`i` components of `χ w`, for the Sobolev section
`w` of a smooth section, are bounded in `W^{k+1,p}` by a multiple of
`‖D w‖_{W^{k,p}} + ‖w‖_{W^{k,p}}`. -/
private theorem exists_norm_contMDiffSMulL_component_le (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ)
    {i : Fin A.n} {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ) (hχi : tsupport χ ⊆ A.dom i) :
    ∃ C : ℝ, ∀ s : Cₛ^((k + 1 : ℕ) : ℕ∞ω)⟮𝓘(ℝ, ℂ); F, V⟯,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F x (s x)) →
      ‖(SobolevSection.contMDiffSMulL A volume p (k + 1) hχ
          (SobolevSection.ofContMDiffSection A volume p (k + 1) s) :
            A.sectionChartData.SobolevData volume p (k + 1)) i‖ ≤
        C * (‖hD.sobolevSuccL A hDs volume p k
            (SobolevSection.ofContMDiffSection A volume p (k + 1) s)‖ +
          ‖A.sectionChartData.lowerOrderL volume p k
            (SobolevSection.ofContMDiffSection A volume p (k + 1) s)‖) := by
  obtain ⟨Cc, hCc⟩ := exists_eLpNormWkp_coord_smul_le A hD hDs hp hp_top k hχ hχi
  obtain ⟨c₁, hc₁⟩ :=
    A.sectionChartData.exists_ofReal_norm_le_eLpNormWkp_of_chartValueL_ae_eq (p := p) (k + 1)
  obtain ⟨c, hc⟩ := exists_eLpNormWkp_coord_le A hD hDs (p := p) k i
  refine ⟨c₁ * Cc * c, fun s hs ↦ ?_⟩
  set w := SobolevSection.ofContMDiffSection A volume p (k + 1) s
  set a := ‖hD.sobolevSuccL A hDs volume p k w‖
  set b := ‖A.sectionChartData.lowerOrderL volume p k w‖
  have ha0 : 0 ≤ a := norm_nonneg (hD.sobolevSuccL A hDs volume p k w)
  have hb0 : 0 ≤ b := norm_nonneg _
  have hcχ : ContDiffOn ℝ (k + 1 : ℕ) (A.coord i fun x ↦ χ x • s x) (A.image i) :=
    (A.contDiffOn_coord ((hχ.of_le ENat.LEInfty.out).smul_section s.contMDiff) i).mono
      (A.image_subset_target_inter_preimage_baseSet i)
  have h₁ := hc₁ hcχ (SobolevSection.chartValueL_contMDiffSMulL_ae_coord hχ
    (SobolevSection.chartValueL_ofContMDiffSection_ae A volume p (k + 1) s) i)
  refine (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h₁.trans ?_)
  calc (c₁ : ℝ≥0∞) * eLpNormWkp p (A.image i) (k + 1) (A.coord i fun x ↦ χ x • s x)
      ≤ c₁ * (Cc * (c * (ENNReal.ofReal a + ENNReal.ofReal b))) := by
        gcongr
        exact (hCc s hs).trans (by gcongr; exact hc s hs)
    _ = ENNReal.ofReal (c₁ * Cc * c * (a + b)) := by
        rw [← ENNReal.ofReal_add ha0 hb0, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        simp only [ENNReal.ofReal_coe_nnreal, mul_assoc]

omit [T2Space M] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- One term of a partition of unity: if `ψ` is one on the support of `χ`, multiplication by `ψ` is
bounded by `Cψ` times the chart-`i` components, and the chart-`i` components of `χ w` are bounded
by `Cc X`, then `‖χ w‖ ≤ max Cψ 0 * max Cc 0 * X`. -/
private theorem norm_contMDiffSMulL_le_of_component_le {k : ℕ} {i : Fin A.n} {χ ψ : M → ℝ}
    (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ) (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ ψ)
    (hψχ : EqOn ψ 1 (tsupport χ)) {Cψ Cc X : ℝ} (hX : 0 ≤ X)
    (hCψ : ∀ v : SobolevSection A volume p k, ‖SobolevSection.contMDiffSMulL A volume p k hψ v‖ ≤
      Cψ * ‖(v : A.sectionChartData.SobolevData volume p k) i‖)
    (w : SobolevSection A volume p k)
    (hw : ‖(SobolevSection.contMDiffSMulL A volume p k hχ w :
      A.sectionChartData.SobolevData volume p k) i‖ ≤ Cc * X) :
    ‖SobolevSection.contMDiffSMulL A volume p k hχ w‖ ≤ max Cψ 0 * max Cc 0 * X := by
  set v := SobolevSection.contMDiffSMulL A volume p k hχ w
  calc ‖v‖ = ‖SobolevSection.contMDiffSMulL A volume p k hψ v‖ := by
        rw [SobolevSection.contMDiffSMulL_contMDiffSMulL_of_eqOn _ hψ hψχ]
    _ ≤ Cψ * ‖(v : A.sectionChartData.SobolevData volume p k) i‖ := hCψ v
    _ ≤ max Cψ 0 * ‖(v : A.sectionChartData.SobolevData volume p k) i‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max Cψ 0 * (max Cc 0 * X) := by
        gcongr
        exact hw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
    _ = max Cψ 0 * max Cc 0 * X := by ring

include hD hDs in
/-- **The elliptic estimate one order up.** Let `D` be a smooth real Cauchy–Riemann operator on a
complex vector bundle `V` over a compact boundaryless complex curve, with a finite bundle atlas `A`,
and let `1 < p < ∞`. For every `k` there is a constant `C` such that every
`ξ ∈ W^{k+1,p}(Σ, V)` satisfies `‖ξ‖_{W^{k+1,p}} ≤ C (‖D ξ‖_{W^{k,p}} + ‖ξ‖_{W^{k,p}})`, where `D ξ`
is the realization `TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL`. -/
theorem exists_norm_le_norm_sobolevSuccL_add_norm_lowerOrderL (hp : 1 < p) (hp_top : p ≠ ⊤)
    (k : ℕ) :
    ∃ C : ℝ, ∀ w : SobolevSection A volume p (k + 1),
      ‖w‖ ≤ C * (‖hD.sobolevSuccL A hDs volume p k w‖ +
        ‖A.sectionChartData.lowerOrderL volume p k w‖) := by
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
    SobolevSection.exists_norm_contMDiffSMulL_le (μ := volume) (p := p) (k := k + 1) (hψ i)
      (hψi i)
  choose Cc hCc using fun i ↦
    exists_norm_contMDiffSMulL_component_le A hD hDs hp hp_top k (χ i).contMDiff (hχ i)
  set C := ∑ i, max (Cψ i) 0 * max (Cc i) 0
  refine ⟨C, fun w ↦ ?_⟩
  -- The estimate is a closed condition, so it suffices to prove it on the dense set of smooth
  -- sections.
  have hP : IsClosed {w : SobolevSection A volume p (k + 1) | ‖w‖ ≤ C *
      (‖hD.sobolevSuccL A hDs volume p k w‖ + ‖A.sectionChartData.lowerOrderL volume p k w‖)} :=
    isClosed_le continuous_norm (continuous_const.mul
      (((continuous_norm (E := zeroOneSobolevSections A volume p k)).comp
        (hD.sobolevSuccL A hDs volume p k).continuous).add
      (continuous_norm.comp (A.sectionChartData.lowerOrderL volume p k).continuous)))
  have hdense := SobolevSection.dense_ofContMDiffSection_contMDiff (A := A) (μ := volume)
    (p := p) (k := k + 1) hp_top
  refine hP.closure_subset_iff.2 ?_ (hdense.closure_eq ▸ mem_univ w)
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_ofPred_eq]
  set w := SobolevSection.ofContMDiffSection A volume p (k + 1) s
  set X := ‖hD.sobolevSuccL A hDs volume p k w‖ + ‖A.sectionChartData.lowerOrderL volume p k w‖
  have hX : 0 ≤ X := add_nonneg (norm_nonneg (hD.sobolevSuccL A hDs volume p k w)) (norm_nonneg _)
  calc ‖w‖ = ‖∑ i, SobolevSection.contMDiffSMulL A volume p (k + 1) (χ i).contMDiff w‖ := by
        rw [SobolevSection.sum_contMDiffSMulL_eq_self_of_sum_eq_one _ hχ1]
    _ ≤ ∑ i, ‖SobolevSection.contMDiffSMulL A volume p (k + 1) (χ i).contMDiff w‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, max (Cψ i) 0 * max (Cc i) 0 * X := Finset.sum_le_sum fun i _ ↦
        norm_contMDiffSMulL_le_of_component_le A (χ i).contMDiff (hψ i) (fun _ h ↦ (hψ1 i _).1 h)
          hX (hCψ i) w (hCc i s hs)
    _ = C * X := by rw [Finset.sum_mul]

include hD hDs in
/-- **The higher-order elliptic estimate for a smooth real Cauchy–Riemann operator on a closed
surface.** Let `D` be a smooth real Cauchy–Riemann operator on a complex vector bundle `V` over a
compact boundaryless complex curve, with a finite bundle atlas `A`, and let `1 < p < ∞`. For every
`k` there is a constant `C` such that every `ξ ∈ W^{k+1,p}(Σ, V)` satisfies
`‖ξ‖_{W^{k+1,p}} ≤ C (‖D ξ‖_{W^{k,p}} + ‖ξ‖_{Lᵖ})`, where `D ξ` is the realization
`TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL` and `‖ξ‖_{Lᵖ}` is the norm of `ξ` in
`W^{0,p}(Σ, V)`, all `k + 1` derivatives forgotten
(`TauCeti.SectionChartData.lowerToZeroL`). -/
theorem exists_norm_le_norm_sobolevSuccL_add_norm (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ) :
    ∃ C : ℝ, ∀ w : SobolevSection A volume p (k + 1),
      ‖w‖ ≤ C * (‖hD.sobolevSuccL A hDs volume p k w‖ +
        ‖A.sectionChartData.lowerToZeroL volume p (k + 1) w‖) := by
  induction k with
  | zero =>
    obtain ⟨C, hC⟩ := exists_norm_le_norm_sobolevSuccL_add_norm_lowerOrderL A hD hDs hp hp_top 0
    exact ⟨C, fun w ↦ by simpa only [← SectionChartData.lowerToZeroL_lowerOrderL,
      SectionChartData.lowerToZeroL_zero] using hC w⟩
  | succ k ih =>
    obtain ⟨C₁, hC₁⟩ :=
      exists_norm_le_norm_sobolevSuccL_add_norm_lowerOrderL A hD hDs hp hp_top (k + 1)
    obtain ⟨C₂, hC₂⟩ := ih
    refine ⟨max C₁ 0 * (1 + max C₂ 0 * 2), fun w ↦ ?_⟩
    set w' := A.sectionChartData.lowerOrderL volume p (k + 1) w
    set S := ‖hD.sobolevSuccL A hDs volume p (k + 1) w‖
    set L := ‖A.sectionChartData.lowerToZeroL volume p (k + 1 + 1) w‖
    have hS0 : 0 ≤ S := norm_nonneg (hD.sobolevSuccL A hDs volume p (k + 1) w)
    have hL0 : 0 ≤ L := norm_nonneg _
    have hw0 : 0 ≤ ‖w'‖ := norm_nonneg _
    -- The realization on `w'` is the lowered realization on `w`.
    have hS' : ‖hD.sobolevSuccL A hDs volume p k w'‖ ≤ S := by
      rw [← zeroOneLowerOrdersL_sobolevSuccL A hD hDs volume p k w, ← Submodule.norm_coe,
        coe_zeroOneLowerOrdersL, SectionChartData.lowerOrdersL_one]
      exact (SectionChartData.norm_lowerOrderL_le _ _ _ _ _).trans_eq (Submodule.norm_coe _)
    have hw' : ‖w'‖ ≤ max C₂ 0 * (S + L) := by
      refine (hC₂ w').trans ?_
      rw [SectionChartData.lowerToZeroL_lowerOrderL]
      exact mul_le_mul (le_max_left _ _) (add_le_add hS' le_rfl)
        (add_nonneg (norm_nonneg (hD.sobolevSuccL A hDs volume p k w')) (norm_nonneg _))
        (le_max_right _ _)
    have h₁ : 0 ≤ max C₁ 0 := le_max_right _ _
    have h₂ : 0 ≤ max C₂ 0 := le_max_right _ _
    calc ‖w‖ ≤ max C₁ 0 * (S + ‖w'‖) :=
          (hC₁ w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hS0 hw0))
      _ ≤ max C₁ 0 * (S + max C₂ 0 * (S + L)) := by gcongr
      _ ≤ max C₁ 0 * (1 + max C₂ 0 * 2) * (S + L) := by
          nlinarith [mul_nonneg h₁ (mul_nonneg h₂ hL0), mul_nonneg h₁ (mul_nonneg h₂ hS0),
            mul_nonneg h₁ hL0]

end IsRealCauchyRiemannOperator

end Global

end TauCeti
