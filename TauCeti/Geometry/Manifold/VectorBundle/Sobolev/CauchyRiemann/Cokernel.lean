/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Annihilator
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.SemiFredholm
public import TauCeti.Analysis.Normed.Module.Annihilator
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Annihilator.Estimate
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Analysis.Sobolev.Wkp.Local.Compactness
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.ExtendByZero
import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional

/-!
# The cokernel of a smooth real Cauchy–Riemann operator on a closed surface

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`
(so `M` is compact). Let `D` be a smooth real Cauchy–Riemann operator on `V`. For `1 < p < ∞`, the
realization `D : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)`
(`TauCeti.IsRealCauchyRiemannOperator.sobolevL`) has finite-dimensional cokernel
(`TauCeti.IsRealCauchyRiemannOperator.finiteDimensional_quotient_range_sobolevL`). With the closed
range and finite-dimensional kernel
(`TauCeti.IsRealCauchyRiemannOperator.isClosed_range_sobolevL`,
`TauCeti.IsRealCauchyRiemannOperator.finiteDimensional_ker_sobolevL`), this is the Fredholm
property of McDuff–Salamon, Theorem C.1.10 (i), for smooth operators on closed surfaces.

## The argument

The range is closed, so by the double-annihilator theorem it suffices that the continuous
functionals `Λ` vanishing on the range form a finite-dimensional space
(`Submodule.finiteDimensional_quotient_of_finiteDimensional_orthogonalBilin`), which holds once its
closed unit ball is totally bounded.

Fix a smooth partition of unity `χ` subordinate to the chart domains, and in every chart `i` open
sets `Q₀ ⋐ Q₁ ⋐ Q₂ ⋐ Q₃ ⋐ Aᵢ` of the chart image `Aᵢ`, with `Q₀` containing the chart image of
the support of `χᵢ`. Over `Q₃`, an annihilator `Λ` is integration against an `L^q` covector field
`θᵢ` solving the adjoint equation weakly, `q` the conjugate exponent
(`TauCeti.exists_memLp_forall_integral_eq_zero_of_annihilator`).

* *Upper bound.* The `L^q(Q₂)` norm of `θᵢ` is at most a constant times `‖Λ‖`
  (`TauCeti.exists_eLpNorm_le_of_forall_eq_setIntegral`), so by the interior estimate for weak
  solutions of the adjoint equation
  (`TauCeti.exists_norm_wkp_le_of_forall_integral_apply_cauchyRiemann_eq_zero`) its values on a
  vector are in `W^{1,q}(Q₁)` with norm at most a constant times `‖Λ‖`. By Rellich's theorem
  (`TauCeti.Wkp.isCompactOperator_restrictL_lowerOrderL`) they lie, for `‖Λ‖ ≤ 1`, in a compact
  subset of `L^q(Q₀)`.
* *Lower bound.* Every `(0,1)`-form `w` is the sum of the `(0,1)`-projections `wᵢ` of the
  products `χᵢ w`, and `Λ wᵢ` is the integral over `Q₀` of `θᵢ` against the chart reading of
  `wᵢ`.
  By Hölder's inequality, `‖Λ - Λ'‖` is at most a constant times the sum of the `L^q(Q₀)` norms
  of the differences of the representing fields.

The map sending `Λ` to the values of its representing fields in `L^q(Q₀)` is therefore a map from
the unit ball into a compact set that shrinks distances by at most a constant factor, which makes
the ball totally bounded (`FiniteDimensional.of_norm_sub_le_mul_dist`). The representing
fields are chosen, so the map is not linear; the lower bound applies to differences because the
difference of two representing fields represents the difference of the functionals.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.finiteDimensional_orthogonalBilin_range_sobolevL`: the
  annihilator of the range of `D` is finite-dimensional.
* `TauCeti.IsRealCauchyRiemannOperator.finiteDimensional_quotient_range_sobolevL`: **the cokernel
  of `D` is finite-dimensional.**

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10 (i) and its proof, Theorem C.2.3.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace Complex
open ContinuousLinearMap (complexAntilinearPartL lsmul lsmul_I_mul_lsmul_I)
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

local instance instVectorBundleRealCauchyRiemannCokernel : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [hq₁ : Fact (1 ≤ q)] [hpq : p.HolderConjugate q]

namespace IsRealCauchyRiemannOperator

/-- `θ` represents the functional `Λ` on the `Lᵖ` `(0,1)`-forms over `Q` in chart `i`:
`Λ w = ∫_Q θ (wᵢ(1))` for every `(0,1)`-form `w` vanishing off the points read in chart `i` inside
`Q`, where `wᵢ` is the chart-`i` reading of `w`. -/
private def Represents (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ) (i : Fin A.n)
    (Q : Opens ℂ) (θ : ℂ → F →L[ℝ] ℝ) : Prop :=
  ∀ w : zeroOneSobolevSections A volume p 0,
    (w : SobolevSection A.tangentHom volume p 0) ∈
        SobolevSection.aeZeroOff A.tangentHom volume p 0 ((A.chart i).symm '' Q) →
      Λ w = ∫ z in Q, θ z (A.tangentHom.sectionChartData.chartValueL volume p 0 i
        ((w : SobolevSection A.tangentHom volume p 0) :
          A.tangentHom.sectionChartData.SobolevData volume p 0) z 1)

/-! ### The upper bound -/

include hD hDs hpq in
/-- **The interior bound of the representing field.** Let `Q₁ ⋐ Q₂ ⋐ Q₃ ⊆ Aᵢ`. There is a
constant `C` such that, whenever `θ ∈ L^q(Q₃)` represents a functional `Λ` over `Q₃` and solves
the adjoint equation of `D` weakly on `Q₃`, its value `θ(·) v` on every `v : F` is in `W^{1,q}(Q₁)`
with norm at most `C ‖v‖ ‖Λ‖`. -/
private theorem exists_norm_wkp_le_of_represents (hp : 1 < p) (hp_top : p ≠ ⊤) (i : Fin A.n)
    {Q₁ Q₂ Q₃ : Opens ℂ} (hQ₃ : (Q₃ : Set ℂ) ⊆ A.image i) (hQ₂ : closure (Q₂ : Set ℂ) ⊆ Q₃)
    (hQ₁c : IsCompact (closure (Q₁ : Set ℂ))) (hQ₁ : closure (Q₁ : Set ℂ) ⊆ Q₂) :
    ∃ C : ℝ, ∀ (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ) (θ : ℂ → F →L[ℝ] ℝ),
      MemLp θ q (volume.restrict Q₃) → Represents A Λ i Q₃ θ →
      (∀ φ : 𝓓(Q₃, F), ∫ z, θ z ((complexAntilinearPartL (fderiv ℝ (φ : ℂ → F) z) +
        A.chartZeroOrder D i z ((φ : ℂ → F) z)) 1) = 0) →
      ∀ v : F, ∃ u : Wkp volume Q₁ q 1,
        (Wkp.value 1 u : ℂ → ℝ) =ᵐ[volume.restrict (Q₁ : Set ℂ)] (fun z ↦ θ z v) ∧
          ‖u‖ ≤ C * ‖v‖ * ‖Λ‖ := by
  have hq : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt (p := p) (q := q)).1
    hp_top.lt_top
  have hq_top : q ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt (p := q) (q := p)).2 hp).ne
  have hQ₂₃ : Q₂ ≤ Q₃ := subset_closure.trans hQ₂
  obtain ⟨C₁, hC₁⟩ := exists_eLpNorm_le_of_forall_eq_setIntegral (p := p) (q := q) A i hQ₃ hQ₂
  -- The adjoint equation in the planar form `∂ₛ + i ∂ₜ + 2 Zᵢ(·)(1)`.
  have hZ := (A.contDiffOn_chartZeroOrder_image hD hDs i).mono (hQ₂₃.trans hQ₃)
  obtain ⟨C₂, hC₂⟩ := exists_norm_wkp_le_of_forall_integral_apply_cauchyRiemann_eq_zero (k := 0)
    (J := fun _ ↦ lsmul ℝ ℂ Complex.I) (S := fun z ↦ (2 : ℝ) •
      (ContinuousLinearMap.apply ℝ F (1 : ℂ)).comp (A.chartZeroOrder D i z))
    contDiffOn_const (((contDiffOn_const.clm_comp hZ).const_smul _).of_le (by simp))
    (fun _ _ ↦ lsmul_I_mul_lsmul_I) hq hq_top hQ₁c hQ₁
  refine ⟨|C₂| * max C₁ 0, fun Λ θ hθ hrep hweak v ↦ ?_⟩
  have hθ₂ : MemLp θ q (volume.restrict Q₂) :=
    hθ.mono_measure (Measure.restrict_mono hQ₂₃ le_rfl)
  -- Test functions on `Q₂` are test functions on `Q₃`.
  have hmono (φ : 𝓓(Q₂, F)) : ((TestFunction.monoCLM ℝ φ : 𝓓(Q₃, F)) : ℂ → F) = φ := by
    simp [TestFunction.monoCLM_apply, hQ₂₃]
  obtain ⟨u, hu, huC⟩ := hC₂ θ hθ₂ (fun φ ↦ integral_apply_cauchyRiemann_eq_zero_of_integral_eq_zero
    (by simpa only [hmono] using hweak (TestFunction.monoCLM ℝ φ))) v
  refine ⟨u, hu, huC.trans ?_⟩
  have hE := hC₁ Λ θ hθ₂ hrep
  calc C₂ * ‖v‖ * (eLpNorm θ q (volume.restrict Q₂)).toReal
      ≤ |C₂| * ‖v‖ * (eLpNorm θ q (volume.restrict Q₂)).toReal := by
        gcongr
        exact le_abs_self C₂
    _ ≤ |C₂| * ‖v‖ * (max C₁ 0 * ‖Λ‖) := by
        gcongr
        exact hE.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    _ = |C₂| * max C₁ 0 * ‖v‖ * ‖Λ‖ := by ring

include hD hDs hpq in
/-- **Compactness of the representing fields.** Let `Q₀ ⋐ Q₁ ⋐ Q₂ ⋐ Q₃ ⊆ Aᵢ` and `v : F`. The
values `θ(·) v` on `Q₀` of the fields `θ` representing functionals `Λ` with `‖Λ‖ ≤ 1` over `Q₃` and
solving the adjoint equation of `D` weakly on `Q₃` lie in a fixed compact subset of `L^q(Q₀)`. -/
private theorem exists_isCompact_of_represents (hp : 1 < p) (hp_top : p ≠ ⊤) (i : Fin A.n)
    {Q₀ Q₁ Q₂ Q₃ : Opens ℂ} (hQ₃ : (Q₃ : Set ℂ) ⊆ A.image i) (hQ₂ : closure (Q₂ : Set ℂ) ⊆ Q₃)
    (hQ₁c : IsCompact (closure (Q₁ : Set ℂ))) (hQ₁ : closure (Q₁ : Set ℂ) ⊆ Q₂)
    (hQ₀c : IsCompact (closure (Q₀ : Set ℂ))) (hQ₀ : closure (Q₀ : Set ℂ) ⊆ Q₁) (v : F) :
    ∃ K : Set (Lp ℝ q (volume.restrict (Q₀ : Set ℂ))), IsCompact K ∧
      ∀ (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ) (θ : ℂ → F →L[ℝ] ℝ),
        MemLp θ q (volume.restrict Q₃) → Represents A Λ i Q₃ θ →
        (∀ φ : 𝓓(Q₃, F), ∫ z, θ z ((complexAntilinearPartL (fderiv ℝ (φ : ℂ → F) z) +
          A.chartZeroOrder D i z ((φ : ℂ → F) z)) 1) = 0) → ‖Λ‖ ≤ 1 →
        ∃ g ∈ K, g =ᵐ[volume.restrict (Q₀ : Set ℂ)] fun z ↦ θ z v := by
  have hQ₀₁ : Q₀ ≤ Q₁ := subset_closure.trans hQ₀
  obtain ⟨C, hC⟩ := exists_norm_wkp_le_of_represents (q := q) A hD hDs hp hp_top i hQ₃ hQ₂ hQ₁c hQ₁
  -- Rellich's theorem: `W^{1,q}(Q₁) → L^q(Q₀)` is compact.
  let R : Wkp volume Q₁ q 1 →L[ℝ] Lp ℝ q (volume.restrict (Q₀ : Set ℂ)) :=
    (Wkp.valueL 0).comp ((Wkp.restrictL hQ₀₁ 0).comp (Wkp.lowerOrderL 0))
  have hR : IsCompactOperator R :=
    (Wkp.isCompactOperator_restrictL_lowerOrderL hQ₀c hQ₀ 0).clm_comp _
  refine ⟨closure (R '' Metric.closedBall 0 (|C| * ‖v‖)),
    hR.isCompact_closure_image_closedBall _, fun Λ θ hθ hrep hweak hΛ ↦ ?_⟩
  obtain ⟨u, hu, huC⟩ := hC Λ θ hθ hrep hweak v
  refine ⟨R u, subset_closure ⟨u, mem_closedBall_zero_iff.2 (huC.trans ?_), rfl⟩, ?_⟩
  · calc C * ‖v‖ * ‖Λ‖ ≤ |C| * ‖v‖ * ‖Λ‖ := by gcongr; exact le_abs_self C
      _ ≤ |C| * ‖v‖ * 1 := by gcongr
      _ = |C| * ‖v‖ := mul_one _
  · -- `R u` is the restriction of the value of `u`.
    filter_upwards [Wkp.value_restrictL_ae hQ₀₁ 0 (Wkp.lowerOrderL 0 u),
      ae_restrict_of_ae_restrict_of_subset hQ₀₁ hu] with z h₁ h₂
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, Wkp.valueL_apply, h₁,
      Wkp.lowerOrderL_apply, ← Wkp.value_succ, h₂]

/-! ### The lower bound -/

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] hq₁ in
include hpq in
/-- **The lower bound in one chart.** Let `Q₀ ⊆ Q ⊆ Aᵢ`, and let `θ` and `θ'` in `L^q(Q)` represent
functionals `Λ` and `Λ'` over `Q`. For every `(0,1)`-form `w` vanishing off the points read in
chart `i` inside `Q₀`, `|Λ w - Λ' w|` is at most the `L^q(Q₀)` norm of `θ - θ'` times the `Lᵖ`
norm of the chart-`i` reading of `w`, by Hölder's inequality. -/
private theorem norm_apply_sub_apply_le {i : Fin A.n} {Q₀ Q : Opens ℂ} (hQ₀ : Q₀ ≤ Q)
    (hQ : (Q : Set ℂ) ⊆ A.image i) {Λ Λ' : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ}
    {θ θ' : ℂ → F →L[ℝ] ℝ} (hθ : MemLp θ q (volume.restrict Q))
    (hθ' : MemLp θ' q (volume.restrict Q)) (hrep : Represents A Λ i Q θ)
    (hrep' : Represents A Λ' i Q θ') {w : zeroOneSobolevSections A volume p 0}
    (hw : (w : SobolevSection A.tangentHom volume p 0) ∈
      SobolevSection.aeZeroOff A.tangentHom volume p 0 ((A.chart i).symm '' Q₀)) :
    ‖Λ w - Λ' w‖ ≤ (eLpNorm (θ - θ') q (volume.restrict Q₀)).toReal *
      ‖A.tangentHom.sectionChartData.chartValueL volume p 0 i
        ((w : SobolevSection A.tangentHom volume p 0) :
          A.tangentHom.sectionChartData.SobolevData volume p 0)‖ := by
  set g := A.tangentHom.sectionChartData.chartValueL volume p 0 i
    ((w : SobolevSection A.tangentHom volume p 0) :
      A.tangentHom.sectionChartData.SobolevData volume p 0)
  have hQi : (Q : Set ℂ) ⊆ A.tangentHom.sectionChartData.image i := by
    rwa [sectionChartData_image_tangentHom]
  have hQ₀' : (Q₀ : Set ℂ) ⊆ Q := SetLike.coe_subset_coe.2 hQ₀
  have hg : MemLp g p (volume.restrict Q) :=
    (Lp.memLp g).mono_measure (Measure.restrict_mono hQi le_rfl)
  -- The pairing `(θ, L) ↦ θ (L 1)` is bounded by `‖θ‖ ‖L‖`.
  have hb : Continuous (Function.uncurry fun (θ : F →L[ℝ] ℝ) (L : ℂ →L[ℝ] F) ↦ θ (L 1)) :=
    continuous_fst.clm_apply (continuous_snd.clm_apply continuous_const)
  have hbd (θ : F →L[ℝ] ℝ) (L : ℂ →L[ℝ] F) : ‖θ (L 1)‖ ≤ (1 : ℝ≥0) * ‖θ‖ * ‖L‖ := by
    simpa using θ.le_opNorm_of_le (L.le_opNorm_of_le (norm_one (α := ℂ)).le)
  have hint (η : ℂ → F →L[ℝ] ℝ) (hη : MemLp η q (volume.restrict Q)) :
      Integrable (fun z ↦ η z (g z 1)) (volume.restrict Q) :=
    memLp_one_iff_integrable.1 (MemLp.of_bilin (fun (θ : F →L[ℝ] ℝ) (L : ℂ →L[ℝ] F) ↦ θ (L 1)) 1
      hη hg hb (.of_forall fun z ↦ by rw [← NNReal.coe_le_coe]; push_cast; exact hbd _ _))
  -- The reading of `w` vanishes almost everywhere on `Q` off `Q₀`.
  have hvan : ∀ᵐ z ∂volume, z ∈ (Q : Set ℂ) \ Q₀ → (θ - θ') z (g z 1) = 0 := by
    have hQ' : (Q : Set ℂ) ⊆ A.tangentHom.image i := by rwa [A.image_tangentHom]
    have h := SobolevSection.chartValueL_eq_zero_ae_of_mem_aeZeroOff_image
      (hQ₀'.trans hQ') hw
    filter_upwards [(ae_restrict_iff' Q.isOpen.measurableSet).1
      (ae_restrict_of_ae_restrict_of_subset hQ' h)] with z hz hzQ
    rw [hz hzQ.1 hzQ.2, zero_apply, map_zero]
  rw [hrep w (SobolevSection.aeZeroOff_mono (image_mono hQ₀) hw),
    hrep' w (SobolevSection.aeZeroOff_mono (image_mono hQ₀) hw), ← integral_sub (hint θ hθ)
      (hint θ' hθ'), setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      Q.isOpen.measurableSet.nullMeasurableSet hQ₀ (by simpa using hvan)]
  -- Hölder's inequality on `Q₀`.
  have hH := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm_of_pos (μ := volume.restrict Q₀) (p := q)
    (q := p) (r := 1) (f := θ - θ') (g := g) _ 1 hb (.of_forall fun z ↦ hbd _ _) one_pos
  have hgQ₀ : eLpNorm g p (volume.restrict Q₀) ≤ ‖g‖ₑ := by
    rw [Lp.eNorm_def]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono (hQ₀'.trans hQi) le_rfl)
  have hE : eLpNorm (θ - θ') q (volume.restrict Q₀) ≠ ⊤ :=
    ((hθ.sub hθ').mono_measure (Measure.restrict_mono hQ₀ le_rfl)).eLpNorm_ne_top
  rw [← toReal_eNorm, ← toReal_eNorm g, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hE eNorm_ne_top) ?_
  refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
  have hm : AEStronglyMeasurable (fun z ↦ θ z (g z 1) - θ' z (g z 1)) (volume.restrict Q₀) :=
    ((hint θ hθ).sub (hint θ' hθ')).aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hQ₀ le_rfl)
  rw [← eLpNorm_one_eq_lintegral_eNorm hm]
  simp only [ENNReal.coe_one, one_mul] at hH
  exact hH.trans (by gcongr)

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
include hpq in
/-- **The lower bound.** Let `χ` be a smooth partition of unity indexed by the charts and, in every
chart `i`, let `Q₀ᵢ ⊆ Qᵢ ⊆ Aᵢ` with the support of `χᵢ` read in chart `i` inside `Q₀ᵢ`. There is a
constant `C` such that, whenever the fields `θᵢ` and `θ'ᵢ` in `L^q(Qᵢ)` represent functionals `Λ`
and `Λ'` over `Qᵢ` in every chart, `‖Λ - Λ'‖` is at most `C` times the sum, over the charts `i`
and the vectors `v` of the basis `finBasis ℝ F`, of the `L^q(Q₀ᵢ)` norms of `(θᵢ - θ'ᵢ)(·) v`. -/
private theorem exists_norm_sub_le_sum (χ : SmoothPartitionOfUnity (Fin A.n) 𝓘(ℝ, ℂ) M univ)
    {Q₀ Q : Fin A.n → Opens ℂ} (hχ : ∀ i, tsupport (χ i) ⊆ (A.chart i).symm '' Q₀ i)
    (hQ₀ : ∀ i, Q₀ i ≤ Q i) (hQ : ∀ i, (Q i : Set ℂ) ⊆ A.image i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Λ Λ' : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ)
      (θ θ' : Fin A.n → ℂ → F →L[ℝ] ℝ), (∀ i, MemLp (θ i) q (volume.restrict (Q i))) →
      (∀ i, MemLp (θ' i) q (volume.restrict (Q i))) → (∀ i, Represents A Λ i (Q i) (θ i)) →
      (∀ i, Represents A Λ' i (Q i) (θ' i)) →
      ‖Λ - Λ'‖ ≤ C * ∑ i, ∑ c, (eLpNorm (fun z ↦ (θ i z - θ' i z) (finBasis ℝ F c)) q
        (volume.restrict (Q₀ i))).toReal := by
  have hχ1 (x : M) : ∑ i, χ i x = 1 := by
    simpa [finsum_eq_sum_of_fintype] using χ.sum_eq_one (mem_univ x)
  set b := finBasis ℝ F
  -- `P i w` is the `(0,1)`-projection of `χᵢ w`; the `P i` sum to the identity.
  let P (i : Fin A.n) :
      zeroOneSobolevSections A volume p 0 →L[ℝ] zeroOneSobolevSections A volume p 0 :=
    (zeroOnePartSobolevL A volume p 0).comp ((SobolevSection.contMDiffSMulL A.tangentHom volume p 0
      (χ i).contMDiff).comp (zeroOneSobolevSections A volume p 0).subtypeL)
  have hP (w : zeroOneSobolevSections A volume p 0) : ∑ i, P i w = w := by
    simp only [P, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, ← map_sum,
      SobolevSection.sum_contMDiffSMulL_eq_self_of_sum_eq_one _ hχ1, zeroOnePartSobolevL_coe]
  set Kb := ∑ c, ‖(b.coord c).toContinuousLinearMap‖
  set k : Fin A.n → ℝ := fun i ↦
    Kb * ‖A.tangentHom.sectionChartData.chartValueL volume p 0 i‖ * ‖P i‖ with hk
  have hk0 (i : Fin A.n) : 0 ≤ k i := by positivity
  refine ⟨∑ i, k i, Finset.sum_nonneg fun i _ ↦ hk0 i,
    fun Λ Λ' θ θ' hθ hθ' hrep hrep' ↦ ?_⟩
  set e : Fin A.n → Fin (finrank ℝ F) → ℝ := fun i c ↦
    (eLpNorm (fun z ↦ (θ i z - θ' i z) (b c)) q (volume.restrict (Q₀ i))).toReal
  have he0 (i : Fin A.n) : 0 ≤ ∑ c, e i c := Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
  -- The norm of `θᵢ - θ'ᵢ` is controlled by its values on the basis.
  have hE (i : Fin A.n) : (eLpNorm (θ i - θ' i) q (volume.restrict (Q₀ i))).toReal ≤
      Kb * ∑ c, e i c :=
    b.toReal_eLpNorm_le_mul_sum_toReal_eLpNorm_apply (((hθ i).sub (hθ' i)).mono_measure
      (Measure.restrict_mono (hQ₀ i) le_rfl)).aestronglyMeasurable
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
  have hmem (i : Fin A.n) : ((P i w : zeroOneSobolevSections A volume p 0) :
      SobolevSection A.tangentHom volume p 0) ∈
        SobolevSection.aeZeroOff A.tangentHom volume p 0 ((A.chart i).symm '' Q₀ i) :=
    SobolevSection.aeZeroOff_mono (hχ i)
      (zeroOnePartSobolevL_mem_aeZeroOff (SobolevSection.contMDiffSMulL_mem_aeZeroOff _ _))
  calc ‖(Λ - Λ') w‖ = ‖∑ i, (Λ (P i w) - Λ' (P i w))‖ := by
        rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, hP, sub_apply]
    _ ≤ ∑ i, ‖Λ (P i w) - Λ' (P i w)‖ := norm_sum_le _ _
    _ ≤ ∑ i, (Kb * ∑ c, e i c) *
          (‖A.tangentHom.sectionChartData.chartValueL volume p 0 i‖ * (‖P i‖ * ‖w‖)) :=
        Finset.sum_le_sum fun i _ ↦ (norm_apply_sub_apply_le A (hQ₀ i) (hQ i) (hθ i) (hθ' i)
          (hrep i) (hrep' i) (hmem i)).trans (mul_le_mul (hE i) ((ContinuousLinearMap.le_opNorm
            _ _).trans (mul_le_mul_of_nonneg_left ((P i).le_opNorm w) (norm_nonneg _)))
            (norm_nonneg _) (mul_nonneg (by positivity) (he0 i)))
    _ ≤ ∑ i, (∑ j, k j) * ((∑ c, e i c) * ‖w‖) := Finset.sum_le_sum fun i _ ↦ by
        calc _ = k i * ((∑ c, e i c) * ‖w‖) := by rw [hk]; ring
          _ ≤ _ := by
            have := he0 i
            gcongr
            exact Finset.single_le_sum (fun j _ ↦ hk0 j) (Finset.mem_univ i)
    _ = (∑ i, k i) * (∑ i, ∑ c, e i c) * ‖w‖ := by
        rw [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]

/-! ### Finite dimension of the cokernel -/

omit [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- **Nested chart sets.** There are a smooth partition of unity `χ` indexed by the charts and, in
every chart `i`, open sets `Q₀ ⋐ Q₁ ⋐ Q₂ ⋐ Q₃ ⋐ Aᵢ` of the chart image `Aᵢ`, the first two with
compact closure, with the support of `χᵢ` read in chart `i` inside `Q₀`. -/
private theorem exists_nested_chart_sets :
    ∃ (χ : SmoothPartitionOfUnity (Fin A.n) 𝓘(ℝ, ℂ) M univ) (Q₀ Q₁ Q₂ Q₃ : Fin A.n → Opens ℂ),
      (∀ i, tsupport (χ i) ⊆ (A.chart i).symm '' Q₀ i) ∧
      (∀ i, IsCompact (closure (Q₀ i : Set ℂ)) ∧ closure (Q₀ i : Set ℂ) ⊆ Q₁ i) ∧
      (∀ i, IsCompact (closure (Q₁ i : Set ℂ)) ∧ closure (Q₁ i : Set ℂ) ⊆ Q₂ i) ∧
      (∀ i, closure (Q₂ i : Set ℂ) ⊆ Q₃ i) ∧ (∀ i, closure (Q₃ i : Set ℂ) ⊆ A.image i) ∧
      ∀ i, Q₀ i ≤ Q₃ i := by
  have := A.compactSpace
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ A.dom
    A.isOpen_dom (by rw [A.iUnion_dom])
  -- The support of `χᵢ` read in chart `i` is a compact subset of the chart image.
  have hK (i : Fin A.n) : IsCompact (A.chart i '' tsupport (χ i)) :=
    A.isCompact_chart_image_of_isClosed (isClosed_tsupport _) (hχ i)
  have step {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
      ∃ W : Opens ℂ, K ⊆ W ∧ closure (W : Set ℂ) ⊆ U ∧ IsCompact (closure (W : Set ℂ)) :=
    let ⟨W, hW, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    ⟨⟨W, hW⟩, hKW, hWU, hWc⟩
  choose Q₃ hK₃ hQ₃ _ using fun i ↦ step (hK i) (A.image i).isOpen
    fun _ hy ↦ A.mem_image.2 (image_mono (hχ i) hy)
  choose Q₂ hK₂ hQ₂ _ using fun i ↦ step (hK i) (Q₃ i).isOpen (hK₃ i)
  choose Q₁ hK₁ hQ₁ hQ₁c using fun i ↦ step (hK i) (Q₂ i).isOpen (hK₂ i)
  choose Q₀ hK₀ hQ₀ hQ₀c using fun i ↦ step (hK i) (Q₁ i).isOpen (hK₁ i)
  refine ⟨χ, Q₀, Q₁, Q₂, Q₃, fun i x hx ↦ ⟨A.chart i x, hK₀ i (mem_image_of_mem _ hx),
    (A.chart i).left_inv (A.dom_subset_chart_source i (hχ i hx))⟩, fun i ↦ ⟨hQ₀c i, hQ₀ i⟩,
    fun i ↦ ⟨hQ₁c i, hQ₁ i⟩, hQ₂, hQ₃, fun i ↦ subset_closure.trans ((hQ₀ i).trans
      (subset_closure.trans ((hQ₁ i).trans (subset_closure.trans (hQ₂ i)))))⟩

include hD hDs in
/-- **The annihilator of the range is finite-dimensional.** On a closed surface, the continuous
functionals on the `Lᵖ` `(0,1)`-forms vanishing on the range of the realization
`W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` of a smooth real Cauchy–Riemann operator `D`, `1 < p < ∞`,
form a finite-dimensional space. -/
theorem finiteDimensional_orthogonalBilin_range_sobolevL (hp : 1 < p) (hp_top : p ≠ ⊤) :
    FiniteDimensional ℝ ((hD.sobolevL A hDs volume p).range.orthogonalBilin
      (topDualPairing ℝ (zeroOneSobolevSections A volume p 0)).flip) := by
  have hpq : p.HolderConjugate p.conjExponent := .conjExponent hp.le
  have : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  set q := p.conjExponent
  set G := (hD.sobolevL A hDs volume p).range.orthogonalBilin
    (topDualPairing ℝ (zeroOneSobolevSections A volume p 0)).flip
  have hG (Λ : G) (w : SobolevSection A volume p 1) :
      (Λ : zeroOneSobolevSections A volume p 0 →L[ℝ] ℝ) (hD.sobolevL A hDs volume p w) = 0 :=
    Submodule.mem_orthogonalBilin.1 Λ.property _ ⟨w, rfl⟩
  obtain ⟨χ, Q₀, Q₁, Q₂, Q₃, hχ, hQ₀, hQ₁, hQ₂, hQ₃, hQ₀₃⟩ := exists_nested_chart_sets A
  have hQ₃' (i : Fin A.n) : (Q₃ i : Set ℂ) ⊆ A.image i := subset_closure.trans (hQ₃ i)
  -- The fields representing an annihilator over `Q₃`, and their compact sets of values.
  choose θ hθ hrep hweak using fun (Λ : G) i ↦
    exists_memLp_forall_integral_eq_zero_of_annihilator (q := q) A hD hDs hp hp_top Λ (hG Λ) i
      (hQ₃ i)
  choose K hK hKθ using fun i (c : Fin (finrank ℝ F)) ↦ exists_isCompact_of_represents (q := q)
    A hD hDs hp hp_top i (hQ₃' i) (hQ₂ i) (hQ₁ i).1 (hQ₁ i).2 (hQ₀ i).1 (hQ₀ i).2 (finBasis ℝ F c)
  obtain ⟨C, hC0, hC⟩ := exists_norm_sub_le_sum (p := p) (q := q) A χ hχ hQ₀₃ hQ₃'
  -- `f Λ` collects the values of the representing fields on the basis, in `L^q(Q₀)`.
  let f (Λ : G) (i : Fin A.n) (c : Fin (finrank ℝ F)) :
      Lp ℝ q (volume.restrict (Q₀ i : Set ℂ)) :=
    (((hθ Λ i).mono_measure (Measure.restrict_mono (hQ₀₃ i) le_rfl)).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℝ (finBasis ℝ F c))).toLp _
  refine FiniteDimensional.of_norm_sub_le_mul_dist (𝕜 := ℝ) (f := f)
    (K := Set.pi univ fun i ↦ Set.pi univ (K i)) (C := C * (A.n * finrank ℝ F))
    (isCompact_univ_pi fun i ↦ isCompact_univ_pi (hK i)) (fun Λ hΛ i _ c _ ↦ ?_)
    (fun Λ Λ' _ _ ↦ ?_)
  · obtain ⟨g, hg, hgθ⟩ := hKθ i c Λ (θ Λ i) (hθ Λ i) (hrep Λ i) (hweak Λ i) hΛ
    convert hg using 1
    exact Lp.ext ((MemLp.coeFn_toLp _).trans hgθ.symm)
  · -- Each `L^q(Q₀)` norm in the lower bound is at most the distance of `f Λ` and `f Λ'`.
    have he (i : Fin A.n) (c : Fin (finrank ℝ F)) :
        (eLpNorm (fun z ↦ (θ Λ i z - θ Λ' i z) (finBasis ℝ F c)) q
          (volume.restrict (Q₀ i))).toReal ≤ dist (f Λ) (f Λ') := by
      rw [dist_eq_norm]
      refine le_trans (le_of_eq ?_) ((norm_le_pi_norm (f Λ i - f Λ' i) c).trans
        (norm_le_pi_norm (f Λ - f Λ') i))
      rw [Pi.sub_apply, ← MemLp.toLp_sub, Lp.norm_toLp]
      -- The two functions agree pointwise: `(θ - θ') z v = θ z v - θ' z v`.
      rfl
    refine (hC Λ Λ' (θ Λ) (θ Λ') (hθ Λ) (hθ Λ') (hrep Λ) (hrep Λ')).trans ?_
    rw [mul_assoc]
    gcongr
    refine (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun c _ ↦ he i c).trans_eq ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

include hD hDs in
/-- **Finite-dimensional cokernel** (McDuff–Salamon, Theorem C.1.10 (i), for smooth operators on
closed surfaces). On a closed surface, the realization `W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` of a
smooth real Cauchy–Riemann operator `D`, `1 < p < ∞`, has finite-dimensional cokernel. -/
theorem finiteDimensional_quotient_range_sobolevL (hp : 1 < p) (hp_top : p ≠ ⊤) :
    FiniteDimensional ℝ
      (zeroOneSobolevSections A volume p 0 ⧸ (hD.sobolevL A hDs volume p).range) := by
  have := finiteDimensional_orthogonalBilin_range_sobolevL A hD hDs hp hp_top
  exact Submodule.finiteDimensional_quotient_of_finiteDimensional_orthogonalBilin _
    (isClosed_range_sobolevL A hD hDs hp hp_top)

end IsRealCauchyRiemannOperator

end TauCeti
