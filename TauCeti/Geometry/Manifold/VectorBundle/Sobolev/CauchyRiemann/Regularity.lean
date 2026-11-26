/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Morrey
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
import Mathlib.Tactic.Module
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Annihilator.Basic
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Local

/-!
# Regularity of the kernel and cokernel of smooth real Cauchy–Riemann operators

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`
(so `M` is compact). Let `D` be a smooth real Cauchy–Riemann operator on `V`. In chart `i` it
reads `∂bar uᵢ + Zᵢ uᵢ`, where `Zᵢ` is the smooth zeroth-order term
`TauCeti.FiniteBundleAtlas.chartZeroOrder`
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevL_ae`).
A `(0,1)`-form is complex antilinear, so it is determined by its value on `1`, and the equation
`∂bar u + Z u = 0` is the real Cauchy–Riemann equation `∂ₛu + i ∂ₜu + 2 Z(u)(1) = 0` of the
planar theory.

* **Kernel.** For `2 < p ≤ ∞`, an element `w` of `W^{1,p}(Σ, V)` with `D w = 0`
  (`TauCeti.IsRealCauchyRiemannOperator.sobolevL`) is a smooth section `s` with `D s = 0`
  (`TauCeti.IsRealCauchyRiemannOperator.exists_contMDiff_of_sobolevL_eq_zero`). The continuous
  representative of `w` (Morrey's embedding,
  `TauCeti.SobolevSection.HasContinuousRepresentatives.of_two_lt_mul`) solves in every chart the
  weak Cauchy–Riemann equation with smooth coefficients
  (`TauCeti.IsRealCauchyRiemannOperator.isWeakCauchyRiemannOn_coord_toSection_of_sobolevL_eq_zero`),
  so it is smooth in every chart by interior bootstrapping
  (`TauCeti.contDiffOn_of_isWeakCauchyRiemannOn`), hence a smooth section
  (`TauCeti.FiniteBundleAtlas.contMDiff_of_forall_contDiffOn_coord`).
* **The adjoint equation, in a chart.** A locally `L^q` covector field `ηᵢ : ℂ → (F →L[ℝ] ℝ)`,
  `q > 1`, that annihilates the value on `1` of `∂bar φ + Zᵢ φ` for every test function `φ` on the
  image of chart `i` agrees almost everywhere with a smooth field
  (`TauCeti.IsRealCauchyRiemannOperator.exists_contDiffOn_ae_eq_of_forall_integral_eq_zero`). This
  is the planar statement
  `TauCeti.exists_contDiffOn_ae_eq_of_forall_integral_apply_cauchyRiemann_eq_zero` for `J = i` and
  `S = 2 Zᵢ(·)(1)`. It is the chart form expected of an annihilator of the range of the realization
  of `D`: pairing a `(0,1)`-form with a fibre metric and an area form reads in a chart as such a
  covector field applied to the value on `1` of the reading of the form. Showing that an
  annihilator of the range satisfies this chart equation is not done here.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.isWeakCauchyRiemannOn_coord_toSection_of_sobolevL_eq_zero`:
  in chart `i`, the continuous representative of a kernel element solves
  `∂ₛu + i ∂ₜu = -2 Zᵢ(u)(1)` weakly.
* `TauCeti.IsRealCauchyRiemannOperator.contDiffOn_coord_toSection_of_sobolevL_eq_zero`: it is
  smooth on every chart image.
* `TauCeti.IsRealCauchyRiemannOperator.exists_contMDiff_of_sobolevL_eq_zero`: a kernel element of
  the `W^{1,p} → Lᵖ` realization, `p > 2`, is the Sobolev section of a smooth section in the
  kernel of `D`.
* `TauCeti.IsRealCauchyRiemannOperator.exists_contDiffOn_ae_eq_of_forall_integral_eq_zero`:
  a weak solution of the adjoint equation of `D` in a chart is smooth.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10 (iii) and Theorem C.2.3, and Appendix B.4.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace Complex
open ContinuousLinearMap (complexAntilinearPartL lsmul lsmul_I_mul_lsmul_I)
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold Distributions

namespace TauCeti

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannRegularity : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace IsRealCauchyRiemannOperator

omit [FiniteDimensional ℝ F] in
/-- The value on `1` of the complex antilinear part of a real linear map `L : ℂ → F` is
`½ (L 1 + i L i)`. -/
private theorem complexAntilinearPartL_apply_one (L : ℂ →L[ℝ] F) :
    complexAntilinearPartL L 1 = (2⁻¹ : ℝ) • (L 1 + lsmul ℝ ℂ Complex.I (L Complex.I)) := by
  simp

omit [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- The chart reading of the zero `(0,1)`-form vanishes almost everywhere on the chart image. -/
private theorem chartValueL_zero_ae (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL volume p 0 i
        (((0 : zeroOneSobolevSections A volume p 0) : SobolevSection A.tangentHom volume p 0) :
          A.tangentHom.sectionChartData.SobolevData volume p 0)
      =ᵐ[volume.restrict (A.image i)] 0 := by
  simp only [ZeroMemClass.coe_zero, map_zero]
  exact (ae_image_tangentHom_iff A volume i).1
    (Lp.coeFn_zero (ℂ →L[ℝ] F) p (volume.restrict (A.tangentHom.sectionChartData.image i : Set ℂ)))

/-! ### The kernel -/

include hD hDs in
/-- **A kernel element solves the planar Cauchy–Riemann equation in every chart.** For
`2 < p ≤ ∞`, let `w ∈ W^{1,p}(Σ, V)` with `D w = 0`. In chart `i`, the reading `u` of the continuous
representative of `w` is a weak solution of `∂ₛu + i ∂ₜu = -2 Zᵢ(u)(1)` on the chart image, where
`Zᵢ` is the zeroth-order term of `D` in chart `i`. -/
theorem isWeakCauchyRiemannOn_coord_toSection_of_sobolevL_eq_zero (hp : 2 < p)
    {w : SobolevSection A volume p 1}
    (hw : hD.sobolevL A hDs volume p w = 0) (i : Fin A.n) :
    IsWeakCauchyRiemannOn p (A.image i) (fun _ _ ↦ ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
      (fun z x ↦ -(2 : ℝ) • A.chartZeroOrder D i z x 1)
      (A.coord i (SobolevSection.toSection w)) := by
  have hrep : SobolevSection.HasContinuousRepresentatives A volume p 1 :=
    .of_two_lt_mul (by simpa using hp)
  have hae := SobolevSection.chartValueL_ae_eq_coord_toSection hrep w
  refine isWeakCauchyRiemannOn_iff_forall_hasWeakFDerivOn.2 ⟨A.continuousOn_coord
    (SobolevSection.continuous_toSection hrep w) i, SobolevSection.memWkpLoc_coord w hae i,
    fun Du hDu ↦ ?_⟩
  rw [(A.image i).isOpen.interior_eq]
  rw [show Opens.interior (A.image i : Set ℂ) = A.image i from
    Opens.ext (A.image i).isOpen.interior_eq] at hDu
  -- A weak derivative of the reading is one of the chart data, which give the chart formula.
  have hchart := chartValueL_sobolevL_ae A hD hDs volume p w (hDu.congr_ae (hae i).symm)
  rw [hw] at hchart
  filter_upwards [hchart, chartValueL_zero_ae A (p := p) i, hae i] with y h₁ h₂ h₃
  rw [h₂, h₃] at h₁
  have h1 := congrArg (fun L : ℂ →L[ℝ] F ↦ L 1) h₁
  simp only [Pi.zero_apply, zero_apply, add_apply, complexAntilinearPartL_apply_one] at h1
  linear_combination (norm := module) (-2 : ℝ) • h1

include hD hDs in
/-- **Kernel elements are smooth in every chart.** For `2 < p ≤ ∞` and `w ∈ W^{1,p}(Σ, V)` with
`D w = 0`, the reading of the continuous representative of `w` in chart `i` is smooth on the chart
image. -/
theorem contDiffOn_coord_toSection_of_sobolevL_eq_zero (hp : 2 < p)
    {w : SobolevSection A volume p 1} (hw : hD.sobolevL A hDs volume p w = 0) (i : Fin A.n) :
    ContDiffOn ℝ ∞ (A.coord i (SobolevSection.toSection w)) (A.image i) := by
  -- The zeroth-order term is smooth on an open set containing the chart image.
  set U := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.triv i).baseSet
  have hZ : ContDiffOn ℝ ∞ (A.chartZeroOrder D i) U := A.contDiffOn_chartZeroOrder_of_univ hD hDs i
  have hη : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℂ × F ↦ -(2 : ℝ) • A.chartZeroOrder D i x.1 x.2 1)
      (U ×ˢ univ) :=
    (((hZ.comp contDiffOn_fst fun x (hx : x ∈ U ×ˢ (univ : Set F)) ↦ hx.1).clm_apply
      contDiffOn_snd).clm_apply (contDiffOn_const (c := (1 : ℂ)))).const_smul (-(2 : ℝ))
  exact contDiffOn_of_isWeakCauchyRiemannOn hp (ℓ := ⊤) (J := fun _ _ ↦ lsmul ℝ ℂ Complex.I)
    (η := fun z x ↦ -(2 : ℝ) • A.chartZeroOrder D i z x 1)
    (((A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet).prod isOpen_univ)
    contDiffOn_const hη
    (fun z hz ↦ ⟨A.image_subset_target_inter_preimage_baseSet i hz, mem_univ _⟩)
    (.of_forall fun _ ↦ lsmul_I_mul_lsmul_I)
    (isWeakCauchyRiemannOn_coord_toSection_of_sobolevL_eq_zero A hD hDs hp hw i)

include hD hDs in
/-- **Kernel regularity on closed surfaces** (McDuff–Salamon, Theorem C.1.10 (iii), for smooth
operators). For `2 < p ≤ ∞`, an element `w` of the kernel of the realization
`W^{1,p}(Σ, V) → Lᵖ(Σ, Λ^{0,1} ⊗ V)` of a smooth real Cauchy–Riemann operator `D` is the Sobolev
section of a smooth section `s` with `D s = 0`. -/
theorem exists_contMDiff_of_sobolevL_eq_zero (hp : 2 < p) {w : SobolevSection A volume p 1}
    (hw : hD.sobolevL A hDs volume p w = 0) :
    ∃ (s : Π x : M, V x) (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (T% s)),
      w = SobolevSection.ofContMDiffSection A volume p 1 ⟨s, hs.of_le (by simp)⟩ ∧
        ∀ x, D s x = 0 := by
  have hrep : SobolevSection.HasContinuousRepresentatives A volume p 1 :=
    .of_two_lt_mul (by simpa using hp)
  set s := SobolevSection.toSection w
  have hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (T% s) :=
    A.contMDiff_of_forall_contDiffOn_coord fun i ↦
      contDiffOn_coord_toSection_of_sobolevL_eq_zero A hD hDs hp hw i
  set s₁ : Cₛ^1⟮𝓘(ℝ, ℂ); F, V⟯ := ⟨s, hs.of_le (by simp)⟩
  have hws : w = SobolevSection.ofContMDiffSection A volume p 1 s₁ :=
    SectionChartData.eq_of_ae_eq_coord
      (fun i ↦ (SobolevSection.chartValueL_ae_eq_coord_toSection hrep w i).trans
        (A.sectionChartData_coord_ae_eq volume i s).symm)
      (fun i ↦ (SobolevSection.chartValueL_ofContMDiffSection_ae A volume p 1 s₁ i).trans
        (A.sectionChartData_coord_ae_eq volume i s).symm)
  refine ⟨s, hs, hws, ?_⟩
  -- `D s` is continuous and its readings vanish almost everywhere, hence everywhere.
  have hDsc : Continuous fun x ↦ TotalSpace.mk' (ℂ →L[ℝ] F)
      (E := fun x ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) x (D s x) :=
    (contMDiffOn_univ.1 (hDs.contMDiff (by simpa using hs.contMDiffOn))).continuous
  refine fun x ↦ congrFun (A.tangentHom.eq_of_continuous_of_coord_ae_eq (μ := volume)
    (s := D s) (t := 0) hDsc
    (Bundle.contMDiff_zeroSection (IB := 𝓘(ℝ, ℂ)) (n := 0) ℝ
      (E := fun x ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x)).continuous fun (i : Fin A.n) ↦ ?_) x
  have h := chartValueL_sobolevL_ofContMDiffSection_ae A hD hDs volume p s₁ i
  rw [← hws, hw] at h
  rw [A.image_tangentHom]
  filter_upwards [h.symm.trans (chartValueL_zero_ae A (p := p) i),
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hyi
  exact hy.trans (A.tangentHom.coord_zero (i := (i : Fin A.tangentHom.n))
    (A.image_tangentHom i ▸ hyi)).symm

/-! ### The cokernel, in a chart -/

include hD hDs in
/-- **Weak solutions of the adjoint equation are smooth in a chart.** Let `η` be a locally `L^q`
covector field on the image of chart `i`, `q > 1`, such that `∫ η (∂bar φ + Zᵢ φ)(1) = 0` for every
test function `φ` on the chart image, where `Zᵢ` is the zeroth-order term of `D` in chart `i`. Then
`η` agrees almost everywhere on the chart image with a smooth covector field. This is the chart
form expected of an annihilator of the range of the realization of `D`; that an annihilator
satisfies it is not proved here. -/
theorem exists_contDiffOn_ae_eq_of_forall_integral_eq_zero {i : Fin A.n}
    {η : ℂ → F →L[ℝ] ℝ} {q : ℝ≥0∞} (hq : 1 < q) (hη : MemLpLoc q (A.image i) η)
    (h : ∀ φ : 𝓓(A.image i, F), ∫ z, η z ((complexAntilinearPartL (fderiv ℝ (φ : ℂ → F) z) +
      A.chartZeroOrder D i z ((φ : ℂ → F) z)) 1) = 0) :
    ∃ g : ℂ → F →L[ℝ] ℝ, ContDiffOn ℝ ∞ g (A.image i) ∧ η =ᵐ[volume.restrict (A.image i)] g := by
  have hZ := A.contDiffOn_chartZeroOrder_image hD hDs i
  -- The planar form of the equation: `J = i` and `S = 2 Zᵢ(·)(1)`.
  refine exists_contDiffOn_ae_eq_of_forall_integral_apply_cauchyRiemann_eq_zero
    (J := fun _ ↦ lsmul ℝ ℂ Complex.I) (S := fun z ↦ (2 : ℝ) •
      (ContinuousLinearMap.apply ℝ F (1 : ℂ)).comp (A.chartZeroOrder D i z))
    contDiffOn_const ((contDiffOn_const.clm_comp hZ).const_smul _)
    (fun _ _ ↦ lsmul_I_mul_lsmul_I) hq hη fun φ ↦ ?_
  have h2 := congrArg ((2 : ℝ) * ·) (h φ)
  rw [mul_zero, ← integral_const_mul] at h2
  rw [← h2]
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  simp only [add_apply, complexAntilinearPartL_apply_one, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, map_add, map_smul,
    smul_eq_mul]
  ring

end IsRealCauchyRiemannOperator

end TauCeti
