/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.HolomorphicFrame
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Smooth

/-!
# Smooth coefficients and local kernel frames

The native covariant regularity of a Cauchy–Riemann operator implies the smoothness of its local
scalar coefficient. Consequently, a smooth complex-linear real Cauchy–Riemann line operator
admits local kernel frames without any additional local-coordinate regularity hypothesis.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix C.1.
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped ContDiff Manifold Topology TauCeti.ComplexManifold

namespace TauCeti.IsRealCauchyRiemannOperator

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  [T2Space M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [VectorBundle ℂ F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}

omit [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] in
/-- A smooth operator has a smooth scalar coefficient near every chart centre. -/
theorem eventually_contDiffAt_cauchyRiemannChartCoeff
    (hD : IsRealCauchyRiemannOperator F
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ M) D)
    (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ) (b : F ≃L[ℂ] ℂ) (x₀ : M) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ, ℂ) x₀ x₀),
      ContDiffAt ℝ ∞ (cauchyRiemannChartCoeff D b x₀) z := by
  let : FiniteDimensional ℂ F := .of_injective b.toLinearMap b.injective
  let e := trivializationAt F V x₀
  let φ := extChartAt 𝓘(ℝ, ℂ) x₀
  let s := e.localFrame ((Basis.singleton Unit ℂ).map b.symm.toLinearEquiv) ()
  let a : Set M := (chartAt ℂ x₀).source ∩ e.baseSet
  have ha : IsOpen a := (chartAt ℂ x₀).open_source.inter e.open_baseSet
  have hs : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (T% s) e.baseSet := by
    rw [e.contMDiffOn_section_iff e.open_baseSet subset_rfl]
    refine (contMDiffOn_const (c := b.symm 1)).congr fun x hx ↦ ?_
    rw [← e.continuousLinearMapAt_apply_of_mem (R := ℂ) hx,
      Manifold.continuousLinearMapAt_localFrame _ hx, Basis.map_apply, Basis.singleton_apply]
    rfl
  have hDa := hD.contMDiffCovariantDerivativeOn_mono_of_isOpen hDs ha (subset_univ a)
  let eHom := trivializationAt (ℂ →L[ℝ] F)
    (fun x ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) x₀
  have hω := (eHom.contMDiffOn_section_iff ha (by
    intro x hx
    simpa only [eHom, hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet]
      using hx)).1 (hDa.contMDiff (by simpa using hs.mono (inter_subset_right (s :=
        (chartAt ℂ x₀).source) (t := e.baseSet))))
  have hchart := contMDiffOn_iff_contDiffOn.1 (hω.comp
    ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ℂ)) x₀).mono inter_subset_left)
    inter_subset_right)
  let W : Set ℂ := φ.target ∩ φ.symm ⁻¹' a
  have hW : IsOpen W := (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage
    (isOpen_extChartAt_target x₀) ha
  have hxW : φ x₀ ∈ W := by
    refine ⟨mem_extChartAt_target x₀, ?_⟩
    rw [mem_preimage, φ.left_inv (mem_extChartAt_source x₀)]
    exact ⟨mem_chart_source ℂ x₀, mem_baseSet_trivializationAt F V x₀⟩
  have hc : ContDiffOn ℝ ∞ (cauchyRiemannChartCoeff D b x₀) W := by
    refine (((b.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn
      (hchart.clm_apply (contDiffOn_const (c := (1 : ℂ)))))).congr ?_
    intro z hz
    have hy : φ.symm z ∈ (chartAt ℂ x₀).source := hz.2.1
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe, eHom, hom_trivializationAt_apply,
      ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
    rw [TangentBundle.symmL_trivializationAt hy, φ.right_inv hz.1]
    rw [cauchyRiemannChartCoeff_apply,
      (trivializationAt F V x₀).continuousLinearMapAt_apply_of_mem (R := ℂ) hz.2.2,
      (trivializationAt F V x₀).continuousLinearMapAt_apply_of_mem (R := ℝ) hz.2.2]
    rfl
  filter_upwards [hW.mem_nhds hxW] with z hz
  exact (hc z hz).contDiffAt (hW.mem_nhds hz)

/-- A smooth complex-linear real Cauchy–Riemann line operator has a nonzero smooth kernel
frame near every point, with no independently assumed smooth chart coefficient. -/
theorem exists_isNonvanishingHolomorphicOn_of_contMDiffCovariantDerivativeOn
    (hD : IsRealCauchyRiemannOperator F
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ M) D)
    (hDℂ : IsComplexLinearOperator F D) (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
    (b : F ≃L[ℂ] ℂ) (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ σ : Π x : M, V x,
      IsNonvanishingHolomorphicOn F D σ U :=
  hD.exists_isNonvanishingHolomorphicOn b hDℂ x₀
    (hD.eventually_contDiffAt_cauchyRiemannChartCoeff hDs b x₀)

end TauCeti.IsRealCauchyRiemannOperator
