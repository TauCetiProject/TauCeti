/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.HolomorphicFrame.Basic
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
/-- On the open set `u` where the operator is covariantly smooth, its scalar coefficient is
smooth near every chart centre in `u`. -/
theorem eventually_contDiffAt_cauchyRiemannChartCoeff
    (hD : IsRealCauchyRiemannOperator F
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ M) D)
    {u : Set M} (hDs : ContMDiffCovariantDerivativeOn F ∞ D u)
    (hu : IsOpen u) (b : F ≃L[ℂ] ℂ) (x₀ : M) (hx₀ : x₀ ∈ u) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ, ℂ) x₀ x₀),
      ContDiffAt ℝ ∞ (cauchyRiemannChartCoeff D b x₀) z := by
  have : FiniteDimensional ℂ F := .of_injective b.toLinearMap b.injective
  let e := trivializationAt F V x₀
  let φ := extChartAt 𝓘(ℝ, ℂ) x₀
  let s := e.localFrame ((Basis.singleton Unit ℂ).map b.symm.toLinearEquiv) ()
  let a : Set M := (chartAt ℂ x₀).source ∩ (e.baseSet ∩ u)
  have ha : IsOpen a := (chartAt ℂ x₀).open_source.inter (e.open_baseSet.inter hu)
  have hs : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (T% s) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet_of_basis
      ((Basis.singleton Unit ℂ).map b.symm.toLinearEquiv) ()
  have hDa := hD.contMDiffCovariantDerivativeOn_mono_of_isOpen hDs ha (fun _ hx ↦ hx.2.2)
  let eHom := trivializationAt (ℂ →L[ℝ] F)
    (fun x ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) x₀
  have hω := (eHom.contMDiffOn_section_iff ha (by
    intro x hx
    simpa only [eHom, hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet]
      using ⟨hx.1, hx.2.1⟩)).1 (hDa.contMDiff (hs.mono (fun _ hx ↦ hx.2.1)))
  have hchart := contMDiffOn_iff_contDiffOn.1 (hω.comp
    ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ℂ)) x₀).mono inter_subset_left)
    inter_subset_right)
  let W : Set ℂ := φ.target ∩ φ.symm ⁻¹' a
  have hW : IsOpen W := (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage
    (isOpen_extChartAt_target x₀) ha
  have hxW : φ x₀ ∈ W := by
    refine ⟨mem_extChartAt_target x₀, ?_⟩
    rw [mem_preimage, φ.left_inv (mem_extChartAt_source x₀)]
    exact ⟨mem_chart_source ℂ x₀, mem_baseSet_trivializationAt F V x₀, hx₀⟩
  have hc : ContDiffOn ℝ ∞ (cauchyRiemannChartCoeff D b x₀) W := by
    refine (((b.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn
      (hchart.clm_apply (contDiffOn_const (c := (1 : ℂ)))))).congr ?_
    intro z hz
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe, eHom]
    exact cauchyRiemannChartCoeff_eq_hom_trivializationAt D b x₀ hz.1 hz.2.2.1
  filter_upwards [hW.mem_nhds hxW] with z hz
  exact (hc z hz).contDiffAt (hW.mem_nhds hz)

/-- If `finrank ℂ F = 1`, a complex-linear real Cauchy–Riemann operator covariantly smooth on
an open set `u` has a nonzero smooth kernel frame near every point of `u`, with no independently
assumed smooth chart coefficient. -/
theorem exists_isNonvanishingHolomorphicOn_of_contMDiffCovariantDerivativeOn
    (hD : IsRealCauchyRiemannOperator F
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ M) D)
    (hDℂ : IsComplexLinearOperator F D) {u : Set M}
    (hDs : ContMDiffCovariantDerivativeOn F ∞ D u) (hu : IsOpen u)
    (hF : finrank ℂ F = 1) (x₀ : M) (hx₀ : x₀ ∈ u) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ σ : Π x : M, V x,
      IsNonvanishingHolomorphicOn F D σ U := by
  have : FiniteDimensional ℂ F := .of_finrank_pos (by rw [hF]; exact Nat.zero_lt_one)
  let b : F ≃L[ℂ] ℂ := ContinuousLinearEquiv.ofFinrankEq
    (by simpa only [finrank_self] using hF)
  exact hD.exists_isNonvanishingHolomorphicOn b hDℂ x₀
    (hD.eventually_contDiffAt_cauchyRiemannChartCoeff hDs hu b x₀ hx₀)

end TauCeti.IsRealCauchyRiemannOperator
