/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Atlas.Transfer
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Atlas
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density

/-!
# Independence of the realization of a Cauchy–Riemann operator from the bundle atlas

Let `M` be a complex curve without boundary, `V → M` a smooth complex vector bundle, and `D` a
smooth real Cauchy–Riemann operator on `V`. Its realization `W^{1,p}(V) → L^p(Λ^{0,1} ⊗ V)`
(`TauCeti.IsRealCauchyRiemannOperator.sobolevL`) is built on the charts of a finite bundle atlas
`A`. This file shows that the realizations for two finite bundle atlases `A` and `A'` correspond
under the changes of atlas of sections (`TauCeti.SobolevSection.changeAtlas`) and of
`(0,1)`-forms (`TauCeti.zeroOneChangeAtlas`): on smooth sections both realizations are `D`, and
smooth sections are dense in `W^{1,p}` for `p < ∞`. Over a Hausdorff curve both changes of atlas are
isomorphisms (`TauCeti.SobolevSection.transfersTo_of_contMDiffVectorBundle`), so the index of the
realization does not depend on the atlas (McDuff–Salamon, proof of Theorem C.1.10, step 1, where
the index is regarded as an invariant of the operator alone).

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.zeroOneChangeAtlas_comp_sobolevL`: the changes of atlas
  intertwine the realizations.
* `TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_eq_of_atlas`: the realizations for any two
  finite bundle atlases have the same index.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, proof of Theorem C.1.10.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannAtlas : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A A' : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  (μ : Measure ℂ) [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace IsRealCauchyRiemannOperator

variable {A A' μ} in
/-- **The changes of atlas intertwine the realizations.** For `1 ≤ p < ∞`, the realization of `D`
on the atlas `A` followed by the change of atlas of `(0,1)`-forms is the change of atlas of
sections followed by the realization of `D` on the atlas `A'`. -/
theorem zeroOneChangeAtlas_comp_sobolevL (h : SobolevSection.TransfersTo A A' μ p 1)
    (h₀ : SobolevSection.TransfersTo A.tangentHom A'.tangentHom μ p 0) (hp : p ≠ ⊤) :
    (zeroOneChangeAtlas h₀).comp (hD.sobolevL A hDs μ p) =
      (hD.sobolevL A' hDs μ p).comp (SobolevSection.changeAtlas h) := by
  refine ContinuousLinearMap.ext fun w ↦
    (SobolevSection.denseRange_ofContMDiffSection A μ p 1 hp).induction_on w
      (isClosed_eq (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _))
      fun s ↦ ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    SobolevSection.changeAtlas_ofContMDiffSection]
  -- Both sides are the `(0,1)`-form `D s`.
  have hDA (B : FiniteBundleAtlas ℂ M F V) (i : Fin B.n) :
      B.tangentHom.sectionChartData.chartValueL μ p 0 i
          ((hD.sobolevL B hDs μ p (SobolevSection.ofContMDiffSection B μ p 1 s) :
            SobolevSection B.tangentHom μ p 0) : B.tangentHom.sectionChartData.SobolevData μ p 0)
        =ᵐ[μ.restrict (B.tangentHom.image i)] B.tangentHom.coord i (D s) := by
    rw [B.image_tangentHom]
    exact chartValueL_sobolevL_ofContMDiffSection_ae B hD hDs μ p s i
  refine Subtype.ext ?_
  rw [coe_zeroOneChangeAtlas_apply]
  exact SobolevSection.eq_of_ae_eq_coord (SobolevSection.chartValueL_changeAtlas_ae h₀ (hDA A))
    (hDA A')

/-- **The index does not depend on the atlas.** For `1 ≤ p < ∞`, the realizations
`W^{1,p}(V) → L^p(Λ^{0,1} ⊗ V)` of a smooth real Cauchy–Riemann operator built on two finite bundle
atlases have the same index: they correspond under the isomorphisms
`TauCeti.SobolevSection.atlasEquiv` and `TauCeti.zeroOneAtlasEquiv`. -/
theorem index_sobolevL_eq_of_atlas (hp : p ≠ ⊤) :
    (hD.sobolevL A' hDs μ p).index = (hD.sobolevL A hDs μ p).index := by
  have h : SobolevSection.TransfersTo A A' μ p 1 :=
    SobolevSection.transfersTo_of_contMDiffVectorBundle
  have h' : SobolevSection.TransfersTo A' A μ p 1 :=
    SobolevSection.transfersTo_of_contMDiffVectorBundle
  have h₀ : SobolevSection.TransfersTo A.tangentHom A'.tangentHom μ p 0 :=
    SobolevSection.transfersTo_of_contMDiffVectorBundle
  have h₀' : SobolevSection.TransfersTo A'.tangentHom A.tangentHom μ p 0 :=
    SobolevSection.transfersTo_of_contMDiffVectorBundle
  have hS : hD.sobolevL A' hDs μ p =
      ((zeroOneAtlasEquiv h₀ h₀' : zeroOneSobolevSections A μ p 0 →L[ℝ]
        zeroOneSobolevSections A' μ p 0).comp (hD.sobolevL A hDs μ p)).comp
          ((SobolevSection.atlasEquiv h h').symm :
            SobolevSection A' μ p 1 →L[ℝ] SobolevSection A μ p 1) := by
    rw [toContinuousLinearMap_zeroOneAtlasEquiv, zeroOneChangeAtlas_comp_sobolevL hD hDs h h₀ hp,
      ContinuousLinearMap.comp_assoc, ← SobolevSection.toContinuousLinearMap_atlasEquiv h h',
      ContinuousLinearEquiv.coe_comp_coe_symm, ContinuousLinearMap.comp_id]
  rw [hS, ContinuousLinearMap.index_comp_equiv, ContinuousLinearMap.index_equiv_comp]

end IsRealCauchyRiemannOperator

end TauCeti
