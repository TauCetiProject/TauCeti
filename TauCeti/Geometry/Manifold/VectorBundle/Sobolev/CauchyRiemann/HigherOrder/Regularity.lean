/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.HigherOrder.Basic
import TauCeti.Analysis.Complex.Wirtinger.Regularity.ZerothOrder
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart.Basic

/-!
# Order-raising regularity for smooth real Cauchy–Riemann operators

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`
(so `M` is compact). Let `D` be a smooth real Cauchy–Riemann operator on `V` and `1 < p < ∞`. This
file proves elliptic regularity across Sobolev orders: if `ξ ∈ W^{1,p}(Σ, V)` and
`D ξ ∈ W^{k,p}(Σ, Λ^{0,1} ⊗ V)`, then `ξ ∈ W^{k+1,p}(Σ, V)`
(`TauCeti.IsRealCauchyRiemannOperator.exists_chartValuesL_eq_of_chartValuesL_sobolevL_eq`). Here
`D ξ` is the realization `TauCeti.IsRealCauchyRiemannOperator.sobolevL` from `W^{1,p}`, and
membership in a Sobolev space of higher order means having the same chart data as an element of
that space. The element of `W^{k+1,p}(Σ, V)` is then sent by the realization
`TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL` at order `k + 1` to the given `(0,1)`-form.

## The argument

In chart `i` the chart data `u` of `ξ` satisfy `∂bar u + Zᵢ u = g` almost everywhere, where `Zᵢ` is
the smooth zeroth-order term of `D` and `g` are the chart data of `D ξ`, in `W^{k,p}_loc` on the
chart image. The interior regularity of `∂bar` plus a zeroth-order term
(`TauCeti.memWkpLoc_succ_of_complexAntilinearPartL_add_ae_eq`) puts `u` in `W^{k+1,p}_loc` on the
chart image. The chart images cover `M`, so these local classes define an element of
`W^{k+1,p}(Σ, V)` (`TauCeti.SobolevSection.exists_ae_eq_coord_of_forall_memWkpLoc_coord`).

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.memWkpLoc_coord_of_chartValuesL_sobolevL_eq`: the chart
  expressions of `ξ` are in `W^{k+1,p}_loc` on the chart images.
* `TauCeti.IsRealCauchyRiemannOperator.exists_chartValuesL_eq_of_chartValuesL_sobolevL_eq`: the
  order-raising regularity on closed surfaces.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10 (iii) and Theorem C.2.3, and Appendix B.4.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealSobolevCauchyRiemannHigherOrderRegularity :
    VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

namespace IsRealCauchyRiemannOperator

include hD hDs in
/-- **Order-raising regularity in a chart.** Let `1 < p < ∞`, let `ξ ∈ W^{1,p}(Σ, V)` have the
chart data of the section `s`, and let the realization `D ξ` have the chart data of a `(0,1)`-form
`η` of order `k`. Then in every chart `i` the chart expression `A.coord i s` lies in
`W^{k+1,p}_loc` on the chart image. -/
theorem memWkpLoc_coord_of_chartValuesL_sobolevL_eq (hp : 1 < p) (hp_top : p ≠ ⊤)
    {ξ : SobolevSection A volume p 1} {η : zeroOneSobolevSections A volume p k}
    (h : (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValuesL volume p 0
        (hD.sobolevL A hDs volume p ξ : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) volume p 0) =
      (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValuesL volume p k
        (η : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) volume p k))
    {s : Π x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL volume p 1 i ξ
      =ᵐ[volume.restrict (A.image i)] A.coord i s)
    (i : Fin A.n) : MemWkpLoc p (A.image i) (k + 1) (A.coord i s) := by
  obtain ⟨t, ht⟩ := SobolevSection.exists_ae_eq_coord
    (η : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) volume p k)
  have hg := SobolevSection.memWkpLoc_coord (A := A.tangentHom 𝓘(ℝ, ℂ)) _ ht i
  rw [A.image_tangentHom] at hg
  have hDu := A.sectionChartData.hasWeakFDerivOn_chartValueL volume p i ξ
  have hi := SectionChartData.chartValuesL_eq_iff.1 h i
  refine memWkpLoc_succ_of_complexAntilinearPartL_add_ae_eq hp hp_top
    (Ω := A.image i) (Z := A.chartZeroOrder D i)
    ((A.contDiffOn_chartZeroOrder_image hD hDs i).of_le (by exact_mod_cast le_top))
    (SobolevSection.memWkpLoc_coord ξ hs i).memLpLoc (hDu.congr_ae (hs i)) hg ?_
  have ht' := (ae_image_tangentHom_iff A volume i).1 (ht i)
  filter_upwards [chartValueL_sobolevL_ae A hD hDs volume p ξ hDu, ht', hs i] with y h₁ h₂ h₃
  rw [← h₃, ← h₂, ← hi]
  exact h₁.symm

include hD hDs in
/-- **Order-raising regularity on closed surfaces** (McDuff–Salamon, Theorem C.1.10 (iii), for
smooth operators). Let `1 < p < ∞` and `ξ ∈ W^{1,p}(Σ, V)`. If the realization `D ξ` has the chart
data of a `(0,1)`-form `η` of order `k`, then `ξ` has the chart data of an element `ζ` of
`W^{k+1,p}(Σ, V)`, and the realization of `D` at order `k + 1` sends `ζ` to `η`. -/
theorem exists_chartValuesL_eq_of_chartValuesL_sobolevL_eq (hp : 1 < p) (hp_top : p ≠ ⊤)
    {ξ : SobolevSection A volume p 1} {η : zeroOneSobolevSections A volume p k}
    (h : (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValuesL volume p 0
        (hD.sobolevL A hDs volume p ξ : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) volume p 0) =
      (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValuesL volume p k
        (η : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) volume p k)) :
    ∃ ζ : SobolevSection A volume p (k + 1),
      A.sectionChartData.chartValuesL volume p (k + 1) ζ =
          A.sectionChartData.chartValuesL volume p 1 ξ ∧
        hD.sobolevSuccL A hDs volume p k ζ = η := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ M := IsManifold.restrictScalars ℝ ‹_›
  obtain ⟨s, hs⟩ := SobolevSection.exists_ae_eq_coord ξ
  obtain ⟨ζ, hζ⟩ := SobolevSection.exists_ae_eq_coord_of_forall_memWkpLoc_coord (A := A) (n := ∞)
    (by simp) (WithTop.coe_le_coe.2 le_top)
    (memWkpLoc_coord_of_chartValuesL_sobolevL_eq A hD hDs hp hp_top h hs)
  have hζξ (i : Fin A.n) : A.sectionChartData.chartValueL volume p (k + 1) i ζ =
      A.sectionChartData.chartValueL volume p 1 i ξ :=
    Lp.ext ((hζ i).trans (hs i).symm)
  refine ⟨ζ, SectionChartData.chartValuesL_eq_iff.2 hζξ,
    Subtype.ext <| SectionChartData.eq_of_chartValueL_ae_eq fun (i : Fin A.n) ↦
      (ae_image_tangentHom_iff A volume i).2 ?_⟩
  have hDu := A.sectionChartData.hasWeakFDerivOn_chartValueL volume p i ξ
  have hDu' : HasWeakFDerivOn volume (A.image i)
      (A.sectionChartData.chartValueL volume p (k + 1) i ζ)
      (A.sectionChartData.chartDerivL volume p i ξ) := by
    rw [hζξ i]
    exact hDu
  filter_upwards [chartValueL_sobolevSuccL_ae A hD hDs volume p k ζ hDu',
    chartValueL_sobolevL_ae A hD hDs volume p ξ hDu] with y h₁ h₂
  rw [h₁, ← SectionChartData.chartValuesL_eq_iff.1 h i, h₂, hζξ i]

end IsRealCauchyRiemannOperator

end TauCeti
