/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Constructions
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Fredholm
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Prod
import TauCeti.Geometry.Manifold.VectorBundle.Prod

/-!
# The index of a direct sum of real Cauchy–Riemann operators

Let `M` be a complex curve without boundary and `V`, `V'` complex vector bundles over `M`, with a
finite bundle atlas `A` of `V` whose chart domains have closures inside the base sets of the
preferred trivializations of `V'` (so `M` is compact). For smooth real Cauchy–Riemann operators
`D₁` on `V` and `D₂` on `V'`, the direct sum `D₁ ⊕ D₂` (`TauCeti.sectionProdMap`,
`TauCeti.IsRealCauchyRiemannOperator.prod`) is a smooth real Cauchy–Riemann operator on
`V ×ᵇ V'` (`ContMDiffCovariantDerivativeOn.sectionProdMap`). This file proves McDuff–Salamon,
proof of Theorem C.1.10, step 1, additivity of the index under direct sums, for the realizations
`W^{1,p} → Lᵖ` on closed surfaces:

`ind (D₁ ⊕ D₂) = ind D₁ + ind D₂`.

Under the isomorphisms `W^{1,p}(V ×ᵇ V') ≃ W^{1,p}(V) × W^{1,p}(V')`
(`TauCeti.SobolevSection.prodEquiv`) and
`Lᵖ(Λ^{0,1} ⊗ (V ×ᵇ V')) ≃ Lᵖ(Λ^{0,1} ⊗ V) × Lᵖ(Λ^{0,1} ⊗ V')`
(`TauCeti.zeroOneSobolevSectionsProdEquiv`), the realization of `D₁ ⊕ D₂` is the product of the
realizations of `D₁` and `D₂` (`TauCeti.IsRealCauchyRiemannOperator.sobolevL_prod`). In chart
`i` the realizations are `∂bar u + Zᵢ u`; the antilinear part `∂bar` commutes with the complex
linear projections of `F × F'`, and the zeroth-order term of `D₁ ⊕ D₂` is the direct sum of those of
`D₁` and `D₂` (`TauCeti.FiniteBundleAtlas.chartZeroOrder_sectionProdMap`). The index of a product
of Fredholm operators is the sum of the indices (`ContinuousLinearMap.IsFredholm.index_prodMap`).

## Main results

* `TauCeti.FiniteBundleAtlas.chartZeroOrder_sectionProdMap`: the zeroth-order term of a direct sum
  in a chart.
* `TauCeti.IsRealCauchyRiemannOperator.sobolevL_prod`: the realization of `D₁ ⊕ D₂` is the
  product of the realizations of `D₁` and `D₂`.
* `TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_prod`: the realization of `D₁ ⊕ D₂`, which
  is Fredholm by `TauCeti.IsRealCauchyRiemannOperator.isFredholm_sobolevL`, has the sum of the
  indices of the realizations of `D₁` and `D₂`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10 and its proof, step 1.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace ℂ F']
  [IsScalarTower ℝ ℂ F'] [FiniteDimensional ℝ F']
  {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')] [∀ x, AddCommGroup (V' x)]
  [∀ x, Module ℝ (V' x)] [∀ x, Module ℂ (V' x)] [∀ x, IsScalarTower ℝ ℂ (V' x)]
  [∀ x, TopologicalSpace (V' x)] [∀ x, IsTopologicalAddGroup (V' x)]
  [∀ x, ContinuousSMul ℝ (V' x)] [FiberBundle F' V'] [VectorBundle ℂ F' V']

local instance instVectorBundleRealCauchyRiemannProdLeft : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

local instance instVectorBundleRealCauchyRiemannProdRight : VectorBundle ℝ F' V' :=
  VectorBundle.restrictScalars ℝ ℂ F' V'

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] [ContMDiffVectorBundle ∞ F' V' 𝓘(ℝ, ℂ)]
  (A : FiniteBundleAtlas ℂ M F V)
  (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F' V' (A.center i)).baseSet)
  {D₁ : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  {D₂ : (Π x : M, V' x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V' x}
  (hD₁ : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D₁)
  (hD₂ : IsRealCauchyRiemannOperator F' (ofComplexManifold ℂ M) D₂)

include hD₁ hD₂ in
/-- **The zeroth-order term of a direct sum.** On the image of chart `i`, the zeroth-order term of
`D₁ ⊕ D₂` in the chart of `A.prod h` is the direct sum of the zeroth-order terms of `D₁` and `D₂`
in the charts of `A` and of `A.ofBaseSet h`. -/
theorem FiniteBundleAtlas.chartZeroOrder_sectionProdMap {i : Fin A.n} {y : ℂ} (hy : y ∈ A.image i)
    (u : F) (u' : F') :
    (A.prod h).chartZeroOrder (sectionProdMap D₁ D₂) i y (u, u') =
      (A.chartZeroOrder D₁ i y u).prod ((A.ofBaseSet h).chartZeroOrder D₂ i y u') := by
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  have : ∀ x, ContinuousSMul ℂ (V' x) := VectorBundle.continuousSMul ℂ F' V'
  have hx := A.symm_mem_dom hy
  -- The section of `V ×ᵇ V'` which reads as the constant `(u, u')` in chart `i`.
  set σ : Π x, (V ×ᵇ V') x := fun x ↦ ((A.triv i).symm x u, ((A.ofBaseSet h).triv i).symm x u')
  have hσ : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F × F'))
      (fun x ↦ TotalSpace.mk' (F × F') x (σ x)) ((A.chart i).symm y) :=
    mdifferentiableAt_section_prod_iff.2
      ⟨Manifold.mdifferentiableAt_symm_of_mem_baseSet u (A.dom_subset_baseSet i hx),
        Manifold.mdifferentiableAt_symm_of_mem_baseSet u' (h i (subset_closure hx))⟩
  have hc : (A.prod h).coord i σ =ᶠ[nhds y] fun _ ↦ (u, u') := by
    filter_upwards [(A.image i).isOpen.mem_nhds hy] with z hz
    rw [FiniteBundleAtlas.coord_prod]
    exact Prod.ext (A.coord_triv_symm u hz)
      ((A.ofBaseSet h).coord_triv_symm u' ((FiniteBundleAtlas.image_ofBaseSet (h := h) i).ge hz))
  have key := (A.prod h).coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder
    (hD₁.prod hD₂) (by simpa using hy) hσ
  rw [hc.fderiv_eq, fderiv_const_apply, map_zero, zero_add, hc.eq_of_nhds] at key
  rw [← key, FiniteBundleAtlas.coord_tangentHom_prod A h i _ hy,
    A.chartZeroOrder_apply_eq_coord_tangentHom hD₁ hy]
  refine congrArg₂ ContinuousLinearMap.prod ?_ (Eq.trans ?_
    ((A.ofBaseSet h).chartZeroOrder_apply_eq_coord_tangentHom hD₂
      ((FiniteBundleAtlas.image_ofBaseSet (h := h) i).ge hy) u').symm) <;>
  simp only [σ, sectionProdMap_apply, ContinuousLinearMap.fst_comp_prod,
    ContinuousLinearMap.snd_comp_prod]

namespace IsRealCauchyRiemannOperator

variable [T2Space M] {A h}
  (hD₁s : ContMDiffCovariantDerivativeOn F ∞ D₁ univ)
  (hD₂s : ContMDiffCovariantDerivativeOn F' ∞ D₂ univ)
  (μ : Measure ℂ) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)]

include hD₁ hD₂ in
/-- **The realization of a direct sum is the product of the realizations.** Under the
isomorphisms `TauCeti.SobolevSection.prodEquiv` of Sobolev sections and
`TauCeti.zeroOneSobolevSectionsProdEquiv` of Sobolev `(0,1)`-forms, the realization of `D₁ ⊕ D₂`
on `V ×ᵇ V'` sends a Sobolev section to the pair of the realizations of `D₁` and `D₂` on its
components. -/
theorem sobolevL_prod (w : SobolevSection (A.prod h) μ p 1) :
    zeroOneSobolevSectionsProdEquiv A h μ p 0
        ((hD₁.prod hD₂).sobolevL (A.prod h) (hD₁s.sectionProdMap hD₂s) μ p w) =
      (hD₁.sobolevL A hD₁s μ p (SobolevSection.prodEquiv A h μ p 1 w).1,
        hD₂.sobolevL (A.ofBaseSet h) hD₂s μ p (SobolevSection.prodEquiv A h μ p 1 w).2) := by
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  have : ∀ x, ContinuousSMul ℂ (V' x) := VectorBundle.continuousSMul ℂ F' V'
  -- The projections of `F × F'` are complex linear.
  have hfst : (ContinuousLinearMap.fst ℂ F F').restrictScalars ℝ = ContinuousLinearMap.fst ℝ F F' :=
    ContinuousLinearMap.ext fun _ ↦ rfl
  have hsnd : (ContinuousLinearMap.snd ℂ F F').restrictScalars ℝ = ContinuousLinearMap.snd ℝ F F' :=
    ContinuousLinearMap.ext fun _ ↦ rfl
  have hsub (i : Fin A.n) : (A.image i : Set ℂ) ⊆ (A.prod h).image i :=
    (FiniteBundleAtlas.image_prod (h := h) i).ge
  have hDu (i : Fin A.n) := (A.prod h).sectionChartData.hasWeakFDerivOn_chartValueL μ p i
    (w : (A.prod h).sectionChartData.SobolevData μ p 1)
  have hT (i : Fin A.n) := ae_restrict_of_ae_restrict_of_subset (hsub i)
    (chartValueL_sobolevL_ae (A.prod h) (hD₁.prod hD₂) (hD₁s.sectionProdMap hD₂s) μ p w (hDu i))
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [coe_zeroOneSobolevSectionsProdEquiv_fst]
    refine SectionChartData.eq_of_chartValueL_ae_eq fun i ↦ (A.ae_image_tangentHom_iff μ i).2 ?_
    have h₁ := SobolevSection.chartValueL_prodEquiv_fst_ae w i
    filter_upwards [SobolevSection.chartValueL_tangentHomProdEquiv_fst_ae
      ((hD₁.prod hD₂).sobolevL (A.prod h) (hD₁s.sectionProdMap hD₂s) μ p w :
        SobolevSection (A.prod h).tangentHom μ p 0) i, hT i,
      chartValueL_sobolevL_ae A hD₁ hD₁s μ p _
        ((((hDu i).mono (hsub i)).clm_comp (ContinuousLinearMap.fst ℝ F F')).congr_ae h₁.symm), h₁,
      ae_restrict_mem (A.image i).isOpen.measurableSet] with y e₁ e₂ e₃ e₄ hy
    have hZ (a : F × F') : (ContinuousLinearMap.fst ℝ F F').comp
        ((A.prod h).chartZeroOrder (sectionProdMap D₁ D₂) i y a) = A.chartZeroOrder D₁ i y a.1 := by
      rw [FiniteBundleAtlas.chartZeroOrder_sectionProdMap A h hD₁ hD₂ hy,
        ContinuousLinearMap.fst_comp_prod]
    rw [e₁, e₂, e₃, e₄, ContinuousLinearMap.comp_add, hZ, ← hfst,
      ContinuousLinearMap.complexAntilinearPartL_restrictScalars_comp]
  · rw [coe_zeroOneSobolevSectionsProdEquiv_snd]
    refine SectionChartData.eq_of_chartValueL_ae_eq fun i ↦
      (FiniteBundleAtlas.ae_image_tangentHom_ofBaseSet_iff (h := h)).2 ?_
    have h₁ := SobolevSection.chartValueL_prodEquiv_snd_ae w i
    have hsub' : ((A.ofBaseSet h).image i : Set ℂ) ⊆ A.image i :=
      (FiniteBundleAtlas.image_ofBaseSet (h := h) i).le
    filter_upwards [SobolevSection.chartValueL_tangentHomProdEquiv_snd_ae
      ((hD₁.prod hD₂).sobolevL (A.prod h) (hD₁s.sectionProdMap hD₂s) μ p w :
        SobolevSection (A.prod h).tangentHom μ p 0) i, hT i,
      ae_restrict_of_ae_restrict_of_subset (FiniteBundleAtlas.image_ofBaseSet (h := h) i).ge
        (chartValueL_sobolevL_ae (A.ofBaseSet h) hD₂ hD₂s μ p _
          ((((hDu i).mono ((hsub' ).trans (hsub i))).clm_comp
            (ContinuousLinearMap.snd ℝ F F')).congr_ae (ae_restrict_of_ae_restrict_of_subset hsub'
              h₁.symm))), h₁,
      ae_restrict_mem (A.image i).isOpen.measurableSet] with y e₁ e₂ e₃ e₄ hy
    have hZ (a : F × F') : (ContinuousLinearMap.snd ℝ F F').comp
        ((A.prod h).chartZeroOrder (sectionProdMap D₁ D₂) i y a) =
          (A.ofBaseSet h).chartZeroOrder D₂ i y a.2 := by
      rw [FiniteBundleAtlas.chartZeroOrder_sectionProdMap A h hD₁ hD₂ hy,
        ContinuousLinearMap.snd_comp_prod]
    rw [e₁, e₂, e₃, e₄, ContinuousLinearMap.comp_add, hZ, ← hsnd,
      ContinuousLinearMap.complexAntilinearPartL_restrictScalars_comp]

include hD₁ hD₂ in
/-- **The index is additive under direct sums** (McDuff–Salamon, proof of Theorem C.1.10, step 1,
on closed surfaces). For smooth real Cauchy–Riemann operators `D₁` on `V` and `D₂` on `V'` and
`1 < p < ∞`, the realization of `D₁ ⊕ D₂` on `W^{1,p}(V ×ᵇ V')` has the sum of the indices of the
realizations of `D₁` and `D₂`. It is Fredholm by
`TauCeti.IsRealCauchyRiemannOperator.isFredholm_sobolevL`. -/
theorem index_sobolevL_prod (hp : 1 < p) (hp_top : p ≠ ⊤) :
    ((hD₁.prod hD₂).sobolevL (A.prod h) (hD₁s.sectionProdMap hD₂s) volume p).index =
      (hD₁.sobolevL A hD₁s volume p).index +
        (hD₂.sobolevL (A.ofBaseSet h) hD₂s volume p).index := by
  have heq : (hD₁.prod hD₂).sobolevL (A.prod h) (hD₁s.sectionProdMap hD₂s) volume p =
      ((zeroOneSobolevSectionsProdEquiv A h volume p 0).symm : _ →L[ℝ] _).comp
        (((hD₁.sobolevL A hD₁s volume p).prodMap
          (hD₂.sobolevL (A.ofBaseSet h) hD₂s volume p)).comp
            (SobolevSection.prodEquiv A h volume p 1 : _ →L[ℝ] _)) :=
    ContinuousLinearMap.ext fun w ↦
      (zeroOneSobolevSectionsProdEquiv A h volume p 0).eq_symm_apply.2
        (sobolevL_prod hD₁ hD₂ hD₁s hD₂s volume p w)
  rw [heq, ContinuousLinearMap.index_equiv_comp, ContinuousLinearMap.index_comp_equiv,
    (isFredholm_sobolevL A hD₁ hD₁s hp hp_top).index_prodMap
      (isFredholm_sobolevL (A.ofBaseSet h) hD₂ hD₂s hp hp_top)]

end IsRealCauchyRiemannOperator

end TauCeti
