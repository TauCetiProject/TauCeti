/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Fredholm
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Exponent
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Interior
import TauCeti.Analysis.Fredholm.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Exponent
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart.Basic

/-!
# Kernel regularity for real Cauchy–Riemann operators with an `Lᵖ` zeroth-order term

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`
(so `M` is compact). Let `D₀` be a smooth real Cauchy–Riemann operator on `V`, `p > 2` and `α` an
`Lᵖ` zeroth-order term. For `1 ≤ q ≤ p` the realization
`P_q : W^{1,q}(M, V) → L^q(M, Λ^{0,1} ⊗ V)` of `D₀ + α`
(`TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevL`) commutes with lowering the exponent
(`TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevL_ofExponentLEL`). This file proves the
regularity of this square: for `1 < q ≤ q' ≤ p`, a `W^{1,q}` section `ξ` with `P_q ξ ∈ L^{q'}` is a
`W^{1,q'}` section
(`TauCeti.IsRealCauchyRiemannOperator.exists_ofExponentLEL_eq_of_perturbedSobolevL_eq`). In
particular the kernel of `P_q` lies in `W^{1,p}`. So lowering the exponent identifies the kernels
(`TauCeti.IsRealCauchyRiemannOperator.kerPerturbedSobolevLEquiv`) and the cokernels
(`TauCeti.IsRealCauchyRiemannOperator.cokerPerturbedSobolevLEquiv`) of `P_q` and `P_{q'}`. This is
McDuff–Salamon, Theorem C.1.10 (i), regularity of the kernel and the cokernel, for operators of
class `W^{0,p}` at the order `ℓ = k = 1` on closed surfaces.

## The argument

In chart `i` the chart data `u` of `ξ` satisfy `∂ₛu + i ∂ₜu + S u = η` almost everywhere, with
`S = 2 (Zᵢ + αᵢ^{0,1})(·)(1)` locally `Lᵖ` (the smooth zeroth-order term `Zᵢ` of `D₀` plus the
chart data of `α`) and `η = 2 g(1)` locally `L^{q'}`, for the chart data `g` of `P_q ξ`. The planar
regularity theorem `TauCeti.memWkpLoc_one_of_hasWeakFDerivOn_of_ae_eq` puts `u` in
`W^{1,q'}_loc`, and the chart images cover `M`
(`TauCeti.SobolevSection.exists_ae_eq_coord_of_forall_memWkpLoc_coord`).

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevL_ofExponentLEL`: the realizations commute
  with lowering the exponent.
* `TauCeti.IsRealCauchyRiemannOperator.exists_ofExponentLEL_eq_of_perturbedSobolevL_eq`: the
  regularity across exponents.
* `TauCeti.IsRealCauchyRiemannOperator.kerPerturbedSobolevLEquiv`,
  `TauCeti.IsRealCauchyRiemannOperator.finrank_ker_perturbedSobolevL_eq`: the kernels at `q` and
  `q'` are linearly equivalent.
* `TauCeti.IsRealCauchyRiemannOperator.cokerPerturbedSobolevLEquiv`: so are the cokernels.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10 (i), Theorem C.2.3 and Proposition B.4.9.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL complexAntilinearPartL_apply_one lsmul
  lsmul_I_mul_lsmul_I)
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannPerturbationExponent : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p q q' : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] [Fact (1 ≤ (q' : ℝ≥0∞))]

namespace IsRealCauchyRiemannOperator

/-- **The zeroth-order term commutes with lowering the exponent.** For `q ≤ q' ≤ p` and any
additive Haar measure `μ` on the charts, the zeroth-order term at exponent `q` of the `W^{1,q}`
copy of a `W^{1,q'}` section `w` is the `L^q` copy of the zeroth-order term at exponent `q'`
of `w`. -/
theorem perturbationL_ofExponentLEL (μ : Measure ℂ) [μ.IsAddHaarMeasure] (hp : 2 < p)
    (hqq' : q ≤ q') (hq'p : q' ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 0)
    (w : SobolevSection A μ q' 1) :
    perturbationL A μ hp (hqq'.trans hq'p) α
        (A.sectionChartData.ofExponentLEL μ 1 (ENNReal.coe_le_coe.2 hqq') w) =
      zeroOneOfExponentLEL A μ 0 (ENNReal.coe_le_coe.2 hqq') (perturbationL A μ hp hq'p α w) := by
  refine Subtype.ext (SectionChartData.eq_of_chartValueL_ae_eq fun (i : Fin A.n) ↦ ?_)
  refine (ae_image_tangentHom_iff A μ i).2 ?_
  -- Lowering the exponent keeps the chart data, as functions.
  have hw := SectionChartData.coeFn_chartValueL_ofExponentLEL (C := A.sectionChartData)
    (μ := μ) (ENNReal.coe_le_coe.2 hqq') w i
  have hP := SectionChartData.coeFn_chartValueL_ofExponentLEL
    (C := A.tangentHom.sectionChartData) (μ := μ) (ENNReal.coe_le_coe.2 hqq')
    (perturbationL A μ hp hq'p α w : SobolevSection A.tangentHom μ q' 0) i
  rw [coe_zeroOneOfExponentLEL, hP]
  filter_upwards [chartValueL_perturbationL_ae A μ hp (hqq'.trans hq'p) α
      (A.sectionChartData.ofExponentLEL μ 1 (ENNReal.coe_le_coe.2 hqq') w) i,
    chartValueL_perturbationL_ae A μ hp hq'p α w i] with y h₁ h₂
  rw [h₁, h₂, hw]

/-- **The realizations commute with lowering the exponent.** For `q ≤ q' ≤ p`, the realization
of `D₀ + α` at exponent `q` of the `W^{1,q}` copy of a `W^{1,q'}` section `w` is the `L^q` copy of
the realization at exponent `q'` of `w`. -/
theorem perturbedSobolevL_ofExponentLEL (μ : Measure ℂ) [μ.IsAddHaarMeasure] (hp : 2 < p)
    (hqq' : q ≤ q') (hq'p : q' ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 0)
    (w : SobolevSection A μ q' 1) :
    hD.perturbedSobolevL A hDs μ hp (hqq'.trans hq'p) α
        (A.sectionChartData.ofExponentLEL μ 1 (ENNReal.coe_le_coe.2 hqq') w) =
      zeroOneOfExponentLEL A μ 0 (ENNReal.coe_le_coe.2 hqq')
        (hD.perturbedSobolevL A hDs μ hp hq'p α w) := by
  rw [perturbedSobolevL_apply, perturbedSobolevL_apply, map_add, sobolevL_ofExponentLEL,
    perturbationL_ofExponentLEL A μ hp hqq' hq'p]

include hD hDs in
/-- **Regularity in a chart.** For `p > 2`, `1 < q ≤ q' ≤ p` and an `Lᵖ` zeroth-order term `α`,
let `ξ ∈ W^{1,q}(M, V)` have the chart data of the section `s`, and let the realization of `D₀ + α`
send `ξ` to the `L^q` copy of an `L^{q'}` `(0,1)`-form `y`. Then in every chart `i` the chart
expression `A.coord i s` lies in `W^{1,q'}_loc` on the chart image. -/
theorem memWkpLoc_coord_of_perturbedSobolevL_eq (hp : 2 < p) (hq : 1 < q) (hqq' : q ≤ q')
    (hq'p : q' ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p 0)
    {ξ : SobolevSection A volume q 1} {y : zeroOneSobolevSections A volume q' 0}
    (h : hD.perturbedSobolevL A hDs volume hp (hqq'.trans hq'p) α ξ =
      zeroOneOfExponentLEL A volume 0 (ENNReal.coe_le_coe.2 hqq') y)
    {s : Π x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL volume q 1 i ξ
      =ᵐ[volume.restrict (A.image i)] A.coord i s)
    (i : Fin A.n) : MemWkpLoc q' (A.image i) 1 (A.coord i s) := by
  obtain ⟨t, ht⟩ := SobolevSection.exists_ae_eq_coord (y : SobolevSection A.tangentHom volume q' 0)
  have hg := SobolevSection.memWkpLoc_coord (A := A.tangentHom) _ ht i
  rw [A.image_tangentHom] at hg
  have hDu := A.sectionChartData.hasWeakFDerivOn_chartValueL volume q i ξ
  -- The chart data of `α` and the zeroth-order term of `D₀`, as one locally `Lᵖ` field.
  let a : ℂ → F →L[ℝ] ℂ →L[ℝ] F :=
    ⇑((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
      volume p 0 i α)
  have ha : MemLpLoc p (A.image i) a := by
    have h := (Lp.memLp
      ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
        volume p 0 i α)).memLpLoc
    -- The chart images of the section chart data are those of the atlas, by definition.
    rw [← image_hom (A := A) (𝕜 := ℝ) (h := A.tangentHom.closure_dom_subset_baseSet) i]
    exact h
  let ev : (ℂ →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F (1 : ℂ)
  let S : ℂ → F →L[ℝ] F := fun z ↦ (2 : ℝ) • (ev.comp (A.chartZeroOrder D i z) +
    (ev.comp complexAntilinearPartL).comp (a z))
  have hS : MemLpLoc p (A.image i) S := by
    have hZ : MemLpLoc p (A.image i) fun z ↦ ev.comp (A.chartZeroOrder D i z) :=
      (contDiffOn_const.clm_comp (A.contDiffOn_chartZeroOrder_image hD hDs i)).continuousOn
        |>.memLpLoc
    have ha' : MemLpLoc p (A.image i) fun z ↦ (ev.comp complexAntilinearPartL).comp (a z) :=
      ha.clm_comp (G := F →L[ℝ] F)
        ((ContinuousLinearMap.compL ℝ F (ℂ →L[ℝ] F) F) (ev.comp complexAntilinearPartL))
    exact (hZ.add ha').const_smul (2 : ℝ)
  refine memWkpLoc_one_of_hasWeakFDerivOn_of_ae_eq lsmul_I_mul_lsmul_I
    (by exact_mod_cast hp) hS (by exact_mod_cast hq) ENNReal.coe_ne_top
    (SobolevSection.memWkpLoc_coord ξ hs i) (hDu.congr_ae (hs i))
    (by exact_mod_cast hq.trans_le hqq') ENNReal.coe_ne_top (by exact_mod_cast hq'p)
    ((hg.memLpLoc.clm_comp (G := F) ev).const_smul (2 : ℝ)) ?_
  -- The chart data of `P_q ξ` are those of `y`, as functions.
  have hy := SectionChartData.coeFn_chartValueL_ofExponentLEL
    (C := A.tangentHom.sectionChartData) (μ := volume) (ENNReal.coe_le_coe.2 hqq')
    (y : SobolevSection A.tangentHom volume q' 0) i
  filter_upwards [chartValueL_perturbedSobolevL_ae A hD hDs volume hp (hqq'.trans hq'p) α ξ hDu,
    (ae_image_tangentHom_iff A volume i).1 (ht i), hs i] with z h₁ h₂ h₃
  rw [h, coe_zeroOneOfExponentLEL, hy, h₂, h₃] at h₁
  have h1 := congrArg (fun L : ℂ →L[ℝ] F ↦ L 1) h₁
  simp only [add_apply, complexAntilinearPartL_apply_one] at h1
  simp only [S, ev, a, smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, complexAntilinearPartL_apply_one, Pi.smul_apply]
  linear_combination (norm := module) (-2 : ℝ) • h1

include hD hDs in
/-- **Regularity across exponents** (McDuff–Salamon, Theorem C.1.10 (i), regularity of kernel and
cokernel, for operators of class `W^{0,p}` on closed surfaces). For `p > 2`, `1 < q ≤ q' ≤ p` and
an `Lᵖ` zeroth-order term `α`, a `W^{1,q}` section `ξ` whose image under the realization of
`D₀ + α` is the `L^q` copy of an `L^{q'}` `(0,1)`-form is the `W^{1,q}` copy of a `W^{1,q'}`
section. -/
theorem exists_ofExponentLEL_eq_of_perturbedSobolevL_eq (hp : 2 < p) (hq : 1 < q)
    (hqq' : q ≤ q') (hq'p : q' ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p 0)
    {ξ : SobolevSection A volume q 1} {y : zeroOneSobolevSections A volume q' 0}
    (h : hD.perturbedSobolevL A hDs volume hp (hqq'.trans hq'p) α ξ =
      zeroOneOfExponentLEL A volume 0 (ENNReal.coe_le_coe.2 hqq') y) :
    ∃ ξ' : SobolevSection A volume q' 1,
      A.sectionChartData.ofExponentLEL volume 1 (ENNReal.coe_le_coe.2 hqq') ξ' = ξ := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ M := IsManifold.restrictScalars ℝ ‹_›
  obtain ⟨s, hs⟩ := SobolevSection.exists_ae_eq_coord ξ
  obtain ⟨ζ, hζ⟩ := SobolevSection.exists_ae_eq_coord_of_forall_memWkpLoc_coord (A := A) (n := ∞)
    (by simp) (WithTop.coe_le_coe.2 le_top)
    (memWkpLoc_coord_of_perturbedSobolevL_eq A hD hDs hp hq hqq' hq'p α h hs)
  refine ⟨ζ, A.sectionChartData.chartValuesL_injective volume q 1
    (SectionChartData.chartValuesL_eq_iff.2 fun i ↦ Lp.ext ?_)⟩
  rw [SectionChartData.coeFn_chartValueL_ofExponentLEL]
  exact (hζ i).trans (hs i).symm

include hD hDs in
/-- **The kernel does not depend on the exponent** (McDuff–Salamon, Theorem C.1.10 (i), for
operators of class `W^{0,p}` on closed surfaces). For `p > 2`, `1 < q ≤ q' ≤ p` and an `Lᵖ`
zeroth-order term `α`, lowering the exponent is a linear equivalence from the kernel of the
realization `W^{1,q'}(M, V) → L^{q'}(M, Λ^{0,1} ⊗ V)` of `D₀ + α` to the kernel of its realization
`W^{1,q}(M, V) → L^q(M, Λ^{0,1} ⊗ V)`. Taking `q' = p`, every kernel element lies in `W^{1,p}`. -/
def kerPerturbedSobolevLEquiv (hp : 2 < p) (hq : 1 < q) (hqq' : q ≤ q') (hq'p : q' ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p 0) :
    (hD.perturbedSobolevL A hDs volume hp hq'p α).ker ≃ₗ[ℝ]
      (hD.perturbedSobolevL A hDs volume hp (hqq'.trans hq'p) α).ker :=
  LinearMap.kerEquivOfRegularity (perturbedSobolevL_ofExponentLEL A hD hDs volume hp hqq' hq'p α)
    (SectionChartData.ofExponentLEL_injective _) (zeroOneOfExponentLEL_injective _)
    fun _ _ ↦ exists_ofExponentLEL_eq_of_perturbedSobolevL_eq A hD hDs hp hq hqq' hq'p α

/-- The equivalence of kernels is lowering the exponent. -/
@[simp]
theorem coe_kerPerturbedSobolevLEquiv_apply (hp : 2 < p) (hq : 1 < q) (hqq' : q ≤ q')
    (hq'p : q' ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p 0)
    (x : (hD.perturbedSobolevL A hDs volume hp hq'p α).ker) :
    (kerPerturbedSobolevLEquiv A hD hDs hp hq hqq' hq'p α x : SobolevSection A volume q 1) =
      A.sectionChartData.ofExponentLEL volume 1 (ENNReal.coe_le_coe.2 hqq') x :=
  LinearMap.coe_kerEquivOfRegularity_apply _ _ _ _ x

include hD hDs in
/-- **The dimension of the kernel does not depend on the exponent.** -/
theorem finrank_ker_perturbedSobolevL_eq (hp : 2 < p) (hq : 1 < q) (hqq' : q ≤ q')
    (hq'p : q' ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p 0) :
    finrank ℝ (hD.perturbedSobolevL A hDs volume hp hq'p α).ker =
      finrank ℝ (hD.perturbedSobolevL A hDs volume hp (hqq'.trans hq'p) α).ker :=
  (kerPerturbedSobolevLEquiv A hD hDs hp hq hqq' hq'p α).finrank_eq

include hD hDs in
/-- **The cokernel does not depend on the exponent** (McDuff–Salamon, Theorem C.1.10 (i), for
operators of class `W^{0,p}` on closed surfaces). For `p > 2`, `1 < q ≤ q' ≤ p` and an `Lᵖ`
zeroth-order term `α`, lowering the exponent induces a linear equivalence from the cokernel of the
realization of `D₀ + α` at `q'` to its cokernel at `q`. -/
def cokerPerturbedSobolevLEquiv (hp : 2 < p) (hq : 1 < q) (hqq' : q ≤ q') (hq'p : q' ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p 0) :
    (zeroOneSobolevSections A volume q' 0 ⧸ (hD.perturbedSobolevL A hDs volume hp hq'p α).range)
      ≃ₗ[ℝ] zeroOneSobolevSections A volume q 0 ⧸
        (hD.perturbedSobolevL A hDs volume hp (hqq'.trans hq'p) α).range :=
  LinearMap.cokerEquivOfRegularity (perturbedSobolevL_ofExponentLEL A hD hDs volume hp hqq' hq'p α)
    (zeroOneOfExponentLEL_injective _)
    (fun _ _ ↦ exists_ofExponentLEL_eq_of_perturbedSobolevL_eq A hD hDs hp hq hqq' hq'p α)
    ((isFredholm_perturbedSobolevL A hD hDs hp hq (hqq'.trans hq'p) α).range_sup_range_eq_top
      (denseRange_zeroOneOfExponentLEL A volume 0 _))

/-- The equivalence of cokernels sends the class of `w` to the class of its `L^q` copy. -/
@[simp]
theorem cokerPerturbedSobolevLEquiv_mk (hp : 2 < p) (hq : 1 < q) (hqq' : q ≤ q') (hq'p : q' ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p 0)
    (w : zeroOneSobolevSections A volume q' 0) :
    cokerPerturbedSobolevLEquiv A hD hDs hp hq hqq' hq'p α (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (zeroOneOfExponentLEL A volume 0 (ENNReal.coe_le_coe.2 hqq') w) :=
  LinearMap.cokerEquivOfRegularity_mk _ _ _ _ w

end IsRealCauchyRiemannOperator

end TauCeti
