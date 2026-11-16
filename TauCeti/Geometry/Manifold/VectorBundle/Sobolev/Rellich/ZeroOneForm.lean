/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Rellich.Higher
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm

/-!
# Rellich compactness for Sobolev `(0,1)`-forms

Let `M` be a compact Hausdorff complex curve without boundary, given by a finite bundle atlas `A` of
a complex vector bundle `V → M` with finite-dimensional model fibre, and suppose that `V` is smooth
as a real vector bundle. The Sobolev `(0,1)`-forms `TauCeti.zeroOneSobolevSections A μ p k` form a
closed subspace of the Sobolev space `TauCeti.SobolevSection A.tangentHom μ p k` of `V`-valued
one-forms, and lowering the order maps the `(0,1)`-forms of order `k` to those of any order
`l ≤ k`, giving the continuous inclusion `TauCeti.zeroOneOfOrderLEL`.

For `1 ≤ p < ∞` and `l < k`, this inclusion is a compact operator: it is the restriction of the
compact inclusion `W^{k,p} → W^{l,p}` of `V`-valued one-forms
(`TauCeti.SobolevSection.isCompactOperator_ofOrderLEL` for the atlas `A.tangentHom`) to closed
subspaces. This is the compactness used for the formal adjoint of a real Cauchy–Riemann operator,
which acts on `(0,1)`-forms.

## Main definitions

* `TauCeti.zeroOneOfOrderLEL`: the continuous inclusion of the `(0,1)`-forms of order `k` into
  those of order `l ≤ k`.

## Main results

* `TauCeti.isCompactOperator_zeroOneLowerOrderL`: the inclusion of order `k + 1` into order `k` is
  compact.
* `TauCeti.isCompactOperator_zeroOneOfOrderLEL`: the inclusion of order `k` into order `l < k` is
  compact.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

/-- The complex vector bundle `V` regarded as a real vector bundle, as in
`TauCeti.zeroOneSobolevSections`. -/
local instance instVectorBundleRealRellichZeroOneForm : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

/-- A complex curve is a smooth real surface. -/
local instance instIsManifoldRealRellichZeroOneForm : IsManifold 𝓘(ℝ, ℂ) ∞ M :=
  IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ) ∞ M)

variable {A : FiniteBundleAtlas ℂ M F V} {μ : Measure ℂ} [μ.IsAddHaarMeasure] {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {l k : ℕ}

/-- Lowering the order of a `(0,1)`-form gives a `(0,1)`-form. -/
theorem ofOrderLEL_mem_zeroOneSobolevSections (h : l ≤ k)
    {w : SobolevSection A.tangentHom μ p k} (hw : w ∈ zeroOneSobolevSections A μ p k) :
    A.tangentHom.sectionChartData.ofOrderLEL μ p h w ∈ zeroOneSobolevSections A μ p l := by
  rw [mem_zeroOneSobolevSections_iff] at hw ⊢
  intro i
  rw [SectionChartData.chartValueL_ofOrderLEL]
  exact hw i

variable (A μ p) in
/-- The continuous inclusion of the `(0,1)`-forms of order `k` into those of order `l ≤ k`. -/
def zeroOneOfOrderLEL (h : l ≤ k) :
    zeroOneSobolevSections A μ p k →L[ℝ] zeroOneSobolevSections A μ p l :=
  ((A.tangentHom.sectionChartData.ofOrderLEL μ p h).comp
    (zeroOneSobolevSections A μ p k).subtypeL).codRestrict _
      fun w ↦ ofOrderLEL_mem_zeroOneSobolevSections h w.2

/-- The inclusion of `(0,1)`-forms lowers the order of the underlying one-form. -/
@[simp]
theorem coe_zeroOneOfOrderLEL (h : l ≤ k) (w : zeroOneSobolevSections A μ p k) :
    (zeroOneOfOrderLEL A μ p h w : SobolevSection A.tangentHom μ p l) =
      A.tangentHom.sectionChartData.ofOrderLEL μ p h w :=
  ContinuousLinearMap.coe_codRestrict_apply _ _ _ _

/-- The inclusion of `(0,1)`-forms of order `k + 1` into order `k` is the one-step inclusion
`TauCeti.zeroOneLowerOrderL`. -/
theorem zeroOneOfOrderLEL_succ (w : zeroOneSobolevSections A μ p (k + 1)) :
    zeroOneOfOrderLEL A μ p k.le_succ w = zeroOneLowerOrderL A μ p k w :=
  Subtype.ext <| by
    rw [coe_zeroOneOfOrderLEL, coe_zeroOneLowerOrderL]
    exact (SectionChartData.ofOrderLEL_lowerOrderL le_rfl (w : SobolevSection A.tangentHom μ p
      (k + 1))).symm.trans (SectionChartData.ofOrderLEL_self _)

variable [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]

/-- **Rellich's theorem between any two orders for `(0,1)`-forms.** On a compact complex curve
without boundary, given by a finite bundle atlas, the inclusion of the Sobolev `(0,1)`-forms of
order `k` into those of order `l < k` is a compact operator for every `1 ≤ p < ∞`. -/
theorem isCompactOperator_zeroOneOfOrderLEL (hp : p ≠ ⊤) (hlk : l < k) :
    IsCompactOperator (zeroOneOfOrderLEL A μ p hlk.le) :=
  ((SobolevSection.isCompactOperator_ofOrderLEL A.tangentHom μ hp hlk).comp_clm
    (zeroOneSobolevSections A μ p k).subtypeL).codRestrict _ isClosed_zeroOneSobolevSections

/-- **Rellich's theorem for `(0,1)`-forms.** On a compact complex curve without boundary, given by a
finite bundle atlas, the inclusion of the Sobolev `(0,1)`-forms of order `k + 1` into those of
order `k` is a compact operator for every `1 ≤ p < ∞`. -/
theorem isCompactOperator_zeroOneLowerOrderL (hp : p ≠ ⊤) :
    IsCompactOperator (zeroOneLowerOrderL A μ p k) := by
  convert isCompactOperator_zeroOneOfOrderLEL (A := A) (μ := μ) hp k.lt_succ_self using 1
  funext w
  exact (zeroOneOfOrderLEL_succ w).symm

end TauCeti
