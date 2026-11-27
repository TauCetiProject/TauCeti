/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Exponent
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density

/-!
# Lowering the exponent of Sobolev `(0,1)`-forms

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F` and a finite bundle atlas `A`. For `1 ≤ p ≤ q ≤ ∞` the inclusion
`W^{k,q} → W^{k,p}` of Sobolev sections (`TauCeti.SectionChartData.ofExponentLEL`) keeps the chart
data, so it sends `(0,1)`-forms to `(0,1)`-forms. This file restricts it to the inclusion
`W^{k,q}(Σ, Λ^{0,1} ⊗ V) → W^{k,p}(Σ, Λ^{0,1} ⊗ V)` (`TauCeti.zeroOneOfExponentLEL`), shows that
it commutes with the `(0,1)`-projection, and that it has dense range when `V` is smooth: the
`(0,1)`-projection is onto, and lowering the exponent of one-forms has dense range.

## Main definitions

* `TauCeti.zeroOneOfExponentLEL`: the inclusion of `(0,1)`-forms lowering the exponent.

## Main results

* `TauCeti.zeroOneOfExponentLEL_injective`: the inclusion is injective.
* `TauCeti.zeroOneOfExponentLEL_self`, `TauCeti.zeroOneOfExponentLEL_zeroOneOfExponentLEL`: the
  identity at `p = q` and transitivity.
* `TauCeti.zeroOnePartSobolevL_ofExponentLEL`: lowering the exponent commutes with the
  `(0,1)`-projection.
* `TauCeti.denseRange_zeroOneOfExponentLEL`: the inclusion has dense range.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealZeroOneExponent : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable (A : FiniteBundleAtlas ℂ M F V) (μ : Measure ℂ) [μ.IsAddHaarMeasure]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (k : ℕ)

/-- **Lowering the exponent of `(0,1)`-forms.** For `p ≤ q`, the continuous inclusion
`W^{k,q}(Σ, Λ^{0,1} ⊗ V) → W^{k,p}(Σ, Λ^{0,1} ⊗ V)`, the restriction of
`TauCeti.SectionChartData.ofExponentLEL` (`TauCeti.coe_zeroOneOfExponentLEL`). -/
def zeroOneOfExponentLEL (hpq : p ≤ q) :
    zeroOneSobolevSections A μ q k →L[ℝ] zeroOneSobolevSections A μ p k :=
  (((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.ofExponentLEL μ k hpq).comp
    (zeroOneSobolevSections A μ q k).subtypeL).codRestrict _ fun w ↦
      mem_zeroOneSobolevSections_iff.2 fun i ↦ by
        simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
          SectionChartData.coeFn_chartValueL_ofExponentLEL] using
          mem_zeroOneSobolevSections_iff.1 w.property i

variable {A μ k}

/-- The inclusion of `(0,1)`-forms is the inclusion of the underlying one-forms. -/
@[simp]
theorem coe_zeroOneOfExponentLEL (hpq : p ≤ q) (w : zeroOneSobolevSections A μ q k) :
    (zeroOneOfExponentLEL A μ k hpq w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) =
      (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.ofExponentLEL μ k hpq w :=
  ContinuousLinearMap.coe_codRestrict_apply _ _ _ _

/-- Lowering the exponent of `(0,1)`-forms is injective. -/
theorem zeroOneOfExponentLEL_injective (hpq : p ≤ q) :
    Function.Injective (zeroOneOfExponentLEL A μ k hpq) := fun w w' h ↦
  Subtype.ext <| SectionChartData.ofExponentLEL_injective hpq <| by
    rw [← coe_zeroOneOfExponentLEL, ← coe_zeroOneOfExponentLEL, h]

/-- Lowering the exponent of `(0,1)`-forms from `p` to itself is the identity. -/
@[simp]
theorem zeroOneOfExponentLEL_self (w : zeroOneSobolevSections A μ p k) :
    zeroOneOfExponentLEL A μ k le_rfl w = w :=
  Subtype.ext <| by rw [coe_zeroOneOfExponentLEL, SectionChartData.ofExponentLEL_self]

/-- Lowering the exponent of `(0,1)`-forms is transitive. -/
@[simp]
theorem zeroOneOfExponentLEL_zeroOneOfExponentLEL {r : ℝ≥0∞} [Fact (1 ≤ r)] (hpq : p ≤ q)
    (hqr : q ≤ r) (w : zeroOneSobolevSections A μ r k) :
    zeroOneOfExponentLEL A μ k hpq (zeroOneOfExponentLEL A μ k hqr w) =
      zeroOneOfExponentLEL A μ k (hpq.trans hqr) w :=
  Subtype.ext <| by
    rw [coe_zeroOneOfExponentLEL, coe_zeroOneOfExponentLEL, coe_zeroOneOfExponentLEL,
      SectionChartData.ofExponentLEL_ofExponentLEL]

/-- Lowering the exponent commutes with forgetting derivatives on `(0,1)`-forms. -/
theorem zeroOneLowerOrdersL_zeroOneOfExponentLEL (d : ℕ) (hpq : p ≤ q)
    (w : zeroOneSobolevSections A μ q (k + d)) :
    zeroOneLowerOrdersL A μ p k d (zeroOneOfExponentLEL A μ (k + d) hpq w) =
      zeroOneOfExponentLEL A μ k hpq (zeroOneLowerOrdersL A μ q k d w) :=
  Subtype.ext <| by
    rw [coe_zeroOneLowerOrdersL, coe_zeroOneOfExponentLEL, coe_zeroOneOfExponentLEL,
      coe_zeroOneLowerOrdersL, SectionChartData.lowerOrdersL_ofExponentLEL]

/-- **Lowering the exponent commutes with the `(0,1)`-projection.** Both act on chart data, by
`ContinuousLinearMap.complexAntilinearPartL` and by forgetting integrability. -/
theorem zeroOnePartSobolevL_ofExponentLEL (hpq : p ≤ q)
    (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ q k) :
    zeroOnePartSobolevL A μ p k
        ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.ofExponentLEL μ k hpq w) =
      zeroOneOfExponentLEL A μ k hpq (zeroOnePartSobolevL A μ q k w) := by
  refine Subtype.ext (SectionChartData.eq_of_chartValueL_ae_eq fun i ↦ ?_)
  rw [coe_zeroOneOfExponentLEL, SectionChartData.coeFn_chartValueL_ofExponentLEL]
  filter_upwards [chartValueL_zeroOnePartSobolevL_ae
      ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.ofExponentLEL μ k hpq w) i,
    chartValueL_zeroOnePartSobolevL_ae w i] with y h₁ h₂
  rw [h₁, h₂, SectionChartData.coeFn_chartValueL_ofExponentLEL]

variable [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]

variable (A μ k) in
/-- **Dense range.** For `p ≤ q`, the `W^{k,q}` `(0,1)`-forms are dense in the
`W^{k,p}` `(0,1)`-forms: the `(0,1)`-projection is onto and commutes with lowering the exponent,
and lowering the exponent of one-forms has dense range
(`TauCeti.SobolevSection.denseRange_ofExponentLEL`). -/
theorem denseRange_zeroOneOfExponentLEL (hpq : p ≤ q) :
    DenseRange (zeroOneOfExponentLEL A μ k hpq) := by
  have h := (zeroOnePartSobolevL_surjective (A := A) (μ := μ) (p := p) (k := k)).denseRange.comp
    (SobolevSection.denseRange_ofExponentLEL (A.tangentHom 𝓘(ℝ, ℂ)) μ k hpq)
    (zeroOnePartSobolevL A μ p k).continuous
  refine h.mono ?_
  rintro _ ⟨w, rfl⟩
  exact ⟨_, (zeroOnePartSobolevL_ofExponentLEL hpq w).symm⟩

end TauCeti
