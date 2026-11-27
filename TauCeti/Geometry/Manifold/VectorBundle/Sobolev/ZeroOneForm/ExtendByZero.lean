/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.AEZeroOff
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Basic

/-!
# Extension by zero of `(0,1)`-forms from one chart

Let `M` be a complex curve without boundary, `V → M` a complex vector bundle with
finite-dimensional model fibre `F` and finite bundle atlas `A`, and `L` a closed subset of the
domain of chart `i`. Under `TauCeti.SobolevSection.HasExtensionByZero` for the one-forms
`A.tangentHom`, a tuple `g` of chart-`i` Sobolev functions vanishing off `L` extends by zero to a
`V`-valued one-form (`TauCeti.SobolevSection.extendByZeroL`). Its `(0,1)`-projection
(`TauCeti.zeroOnePartSobolevL`) is a `(0,1)`-form that still vanishes off `L`
(`TauCeti.zeroOnePartSobolevL_mem_aeZeroOff`). This gives a continuous linear extension by zero
into the `(0,1)`-forms (`TauCeti.zeroOneExtendByZeroL`). Its chart-`i` data are the complex
antilinear part of the chart-`i` data defined by `g`, so they are those data when these are
complex antilinear almost everywhere (`TauCeti.value_zeroOneExtendByZeroL_ae`).

Over a `C¹` bundle the one-forms have extension by zero at orders `k ≤ 1`, with respect to
Lebesgue measure (`TauCeti.SobolevSection.hasExtensionByZero_of_le_one` for `A.tangentHom`), so
the hypothesis can be discharged for the `Lᵖ` and `W^{1,p}` `(0,1)`-forms.

This is how a functional on the `Lᵖ` `(0,1)`-forms is tested against chart data over one chart,
for instance to bound the covector field representing it in that chart.

## Main definitions

* `TauCeti.zeroOneExtendByZeroL`: the extension by zero of chart-`i` data vanishing off `L` to a
  `(0,1)`-form.

## Main results

* `TauCeti.sum_zeroOnePartSobolevL_contMDiffSMulL_eq_self`: a `(0,1)`-form is the sum of the
  `(0,1)`-projections of its products with a partition of unity.
* `TauCeti.zeroOnePartSobolevL_mem_aeZeroOff`: the `(0,1)`-projection preserves vanishing off a
  set.
* `TauCeti.zeroOneExtendByZeroL_mem_aeZeroOff`: the extension vanishes off `L`.
* `TauCeti.chartValueL_zeroOneExtendByZeroL_ae`: its chart-`i` data are the complex antilinear
  part of the data defined by `g`.
* `TauCeti.value_zeroOneExtendByZeroL_ae`: for complex antilinear data, its chart-`i` components
  have the values of `g`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.2.3 (the cokernel step, which tests functionals on forms supported in one chart).
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SobolevSection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealZeroOneExtension : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable {A : FiniteBundleAtlas ℂ M F V} {μ : Measure ℂ} [μ.IsAddHaarMeasure] {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {k : ℕ}

/-- The `(0,1)`-projection of a one-form vanishing off `L` vanishes off `L`. -/
theorem zeroOnePartSobolevL_mem_aeZeroOff {L : Set M}
    {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k}
    (hw : w ∈ aeZeroOff (A.tangentHom 𝓘(ℝ, ℂ)) μ p k L) :
    (zeroOnePartSobolevL A μ p k w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) ∈
      aeZeroOff (A.tangentHom 𝓘(ℝ, ℂ)) μ p k L := mem_aeZeroOff.2 fun i ↦ by
  filter_upwards [mem_aeZeroOff.1 hw i, chartValueL_zeroOnePartSobolevL_ae w i] with y hy hz hL
  rw [hz, hy hL, map_zero]

/-- **Localizing `(0,1)`-forms.** If the smooth functions `χᵢ` sum to `1`, every `(0,1)`-form `w` is
the sum of the `(0,1)`-projections of the one-forms `χᵢ w`. -/
theorem sum_zeroOnePartSobolevL_contMDiffSMulL_eq_self {ι : Type*} [Fintype ι] {χ : ι → M → ℝ}
    (hχ : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (χ i)) (h1 : ∀ x, ∑ i, χ i x = 1)
    (w : zeroOneSobolevSections A μ p k) :
    ∑ i, zeroOnePartSobolevL A μ p k (contMDiffSMulL (A.tangentHom 𝓘(ℝ, ℂ)) μ p k (hχ i) w) =
      w := by
  rw [← map_sum, sum_contMDiffSMulL_eq_self_of_sum_eq_one _ h1, zeroOnePartSobolevL_coe]

variable (h : HasExtensionByZero (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) {i : Fin A.n} {L : Set M}
  (hL : IsClosed L) (hLi : L ⊆ A.dom i)

/-- **Extension by zero of `(0,1)`-forms.** Chart-`i` Sobolev data of one-forms vanishing off a
closed subset `L` of the domain of chart `i` extend by zero to a `V`-valued one-form, whose
`(0,1)`-projection is a `(0,1)`-form vanishing off `L`
(`TauCeti.zeroOneExtendByZeroL_mem_aeZeroOff`) with chart-`i` data the complex antilinear part of
the given data (`TauCeti.chartValueL_zeroOneExtendByZeroL_ae`). -/
def zeroOneExtendByZeroL :
    chartAeZeroOff (A.tangentHom 𝓘(ℝ, ℂ)) μ p k i L →L[ℝ] zeroOneSobolevSections A μ p k :=
  (zeroOnePartSobolevL A μ p k).comp (extendByZeroL h hL hLi)

theorem zeroOneExtendByZeroL_apply (g : chartAeZeroOff (A.tangentHom 𝓘(ℝ, ℂ)) μ p k i L) :
    zeroOneExtendByZeroL h hL hLi g = zeroOnePartSobolevL A μ p k (extendByZeroL h hL hLi g) :=
  (rfl)

/-- The extension by zero of `(0,1)`-forms vanishes off `L`. -/
theorem zeroOneExtendByZeroL_mem_aeZeroOff (g : chartAeZeroOff (A.tangentHom 𝓘(ℝ, ℂ)) μ p k i L) :
    (zeroOneExtendByZeroL h hL hLi g : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) ∈
      aeZeroOff (A.tangentHom 𝓘(ℝ, ℂ)) μ p k L :=
  zeroOnePartSobolevL_mem_aeZeroOff (extendByZeroL_mem_aeZeroOff h hL hLi g)

/-- The chart-`i` data of the extension by zero of `(0,1)`-forms are the complex antilinear part
of the data `∑ⱼ gⱼ • eⱼ` defined by the components `g` in the basis `Module.finBasis ℝ (ℂ →L[ℝ] F)`.
-/
theorem chartValueL_zeroOneExtendByZeroL_ae (g : chartAeZeroOff (A.tangentHom 𝓘(ℝ, ℂ)) μ p k i L) :
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i (zeroOneExtendByZeroL h hL hLi g)
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i)] fun y ↦
        complexAntilinearPartL (∑ j, Wkp.value k
          ((g : Fin (finrank ℝ (ℂ →L[ℝ] F)) → Wkp μ ((A.tangentHom 𝓘(ℝ, ℂ)).image i) p k) j) y •
            finBasis ℝ (ℂ →L[ℝ] F) j) := by
  filter_upwards [chartValueL_zeroOnePartSobolevL_ae (extendByZeroL h hL hLi g) i,
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL_apply_ae μ p k i
      (extendByZeroL h hL hLi g : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k)] with y h₁ h₂
  rw [zeroOneExtendByZeroL_apply, h₁, h₂]
  -- The chart index is `i : Fin A.n` in `extendByZeroL_apply_self` and an index of
  -- `(A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData` here, so the chart-`i` block is replaced by
  -- `congrArg`.
  exact congrArg (fun d ↦ complexAntilinearPartL (∑ j, Wkp.value k (d j) y •
    finBasis ℝ (ℂ →L[ℝ] F) j)) (extendByZeroL_apply_self h hL hLi g)

/-- **Antilinear data are preserved.** If the data defined by `g` are complex antilinear almost
everywhere, the chart-`i` components of the extension by zero of `(0,1)`-forms have the values of
`g`. -/
theorem value_zeroOneExtendByZeroL_ae (g : chartAeZeroOff (A.tangentHom 𝓘(ℝ, ℂ)) μ p k i L)
    (hg : ∀ᵐ y ∂μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i), ∀ v : ℂ,
      (∑ j, Wkp.value k
        ((g : Fin (finrank ℝ (ℂ →L[ℝ] F)) → Wkp μ ((A.tangentHom 𝓘(ℝ, ℂ)).image i) p k) j) y •
          finBasis ℝ (ℂ →L[ℝ] F) j) (Complex.I • v) =
        -(Complex.I • (∑ j, Wkp.value k
          ((g : Fin (finrank ℝ (ℂ →L[ℝ] F)) → Wkp μ ((A.tangentHom 𝓘(ℝ, ℂ)).image i) p k) j) y •
            finBasis ℝ (ℂ →L[ℝ] F) j) v))
    (c : Fin (finrank ℝ (ℂ →L[ℝ] F))) :
    (Wkp.value k (((zeroOneExtendByZeroL h hL hLi g : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) :
        (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.SobolevData μ p k) i c) : ℂ → ℝ)
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i)]
        Wkp.value k ((g : Fin (finrank ℝ (ℂ →L[ℝ] F)) →
          Wkp μ ((A.tangentHom 𝓘(ℝ, ℂ)).image i) p k) c) := by
  filter_upwards [chartValueL_zeroOneExtendByZeroL_ae h hL hLi g, hg,
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL_apply_ae μ p k i
      (zeroOneExtendByZeroL h hL hLi g :
        SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k)] with y h₁ h₂ h₃
  rw [ContinuousLinearMap.complexAntilinearPartL_eq_self_iff.2 h₂, h₃] at h₁
  simpa [Finsupp.single_apply] using
    congrArg (fun v ↦ (finBasis ℝ (ℂ →L[ℝ] F)).repr v c) h₁

end TauCeti
