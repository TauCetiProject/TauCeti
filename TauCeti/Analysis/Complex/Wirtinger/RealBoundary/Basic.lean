/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Topology.Algebra.Module.Star
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Green.HalfPlane
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Star
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Weak `\bar∂` equations with a real boundary condition

`HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η` is the weak form of `\bar∂ξ = η` on the closed
upper part `Ω ∩ {0 ≤ im}` of an open set `Ω ⊆ ℂ`, with the boundary condition that `ξ` is real
on the real axis imposed weakly. The coefficients lie in a complex Banach space `F` whose real
structure is its `star` operation, so that `x` is real when `star x = x`; for `F = ℂⁿ`, as
`Fin n → ℂ`, this is coordinatewise conjugation and the real vectors are `ℝⁿ`. A locally
integrable `ξ` has no values on the null real axis, so the boundary condition is not a pointwise
statement about `ξ`: it is encoded by the choice of test functions, which are smooth, complex
valued, compactly supported in `Ω`, real on the real axis, and need not vanish there. The
identity tested is the real part of the normalized equation of
`TauCeti.HasWeakConjWirtingerDerivOn`, integrated over the closed upper half-plane: this is
McDuff–Salamon (B.4.3) with `J = i` and the real pairing. The real part, and real-valuedness of
the tests on the axis, are both essential: for smooth data the identity has the boundary term
`-∫_ℝ ⟨φ, iξ⟩ ds`, which vanishes exactly because `φ` and `ξ` are real there.

## Main results

* `HasWeakConjWirtingerDerivRealBoundaryOn.completeSpace`, `.locallyIntegrableOn`,
  `.locallyIntegrableOn_deriv` and `.realPart_setIntegral_eq`: the components of the definition.
* `hasWeakConjWirtingerDerivRealBoundaryOn_zero`, `HasWeakConjWirtingerDerivRealBoundaryOn.add`,
  `.neg`, `.sub`, `.const_smul` and `.mono`: the solutions form a real vector space, local in `Ω`.
* `HasWeakConjWirtingerDerivRealBoundaryOn.of_tendsto`: closure under `L¹` convergence on
  compact subsets of `Ω ∩ {0 ≤ im}`.
* `TauCeti.setIntegral_im_nonneg_cauchyRiemann_smul_of_contDiffOn`: the half-plane integration by
  parts behind the weak formulation, for a map of class `C¹` on `Ω`, with its boundary term
  `-i ∫_ℝ χ ξ ds`.
* `TauCeti.hasWeakConjWirtingerDerivRealBoundaryOn_iff_of_contDiffOn`: a map of class `C¹` on `Ω`
  solves the weak real-boundary equation with its classical `\bar∂` derivative as right-hand side
  exactly when it is real on `Ω ∩ ℝ`, and
  `TauCeti.hasWeakConjWirtingerDerivRealBoundaryOn_zero_iff_of_differentiableOn` is its
  holomorphic case.
* Checks: `z²` solves the weak real-boundary equation with `η = 0`; `i z` and the constant `i`,
  which are holomorphic but not real on `ℝ`, do not.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications **52**, 2012, Appendix B.4, equation (B.4.3).
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace Set Filter Topology LineDeriv
open scoped ContDiff Distributions ComplexConjugate ComplexStarModule

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] {Ω : Opens ℂ}

private theorem isClosed_im_nonneg : IsClosed {z : ℂ | 0 ≤ z.im} :=
  isClosed_le continuous_const Complex.continuous_im

private theorem measurableSet_im_nonneg : MeasurableSet {z : ℂ | 0 ≤ z.im} :=
  isClosed_im_nonneg.measurableSet

variable [NormedSpace ℂ F] [StarAddMonoid F] [StarModule ℂ F] {ξ η : ℂ → F}

/-! ### The weak formulation up to a real boundary -/

/-- The weak equation `\bar∂ξ = η` on the closed upper part `Ω ∩ {0 ≤ im}` of `Ω`, with the
boundary condition that `ξ` is real on the real axis imposed weakly, where `x : F` is real when
`star x = x`. The source and the derivative are locally integrable up to the boundary, and the
real part of the normalized identity of `HasWeakConjWirtingerDerivOn`, integrated over `0 ≤ im`,
holds for every smooth complex test function compactly supported in `Ω` and real on the real
axis. No pointwise condition on `ξ` along the axis is stated: the restriction of the tests to
functions real on the axis, together with taking real parts, is what encodes the boundary
condition. -/
def HasWeakConjWirtingerDerivRealBoundaryOn (Ω : Opens ℂ) (ξ η : ℂ → F) : Prop :=
  CompleteSpace F ∧ LocallyIntegrableOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ∧
    LocallyIntegrableOn η ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ∧
    ∀ χ : 𝓓(Ω, ℂ), (∀ x : ℝ, (χ (x : ℂ)).im = 0) →
      ℜ (∫ z in {z : ℂ | 0 ≤ z.im},
          (lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I) • ξ z) =
        -(2 : ℝ) • ℜ (∫ z in {z : ℂ | 0 ≤ z.im}, χ z • η z)

/-- The defining conditions, usable without unfolding the definition. -/
theorem hasWeakConjWirtingerDerivRealBoundaryOn_iff :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η ↔
      CompleteSpace F ∧ LocallyIntegrableOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ∧
        LocallyIntegrableOn η ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ∧
        ∀ χ : 𝓓(Ω, ℂ), (∀ x : ℝ, (χ (x : ℂ)).im = 0) →
          ℜ (∫ z in {z : ℂ | 0 ≤ z.im},
              (lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I) • ξ z) =
            -(2 : ℝ) • ℜ (∫ z in {z : ℂ | 0 ≤ z.im}, χ z • η z) := Iff.rfl

namespace HasWeakConjWirtingerDerivRealBoundaryOn

/-- The coefficient space of a weak real-boundary equation is complete. -/
theorem completeSpace (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) : CompleteSpace F :=
  h.1

/-- The source is locally integrable up to the boundary. -/
theorem locallyIntegrableOn (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) :
    LocallyIntegrableOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
  h.2.1

/-- The right-hand side is locally integrable up to the boundary. -/
theorem locallyIntegrableOn_deriv (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) :
    LocallyIntegrableOn η ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
  h.2.2.1

/-- The tested identity, for a test function real on the real axis. -/
theorem realPart_setIntegral_eq (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η)
    (χ : 𝓓(Ω, ℂ)) (hχ : ∀ x : ℝ, (χ (x : ℂ)).im = 0) :
    ℜ (∫ z in {z : ℂ | 0 ≤ z.im},
        (lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I) • ξ z) =
      -(2 : ℝ) • ℜ (∫ z in {z : ℂ | 0 ≤ z.im}, χ z • η z) :=
  h.2.2.2 χ hχ

/-- Almost-everywhere replacement on `Ω ∩ {0 ≤ im}` preserves the source of the weak
real-boundary equation. -/
theorem congr_ae {ξ' : ℂ → F} (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η)
    (hξ : ξ =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] ξ') :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ' η := by
  refine ⟨h.1, h.2.1.congr hξ, h.2.2.1, fun χ hχ ↦ ?_⟩
  rw [← h.2.2.2 χ hχ]
  congr 1
  refine setIntegral_congr_ae measurableSet_im_nonneg ?_
  filter_upwards [(ae_restrict_iff' (Ω.isOpen.measurableSet.inter measurableSet_im_nonneg)).1 hξ]
    with z hz hz0
  by_cases hzΩ : z ∈ (Ω : Set ℂ)
  · rw [hz ⟨hzΩ, hz0⟩]
  · have ht : z ∉ tsupport (χ : ℂ → ℂ) := fun h' ↦ hzΩ (χ.tsupport_subset h')
    simp [lineDeriv_of_notMem_tsupport ht]

/-- Almost-everywhere replacement on `Ω ∩ {0 ≤ im}` preserves the right-hand side of the weak
real-boundary equation. -/
theorem congr_ae_deriv {η' : ℂ → F} (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η)
    (hη : η =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] η') :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η' := by
  refine ⟨h.1, h.2.1, h.2.2.1.congr hη, fun χ hχ ↦ ?_⟩
  rw [h.2.2.2 χ hχ]
  congr 2
  refine setIntegral_congr_ae measurableSet_im_nonneg ?_
  filter_upwards [(ae_restrict_iff' (Ω.isOpen.measurableSet.inter measurableSet_im_nonneg)).1 hη]
    with z hz hz0
  by_cases hzΩ : z ∈ (Ω : Set ℂ)
  · rw [hz ⟨hzΩ, hz0⟩]
  · rw [image_eq_zero_of_notMem_tsupport (fun h' ↦ hzΩ (χ.tsupport_subset h'))]
    simp

end HasWeakConjWirtingerDerivRealBoundaryOn

/-! ### Linear structure and locality -/

omit [StarAddMonoid F] [StarModule ℂ F] in
/-- A complex test function pairs integrably over the closed upper half-plane with a map locally
integrable up to the boundary. -/
private theorem integrable_smul_of_locallyIntegrableOn {w : ℂ → F}
    (hw : LocallyIntegrableOn w ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (ψ : 𝓓(Ω, ℂ)) :
    Integrable (fun z ↦ ψ z • w z) (volume.restrict {z : ℂ | 0 ≤ z.im}) := by
  simpa using ψ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] F →L[ℝ] F)
    (hw.restrict_of_inter Ω.isOpen isClosed_im_nonneg)

omit [StarAddMonoid F] [StarModule ℂ F] in
/-- The Cauchy–Riemann pairing of the weak formulation is integrable over the closed upper
half-plane. -/
private theorem integrable_cauchyRiemann_smul {w : ℂ → F}
    (hw : LocallyIntegrableOn w ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (χ : 𝓓(Ω, ℂ)) :
    Integrable (fun z ↦ (lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I) • w z)
      (volume.restrict {z : ℂ | 0 ≤ z.im}) := by
  simpa using integrable_smul_of_locallyIntegrableOn hw (∂_{(1 : ℂ)} χ + I • ∂_{I} χ)

/-- The zero function solves the weak real-boundary equation with right-hand side zero. -/
@[simp]
theorem hasWeakConjWirtingerDerivRealBoundaryOn_zero [CompleteSpace F] :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω (0 : ℂ → F) 0 :=
  ⟨inferInstance, locallyIntegrableOn_zero, locallyIntegrableOn_zero, fun _ _ ↦ by simp⟩

namespace HasWeakConjWirtingerDerivRealBoundaryOn

/-- Solutions of the weak real-boundary equation add. -/
theorem add {ξ₁ ξ₂ η₁ η₂ : ℂ → F} (h₁ : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ₁ η₁)
    (h₂ : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ₂ η₂) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω (ξ₁ + ξ₂) (η₁ + η₂) := by
  refine ⟨h₁.1, h₁.2.1.add h₂.2.1, h₁.2.2.1.add h₂.2.2.1, fun χ hχ ↦ ?_⟩
  simp only [Pi.add_apply, smul_add]
  rw [integral_add (integrable_cauchyRiemann_smul h₁.2.1 χ)
      (integrable_cauchyRiemann_smul h₂.2.1 χ),
    integral_add (integrable_smul_of_locallyIntegrableOn h₁.2.2.1 χ)
      (integrable_smul_of_locallyIntegrableOn h₂.2.2.1 χ), map_add, map_add,
    h₁.2.2.2 χ hχ, h₂.2.2.2 χ hχ, smul_add]

/-- Real multiples of solutions of the weak real-boundary equation are solutions. Complex
multiples are not: `i` times a solution real on `ℝ` is imaginary there. -/
theorem const_smul (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) (c : ℝ) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω (c • ξ) (c • η) := by
  refine ⟨h.1, h.2.1.smul c, h.2.2.1.smul c, fun χ hχ ↦ ?_⟩
  simp only [Pi.smul_apply, smul_comm _ c]
  rw [integral_smul, integral_smul, map_smul, map_smul, h.2.2.2 χ hχ, smul_comm]

/-- Negatives of solutions of the weak real-boundary equation are solutions. -/
theorem neg (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω (-ξ) (-η) := by
  simpa using h.const_smul (-1 : ℝ)

/-- Solutions of the weak real-boundary equation subtract. -/
theorem sub {ξ₁ ξ₂ η₁ η₂ : ℂ → F} (h₁ : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ₁ η₁)
    (h₂ : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ₂ η₂) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω (ξ₁ - ξ₂) (η₁ - η₂) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

/-- The weak real-boundary equation restricts to smaller open sets. -/
theorem mono {Ω' : Opens ℂ} (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) (hΩ : Ω' ≤ Ω) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω' ξ η :=
  ⟨h.1, h.2.1.mono_set (inter_subset_inter_left _ hΩ),
    h.2.2.1.mono_set (inter_subset_inter_left _ hΩ),
    fun χ hχ ↦ h.2.2.2 ⟨χ, χ.contDiff, χ.hasCompactSupport, χ.tsupport_subset.trans hΩ⟩ hχ⟩

end HasWeakConjWirtingerDerivRealBoundaryOn

/-! ### Limits -/

omit [StarAddMonoid F] [StarModule ℂ F] in
/-- `L¹` convergence on compact subsets of `Ω ∩ {0 ≤ im}` passes to the half-plane pairings with
a complex test function. -/
private theorem tendsto_setIntegral_im_nonneg_smul {ι : Type*} {l : Filter ι} {ws : ι → ℂ → F}
    {w : ℂ → F} (hws : ∀ᶠ i in l, LocallyIntegrableOn (ws i) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hw : LocallyIntegrableOn w ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (ht : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun i ↦ ∫ z in K, ‖ws i z - w z‖) l (𝓝 0))
    (ψ : 𝓓(Ω, ℂ)) :
    Tendsto (fun i ↦ ∫ z in {z : ℂ | 0 ≤ z.im}, ψ z • ws i z) l
      (𝓝 (∫ z in {z : ℂ | 0 ≤ z.im}, ψ z • w z)) := by
  refine TestFunction.tendsto_integral_smul_of_tendsto_setIntegral_norm_sub
    (hws.mono fun i hi ↦ hi.restrict_of_inter Ω.isOpen isClosed_im_nonneg)
    (hw.restrict_of_inter Ω.isOpen isClosed_im_nonneg) (fun K hKΩ hK ↦ ?_) ψ
  rw [Measure.restrict_restrict hK.isClosed.measurableSet]
  exact ht _ (inter_subset_inter_left _ hKΩ) (hK.inter_right isClosed_im_nonneg)

/-- **Closure under `L¹` limits up to the boundary.** If `ξᵢ`, `ηᵢ` are eventually solutions and
converge to locally integrable `ξ`, `η` in `L¹` on every compact subset of `Ω ∩ {0 ≤ im}`, then
`ξ`, `η` is a solution. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.of_tendsto [ContinuousStar F] {ι : Type*}
    {l : Filter ι} [l.NeBot] {ξs ηs : ι → ℂ → F}
    (h : ∀ᶠ i in l, HasWeakConjWirtingerDerivRealBoundaryOn Ω (ξs i) (ηs i))
    (hξ : LocallyIntegrableOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hη : LocallyIntegrableOn η ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξt : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun i ↦ ∫ z in K, ‖ξs i z - ξ z‖) l (𝓝 0))
    (hηt : ∀ K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, IsCompact K →
      Tendsto (fun i ↦ ∫ z in K, ‖ηs i z - η z‖) l (𝓝 0)) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η := by
  obtain ⟨i₀, hi₀⟩ := h.exists
  refine ⟨hi₀.completeSpace, hξ, hη, fun χ hχ ↦ ?_⟩
  have hL := (continuous_selfAdjointPart ℝ F).continuousAt.tendsto.comp
    (tendsto_setIntegral_im_nonneg_smul (h.mono fun i hi ↦ hi.locallyIntegrableOn) hξ hξt
      (∂_{(1 : ℂ)} χ + I • ∂_{I} χ))
  have hR := ((continuous_selfAdjointPart ℝ F).continuousAt.tendsto.comp
    (tendsto_setIntegral_im_nonneg_smul (h.mono fun i hi ↦ hi.locallyIntegrableOn_deriv) hη hηt
      χ)).const_smul (-(2 : ℝ))
  simp only [add_apply, TestFunction.lineDerivOp_apply, smul_apply,
    smul_eq_mul] at hL
  exact tendsto_nhds_unique hL
    (hR.congr' (h.mono fun i hi ↦ (hi.realPart_setIntegral_eq χ hχ).symm))

/-! ### Maps of class `C¹` up to the boundary -/

omit [StarAddMonoid F] [StarModule ℂ F] in
/-- **Half-plane integration by parts for the weak formulation.** For a map `ξ` of class `C¹` on
`Ω` and a complex test function `χ` on `Ω`,
`∫_{0 ≤ im} (∂_s χ + i ∂_t χ) ξ = -2 ∫_{0 ≤ im} χ \bar∂ξ - i ∫_ℝ χ ξ ds`. -/
theorem setIntegral_im_nonneg_cauchyRiemann_smul_of_contDiffOn [CompleteSpace F]
    (χ : 𝓓(Ω, ℂ)) (hξ : ContDiffOn ℝ 1 ξ Ω) :
    ∫ z in {z : ℂ | 0 ≤ z.im},
        (lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I) • ξ z =
      -(2 : ℂ) • (∫ z in {z : ℂ | 0 ≤ z.im}, χ z • conjWirtingerDeriv ξ z 1) -
        I • ∫ s : ℝ, χ s • ξ s := by
  set L : F →L[ℝ] ℂ →L[ℝ] F := (ContinuousLinearMap.lsmul ℝ ℂ).flip
  set g : ℂ → F := fun z ↦ L (ξ z) (χ z)
  have hgv (z : ℂ) : g z = χ z • ξ z := by simp [g, L]
  have hχd : Differentiable ℝ (χ : ℂ → ℂ) := χ.contDiff.differentiable (by simp)
  have hg : ContDiff ℝ 1 g := L.contDiff_of_tsupport_subset_right hξ
    (χ.contDiff.of_le (by simp)).contDiffOn Ω.isOpen χ.tsupport_subset
  have hgc : HasCompactSupport g := χ.hasCompactSupport.mono fun z hz h0 ↦ hz (by simp [g, h0])
  have hgd (z v : ℂ) :
      fderiv ℝ g z v = lineDeriv ℝ (χ : ℂ → ℂ) z v • ξ z + χ z • fderiv ℝ ξ z v := by
    rw [L.fderiv_of_tsupport_subset_right (hξ.differentiableOn one_ne_zero) hχd Ω.isOpen
      χ.tsupport_subset, χ.lineDeriv_eq_fderiv]
    simp [L]
  have hint (v : ℂ) : Integrable fun z ↦ fderiv ℝ g z v :=
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hgc.fderiv_apply (𝕜 := ℝ) v)
  have hcw : ContinuousOn (fun z ↦ conjWirtingerDeriv ξ z 1) Ω := by
    have hD := hξ.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
    simp only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one]
    exact continuousOn_const.smul ((hD.clm_apply continuousOn_const).add
      (continuousOn_const.smul (hD.clm_apply continuousOn_const)))
  have hη : Integrable fun z ↦ χ z • conjWirtingerDeriv ξ z 1 :=
    ((χ.continuous.continuousOn.smul hcw).continuous_of_tsupport_subset Ω.isOpen
      ((tsupport_smul_subset_left _ _).trans χ.tsupport_subset)).integrable_of_hasCompactSupport
      (χ.hasCompactSupport.mono fun z hz h0 ↦ hz (by simp [h0]))
  have hpt (z : ℂ) :
      (lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I) • ξ z =
        (fderiv ℝ g z 1 + I • fderiv ℝ g z I) - (2 : ℂ) • (χ z • conjWirtingerDeriv ξ z 1) := by
    rw [hgd, hgd, conjWirtingerDeriv_apply, smul_eq_mul, mul_one]
    module
  have hae : {z : ℂ | 0 < z.im} =ᵐ[volume] {z : ℂ | 0 ≤ z.im} :=
    (Complex.setOf_le_im_ae_eq 0).symm
  simp_rw [hpt]
  rw [← setIntegral_congr_set hae, ← setIntegral_congr_set hae,
    integral_sub (f := fun z ↦ fderiv ℝ g z 1 + I • fderiv ℝ g z I)
      (g := fun z ↦ (2 : ℂ) • (χ z • conjWirtingerDeriv ξ z 1))
      ((hint 1).add ((hint I).smul I)).integrableOn (hη.smul (2 : ℂ)).integrableOn,
    integral_add (f := fun z ↦ fderiv ℝ g z 1) (g := fun z ↦ I • fderiv ℝ g z I)
      (hint 1).integrableOn ((hint I).smul I).integrableOn, integral_smul,
    integral_smul, setIntegral_im_pos_fderiv_one_eq_zero hg hgc,
    setIntegral_im_pos_fderiv_I_eq_neg_integral hg hgc]
  simp only [hgv]
  module

/-- The tested identity for a map of class `C¹` on `Ω` with its classical `\bar∂` derivative: the
two sides differ by the imaginary part of the boundary pairing `∫_ℝ χ ξ ds`. -/
private theorem realPart_setIntegral_cauchyRiemann_smul_of_contDiffOn [CompleteSpace F]
    (χ : 𝓓(Ω, ℂ)) (hξ : ContDiffOn ℝ 1 ξ Ω) :
    ℜ (∫ z in {z : ℂ | 0 ≤ z.im},
        (lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I) • ξ z) =
      -(2 : ℝ) • ℜ (∫ z in {z : ℂ | 0 ≤ z.im}, χ z • conjWirtingerDeriv ξ z 1) +
        ℑ (∫ s : ℝ, χ s • ξ s) := by
  have h2 : -(2 : ℂ) = ((-(2 : ℝ) : ℝ) : ℂ) := by norm_num
  rw [setIntegral_im_nonneg_cauchyRiemann_smul_of_contDiffOn χ hξ, sub_eq_add_neg, map_add,
    map_neg, realPart_I_smul, neg_neg, h2, Complex.coe_smul, map_smul]

/-- **The `C¹` boundary criterion.** A map of class `C¹` on `Ω` solves the weak real-boundary
equation with its classical `\bar∂` derivative as right-hand side exactly when it is real on
`Ω ∩ ℝ`. -/
theorem hasWeakConjWirtingerDerivRealBoundaryOn_iff_of_contDiffOn [CompleteSpace F]
    [ContinuousStar F] (hξ : ContDiffOn ℝ 1 ξ Ω) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ (fun z ↦ conjWirtingerDeriv ξ z 1) ↔
      ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x := by
  have him (Y : F) : (ℑ Y : F) = 0 ↔ star Y = Y := by
    rw [imaginaryPart_apply_coe, smul_eq_zero, smul_eq_zero, sub_eq_zero, eq_comm (a := Y)]
    simp [I_ne_zero]
  constructor
  · intro h x hx
    by_contra hne
    set d : ℂ → F := fun z ↦ ξ z - star (ξ z)
    have hdx : d x ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℝ (d x) (norm_ne_zero_iff.2 hdx)
    have hd : ContinuousOn d Ω :=
      hξ.continuousOn.sub (continuous_star.comp_continuousOn hξ.continuousOn)
    have hU : IsOpen ((Ω : Set ℂ) ∩ d ⁻¹' {y | 0 < ℓ y}) :=
      hd.isOpen_inter_preimage Ω.isOpen (isOpen_lt continuous_const ℓ.continuous)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x
      ⟨hx, show 0 < ℓ (d x) by rw [hℓ]; exact_mod_cast norm_pos_iff.2 hdx⟩
    let b : ContDiffBump (x : ℂ) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
    have hbs : tsupport b ⊆ Metric.ball (x : ℂ) ε := by
      rw [b.tsupport_eq]
      exact Metric.closedBall_subset_ball (by simp only [b]; linarith)
    have hbΩ : tsupport b ⊆ Ω := hbs.trans fun z hz ↦ (hball hz).1
    let χ : 𝓓(Ω, ℂ) := ⟨fun z ↦ (b z : ℂ), ofRealCLM.contDiff.comp b.contDiff,
      b.hasCompactSupport.comp_left ofReal_zero, (tsupport_comp_subset ofReal_zero _).trans hbΩ⟩
    have hχv (z : ℂ) : χ z = (b z : ℂ) := rfl
    -- The boundary pairing of `χ` with `ξ` is real.
    have hY : star (∫ s : ℝ, χ s • ξ s) = ∫ s : ℝ, χ s • ξ s := by
      have key := h.realPart_setIntegral_eq χ fun s ↦ by simp [hχv]
      rw [realPart_setIntegral_cauchyRiemann_smul_of_contDiffOn χ hξ, add_eq_left] at key
      exact (him _).1 (congrArg Subtype.val key)
    -- Testing it against `ℓ ∘ (id - star)` gives a positive integral.
    let ℓ' : F →L[ℝ] ℝ :=
      ℓ.comp (ContinuousLinearMap.id ℝ F - (starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap)
    have hℓ' (z : ℂ) : ℓ' (χ z • ξ z) = b z * ℓ (d z) := by
      simp [ℓ', hχv, d, Complex.coe_smul]
    have hcont : Continuous fun z : ℂ ↦ χ z • ξ z :=
      (χ.continuous.continuousOn.smul hξ.continuousOn).continuous_of_tsupport_subset Ω.isOpen
        ((tsupport_smul_subset_left _ _).trans χ.tsupport_subset)
    have hcpt : HasCompactSupport fun s : ℝ ↦ χ s • ξ s :=
      (χ.hasCompactSupport.comp_isClosedEmbedding
        Complex.isometry_ofReal.isClosedEmbedding).mono fun s hs h0 ↦ hs (by simp_all)
    have hint : Integrable fun s : ℝ ↦ χ s • ξ s :=
      (hcont.comp continuous_ofReal).integrable_of_hasCompactSupport hcpt
    have hzero : ∫ s : ℝ, ℓ' (χ s • ξ s) = 0 := by
      rw [ℓ'.integral_comp_comm hint]
      simp [ℓ', hY]
    have hpos : 0 < ∫ s : ℝ, ℓ' (χ s • ξ s) := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := x)
        (ℓ'.continuous.comp (hcont.comp continuous_ofReal)) (hcpt.comp_left (map_zero ℓ'))
        (fun s ↦ ?_) ?_
      · rw [hℓ']
        by_cases hs : b s = 0
        · simp [hs]
        · exact mul_nonneg b.nonneg (hball (hbs (subset_tsupport _ hs))).2.le
      · rw [hℓ', b.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity)), one_mul,
          hℓ]
        exact_mod_cast (norm_pos_iff.2 hdx).ne'
    exact hpos.ne' hzero
  · intro hreal
    have hD := hξ.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
    have hcw : ContinuousOn (fun z ↦ conjWirtingerDeriv ξ z 1) Ω := by
      simp only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one]
      exact continuousOn_const.smul ((hD.clm_apply continuousOn_const).add
        (continuousOn_const.smul (hD.clm_apply continuousOn_const)))
    refine ⟨inferInstance,
      (hξ.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet).mono_set inter_subset_left,
      (hcw.locallyIntegrableOn Ω.isOpen.measurableSet).mono_set inter_subset_left,
      fun χ hχ ↦ ?_⟩
    rw [realPart_setIntegral_cauchyRiemann_smul_of_contDiffOn χ hξ, add_eq_left]
    refine Subtype.ext ((him _).2 ?_)
    rw [← integral_star]
    refine integral_congr_ae (.of_forall fun s ↦ ?_)
    by_cases hs : (s : ℂ) ∈ Ω
    · dsimp only
      rw [star_smul, hreal s hs, Complex.star_def, Complex.conj_eq_iff_im.2 (hχ s)]
    · simp [image_eq_zero_of_notMem_tsupport fun h' ↦ hs (χ.tsupport_subset h')]

/-- **The holomorphic boundary criterion.** A map holomorphic on `Ω` solves the weak
real-boundary equation with `η = 0` exactly when it is real on `Ω ∩ ℝ`. -/
theorem hasWeakConjWirtingerDerivRealBoundaryOn_zero_iff_of_differentiableOn [CompleteSpace F]
    [ContinuousStar F] (hξ : DifferentiableOn ℂ ξ Ω) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ 0 ↔ ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x := by
  have he : (fun z ↦ conjWirtingerDeriv ξ z 1)
      =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] 0 := by
    rw [Filter.EventuallyEq,
      ae_restrict_iff' (Ω.isOpen.measurableSet.inter measurableSet_im_nonneg)]
    filter_upwards [] with z hz
    simp [(hξ.differentiableAt (Ω.isOpen.mem_nhds hz.1)).conjWirtingerDeriv_eq_zero]
  rw [← hasWeakConjWirtingerDerivRealBoundaryOn_iff_of_contDiffOn
    ((hξ.contDiffOn Ω.isOpen).restrict_scalars ℝ)]
  exact ⟨fun h ↦ h.congr_ae_deriv he.symm, fun h ↦ h.congr_ae_deriv he⟩

/-! ### Checks -/

/-- **Check.** `z ↦ z²` is real on `ℝ` and solves the weak real-boundary equation with `η = 0`. -/
theorem hasWeakConjWirtingerDerivRealBoundaryOn_sq :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun z : ℂ ↦ z ^ 2) 0 :=
  (hasWeakConjWirtingerDerivRealBoundaryOn_zero_iff_of_differentiableOn
    (differentiable_id.pow 2).differentiableOn).2 fun x _ ↦ by simp

/-- **Check.** `z ↦ i z` is holomorphic but imaginary on `ℝ`, and does not solve the weak
real-boundary equation on any `Ω` meeting `ℝ` away from `0`. -/
theorem not_hasWeakConjWirtingerDerivRealBoundaryOn_I_mul {x : ℝ} (hx : (x : ℂ) ∈ Ω)
    (hx0 : x ≠ 0) : ¬ HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun z : ℂ ↦ I * z) 0 := by
  rw [hasWeakConjWirtingerDerivRealBoundaryOn_zero_iff_of_differentiableOn
    (by fun_prop : DifferentiableOn ℂ (fun z : ℂ ↦ I * z) Ω)]
  intro h
  have := congrArg Complex.im (h x hx)
  simp at this
  exact hx0 (by linarith)

/-- **Check.** The constant `i` does not solve the weak real-boundary equation on any `Ω`
meeting `ℝ`. -/
theorem not_hasWeakConjWirtingerDerivRealBoundaryOn_const_I {x : ℝ} (hx : (x : ℂ) ∈ Ω) :
    ¬ HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun _ : ℂ ↦ I) 0 := by
  rw [hasWeakConjWirtingerDerivRealBoundaryOn_zero_iff_of_differentiableOn
    (differentiableOn_const I)]
  intro h
  have := congrArg Complex.im (h x hx)
  norm_num [Complex.star_def] at this

end TauCeti
