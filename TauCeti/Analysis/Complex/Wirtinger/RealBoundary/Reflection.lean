/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Weyl
public import TauCeti.Analysis.Complex.Conformal.Reflection.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.Algebra.Module.Star
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Complex.Wirtinger.Regularity
import TauCeti.Analysis.Sobolev.Local.Morrey
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Star
import TauCeti.MeasureTheory.Measure.Haar.HalfSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Green.HalfPlane
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Analysis.Complex.Wirtinger.Similarity.Examples


/-!
# Weak `\bar∂` equations with a real boundary condition, and weak Schwarz reflection

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

The reflection used throughout is `TauCeti.starSchwarzReflection ξ` from
`Analysis/Complex/Conformal/Reflection/Basic.lean`: `ξ` on `0 ≤ im`, and `star (ξ (conj z))`
below the axis; for `F = ℂ` it is `TauCeti.schwarzReflection`.

A map `C¹` up to the axis that solves the equation off the axis and is pointwise real on it
satisfies the weak real-boundary equation
(`hasWeakConjWirtingerDerivRealBoundaryOn_of_contDiffOn`). The half-plane integration-by-parts
identity retains the boundary integral; its real part vanishes on admissible tests. This also
provides the nontrivial examples `z²` and `z e^{-conj z}`.

## Main results

* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.hasWeakConjWirtingerDerivOn_interior`: away
  from the real axis it is the distributional equation of `TauCeti.HasWeakConjWirtingerDerivOn`.
* `TauCeti.MemLpLoc.starSchwarzReflection` and `TauCeti.locallyIntegrableOn_starSchwarzReflection`:
  local `Lᵖ` bounds and local integrability up to the boundary pass to the reflection on the
  doubled domain.
* `HasWeakConjWirtingerDerivRealBoundaryOn.hasWeakConjWirtingerDerivOn_starSchwarzReflection`:
  on a conjugation-invariant open set, the reflections of a weak solution with real boundary
  values solve the distributional equation `\bar∂ (Rξ) = Rη` on the doubled domain.
* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.exists_differentiableOn_ae_eq`: **weak
  Schwarz reflection**. With finite-dimensional coefficients and `η = 0`, `ξ` agrees almost
  everywhere on `Ω ∩ {0 ≤ im}` with a map holomorphic on all of `Ω`, real on `Ω ∩ ℝ` and
  satisfying `v (conj z) = star (v z)`. It is a weak analogue of
  `TauCeti.differentiableOn_schwarzReflection_of_symmetric`. The boundary-term computation
  below supplies the classical-to-weak step for maps `C¹` up to the axis. Recovering the full
  continuity-only statement would still require the boundary-term computation for data merely
  continuous up to the axis.
* `HasWeakConjWirtingerDerivRealBoundaryOn.mono`: restriction to a smaller open domain.
* `HasWeakConjWirtingerDerivRealBoundaryOn.star_eq_of_continuousOn`: continuous weak solutions
  with finite-dimensional coefficients and locally `Lᵖ` data for `p > 2` are pointwise real on
  the real axis.
* `HasWeakConjWirtingerDerivRealBoundaryOn.star_eq_of_continuousOn_clm`: the pointwise boundary
  conclusion for the coefficient-field equation `∂ₛξ + i ∂ₜξ + C ξ = 0`.
* `TauCeti.setIntegral_im_nonneg_lineDeriv_add_I_mul_smul_eq`: integration by parts for data
  `C¹` on `Ω ∩ {0 ≤ im}` solving the equation on `Ω ∩ {0 < im}`, retaining the boundary integral.
* `TauCeti.hasWeakConjWirtingerDerivRealBoundaryOn_of_contDiffOn`: a solution `C¹` up to the
  axis with complete coefficient space and pointwise real boundary values satisfies the weak
  real-boundary equation.
* Check: the even reflection `s + i|t|`, which omits the conjugation, is not a weak solution
  below the axis. The companion check that the reflection of `z` is `z` is
  `TauCeti.starSchwarzReflection_id`.
* Check: `TauCeti.not_hasWeakConjWirtingerDerivRealBoundaryOn_const_I_of_memLpLoc` excludes the
  constant `i` for every locally `Lᵖ` right-hand side with `p > 2`, on any domain containing a
  real point.

For finite-dimensional coefficients and data locally `Lᵖ` up to the axis with `p > 2`, a weak
real-boundary solution continuous on the closed half-domain is pointwise real along the axis.
Neither pointwise theorem requires a conjugation-invariant domain. The coefficient-field form
`star_eq_of_continuousOn_clm` is the case `η = -½ C ξ` for
`∂ₛξ + i ∂ₜξ + C ξ = 0`. Reflection, interior weak regularity and Morrey continuity identify
the limits from the two sides.

The proof of the reflection theorem splits a real test function `φ` on the doubled domain into
`φ + φ ∘ conj`, which is an admissible test, and `φ - φ ∘ conj`, which vanishes on the axis, so
that both it and its multiple by `i` are admissible; the lower half-plane contributions are
moved to the upper one by the measure-preserving substitution `z ↦ conj z`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications **52**, 2012, Appendix B.4, equation (B.4.3).
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace Set Filter Topology
open scoped ContDiff Distributions ComplexConjugate ComplexStarModule

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] {Ω : Opens ℂ}

/-! ### Measure-theoretic preliminaries -/

private theorem measurableSet_im_nonneg : MeasurableSet {z : ℂ | 0 ≤ z.im} :=
  (isClosed_setOfPred_le_im 0).measurableSet

section LocallyIntegrable

variable [NormedSpace ℝ F] {p : ENNReal}

/-- Reflecting by a continuous linear map `L` below the real axis preserves local `Lᵖ` bounds up
to the boundary: if `f` is locally `Lᵖ` on `Ω ∩ {0 ≤ im}`, then the map equal to `f` on
`0 ≤ im` and to `L (f (conj z))` below is locally `Lᵖ` on `Ω`. -/
theorem MemLpLoc.ite_conj {Ω : Set ℂ} (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (L : F →L[ℝ] F)
    {f : ℂ → F} (hf : MemLpLoc p (Ω ∩ {z | 0 ≤ z.im}) f) :
    MemLpLoc p Ω (fun z ↦ if 0 ≤ z.im then f z else L (f (conj z))) := by
  refine memLpLoc_iff.2 fun K hKΩ hK ↦ ?_
  have hL : MeasurableSet {z : ℂ | z.im < 0} :=
    measurableSet_lt Complex.measurable_im measurable_const
  have hsplit : (fun z ↦ if 0 ≤ z.im then f z else L (f (conj z))) =
      {z : ℂ | 0 ≤ z.im}.indicator f + {z : ℂ | z.im < 0}.indicator (fun z ↦ L (f (conj z))) := by
    funext z
    by_cases hz : 0 ≤ z.im
    · simp [hz]
    · simp [hz, not_le.1 hz]
  rw [hsplit]
  refine MemLp.add ?_ ?_
  · rw [memLp_indicator_iff_restrict measurableSet_im_nonneg.nullMeasurableSet,
      Measure.restrict_restrict measurableSet_im_nonneg]
    exact memLpLoc_iff.1 hf _ (fun z hz ↦ ⟨hKΩ hz.2, hz.1⟩)
      (hK.inter_left (isClosed_setOfPred_le_im 0))
  · rw [memLp_indicator_iff_restrict hL.nullMeasurableSet, Measure.restrict_restrict hL]
    let K' : Set ℂ := (conjLIE : ℂ → ℂ) ⁻¹' K ∩ {z | 0 ≤ z.im}
    have hK' : IsCompact K' :=
      (conjLIE.toHomeomorph.isCompact_preimage.2 hK).inter_right (isClosed_setOfPred_le_im 0)
    have hK'Ω : K' ⊆ Ω ∩ {z | 0 ≤ z.im} := fun z hz ↦
      ⟨by simpa using hΩ (hKΩ hz.1), hz.2⟩
    have h2 := (memLpLoc_iff.1 hf _ hK'Ω hK').comp_measurePreserving
      (conjLIE.measurePreserving.restrict_preimage_emb conjLIE.toHomeomorph.measurableEmbedding K')
    simp only [Function.comp_def, Complex.conjLIE_apply] at h2
    refine L.comp_memLp' (h2.mono_measure (Measure.restrict_mono ?_ le_rfl))
    exact fun z hz ↦ ⟨by simpa using hz.2, by simpa using hz.1.out.le⟩

variable [StarAddMonoid F] [StarModule ℝ F] [ContinuousStar F]

/-- The reflection of a function locally `Lᵖ` up to the boundary is locally `Lᵖ` on the doubled
domain. -/
theorem MemLpLoc.starSchwarzReflection {Ω : Set ℂ} (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    {f : ℂ → F} (hf : MemLpLoc p (Ω ∩ {z | 0 ≤ z.im}) f) :
    MemLpLoc p Ω (starSchwarzReflection f) := by
  have hR : TauCeti.starSchwarzReflection f =
      fun z ↦ if 0 ≤ z.im then f z else star (f (conj z)) :=
    funext (starSchwarzReflection_def f)
  rw [hR]
  simpa only [ContinuousLinearEquiv.coe_coe, starL'_apply] using
    hf.ite_conj hΩ (starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap

/-- The reflection of a function locally integrable up to the boundary is locally integrable on
the doubled domain. -/
theorem locallyIntegrableOn_starSchwarzReflection
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) {f : ℂ → F}
    (hf : LocallyIntegrableOn f ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) :
    LocallyIntegrableOn (starSchwarzReflection f) Ω := by
  have hf' : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) f :=
    (memLpLoc_one_iff_locallyIntegrableOn
      (Ω.isOpen.isLocallyClosed_inter_setOfPred_le_im 0)).2 hf
  exact (memLpLoc_one_iff_locallyIntegrableOn Ω.isOpen.isLocallyClosed).1
    (hf'.starSchwarzReflection hΩ)

end LocallyIntegrable

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

/-- Almost-everywhere replacement on `Ω ∩ {0 ≤ im}` preserves the source of the weak
real-boundary equation. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.congr_ae {ξ' : ℂ → F}
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η)
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
theorem HasWeakConjWirtingerDerivRealBoundaryOn.congr_ae_deriv {η' : ℂ → F}
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η)
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

/-- The weak real-boundary equation restricts to smaller open sets. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.mono {Ω' : Opens ℂ}
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) (hΩ : Ω' ≤ Ω) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω' ξ η := by
  obtain ⟨hF, hξ, hη, hχ⟩ := hasWeakConjWirtingerDerivRealBoundaryOn_iff.1 h
  have hs : (Ω' : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    inter_subset_inter_left _ hΩ
  exact hasWeakConjWirtingerDerivRealBoundaryOn_iff.2 ⟨hF, hξ.mono_set hs, hη.mono_set hs,
    fun χ hχr ↦ hχ ⟨χ, χ.contDiff, χ.hasCompactSupport, χ.tsupport_subset.trans hΩ⟩ hχr⟩

/-! ### Test functions -/

/-- The complex test function `ψ • c`, for a real test function `ψ` and `c : ℂ`. -/
private def smulTest (ψ : 𝓓(Ω, ℝ)) (c : ℂ) : 𝓓(Ω, ℂ) :=
  TestFunction.postcompCLM ((ContinuousLinearMap.id ℝ ℝ).smulRight c) ψ

private theorem smulTest_apply (ψ : 𝓓(Ω, ℝ)) (c : ℂ) (z : ℂ) :
    smulTest ψ c z = ψ z • c := rfl

private theorem lineDeriv_smulTest (ψ : 𝓓(Ω, ℝ)) (c : ℂ) (z v : ℂ) :
    lineDeriv ℝ (smulTest ψ c : ℂ → ℂ) z v = lineDeriv ℝ (ψ : ℂ → ℝ) z v • c := by
  have h := congrFun (congrArg DFunLike.coe (TestFunction.lineDerivCLM_postcompCLM
    (n := ⊤) (k := ⊤) ((ContinuousLinearMap.id ℝ ℝ).smulRight c) v ψ)) z
  simpa [smulTest] using h

/-! ### The half-plane pairing -/

/-- The normalized half-plane pairing of a real test function, whose real part the weak
formulation constrains. -/
private def halfPairing (ξ η : ℂ → F) (ψ : 𝓓(Ω, ℝ)) : F :=
  (∫ z in {z : ℂ | 0 ≤ z.im}, lineDeriv ℝ (ψ : ℂ → ℝ) z 1 • ξ z) +
    I • (∫ z in {z : ℂ | 0 ≤ z.im}, lineDeriv ℝ (ψ : ℂ → ℝ) z I • ξ z) +
    (2 : ℂ) • ∫ z in {z : ℂ | 0 ≤ z.im}, (ψ : ℂ → ℝ) z • η z

private theorem halfPairing_add (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η)
    (ψ₁ ψ₂ : 𝓓(Ω, ℝ)) :
    halfPairing ξ η (ψ₁ + ψ₂) = halfPairing ξ η ψ₁ + halfPairing ξ η ψ₂ := by
  have hd (ψ : 𝓓(Ω, ℝ)) (v : ℂ) (z : ℂ) :
      lineDeriv ℝ (ψ : ℂ → ℝ) z v = (TestFunction.lineDerivCLM ℝ v ψ : 𝓓(Ω, ℝ)) z := by
    simp
  have hsum (v : ℂ) (z : ℂ) : lineDeriv ℝ ((ψ₁ + ψ₂ : 𝓓(Ω, ℝ)) : ℂ → ℝ) z v =
      lineDeriv ℝ (ψ₁ : ℂ → ℝ) z v + lineDeriv ℝ (ψ₂ : ℂ → ℝ) z v := by
    rw [hd, hd ψ₁, hd ψ₂, map_add, add_apply]
  have hξ := h.2.1.restrict_of_inter Ω.isOpen (isClosed_setOfPred_le_im 0)
  have hη := h.2.2.1.restrict_of_inter Ω.isOpen (isClosed_setOfPred_le_im 0)
  simp only [halfPairing, hsum, add_smul, add_apply]
  rw [integral_add (integrable_lineDeriv_smul_of_locallyIntegrableOn hξ ψ₁ 1)
      (integrable_lineDeriv_smul_of_locallyIntegrableOn hξ ψ₂ 1),
    integral_add (integrable_lineDeriv_smul_of_locallyIntegrableOn hξ ψ₁ I)
      (integrable_lineDeriv_smul_of_locallyIntegrableOn hξ ψ₂ I),
    integral_add (ψ₁.integrable_smul hη) (ψ₂.integrable_smul hη)]
  module

private theorem halfPairing_neg (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η)
    (ψ : 𝓓(Ω, ℝ)) : halfPairing ξ η (-ψ) = -halfPairing ξ η ψ := by
  have h0 := halfPairing_add h ψ (-ψ)
  rw [add_neg_cancel] at h0
  have hz : halfPairing ξ η (0 : 𝓓(Ω, ℝ)) = 0 := by
    simp [halfPairing, lineDeriv]
  rw [hz] at h0
  exact (neg_eq_of_add_eq_zero_right h0.symm).symm

/-- Testing the weak formulation against `ψ • c` constrains the real part of `c` times the
half-plane pairing of `ψ`. -/
private theorem realPart_smul_halfPairing (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η)
    (ψ : 𝓓(Ω, ℝ)) (c : ℂ) (hc : ∀ x : ℝ, ψ (x : ℂ) * c.im = 0) :
    ℜ (c • halfPairing ξ η ψ) = 0 := by
  have hξ := h.2.1.restrict_of_inter Ω.isOpen (isClosed_setOfPred_le_im 0)
  have _ := h.2.2.1.restrict_of_inter Ω.isOpen (isClosed_setOfPred_le_im 0)
  have key := h.2.2.2 (smulTest ψ c) fun x ↦ by simpa [smulTest_apply] using hc x
  have h1 : ∫ z in {z : ℂ | 0 ≤ z.im},
      (lineDeriv ℝ (smulTest ψ c : ℂ → ℂ) z 1 + I * lineDeriv ℝ (smulTest ψ c : ℂ → ℂ) z I) •
        ξ z =
      c • ((∫ z in {z : ℂ | 0 ≤ z.im}, lineDeriv ℝ (ψ : ℂ → ℝ) z 1 • ξ z) +
        I • ∫ z in {z : ℂ | 0 ≤ z.im}, lineDeriv ℝ (ψ : ℂ → ℝ) z I • ξ z) := by
    have hpt (z : ℂ) :
        (lineDeriv ℝ (smulTest ψ c : ℂ → ℂ) z 1 + I * lineDeriv ℝ (smulTest ψ c : ℂ → ℂ) z I) •
          ξ z =
        c • (lineDeriv ℝ (ψ : ℂ → ℝ) z 1 • ξ z + I • (lineDeriv ℝ (ψ : ℂ → ℝ) z I • ξ z)) := by
      simp only [lineDeriv_smulTest, ← Complex.coe_smul]
      module
    have hi : Integrable (fun z ↦ I • (lineDeriv ℝ (ψ : ℂ → ℝ) z I • ξ z))
        (volume.restrict {z : ℂ | 0 ≤ z.im}) :=
      (integrable_lineDeriv_smul_of_locallyIntegrableOn hξ ψ I).smul I
    simp only [hpt]
    rw [integral_smul, integral_add (integrable_lineDeriv_smul_of_locallyIntegrableOn hξ ψ 1) hi,
      integral_smul]
  have h2 : ∫ z in {z : ℂ | 0 ≤ z.im}, smulTest ψ c z • η z =
      c • ∫ z in {z : ℂ | 0 ≤ z.im}, (ψ : ℂ → ℝ) z • η z := by
    rw [← integral_smul]
    congr 1
    ext z
    rw [smulTest_apply, Complex.real_smul, mul_comm, mul_smul, Complex.coe_smul]
  rw [h1, h2] at key
  have hsplit : c • halfPairing ξ η ψ =
      c • ((∫ z in {z : ℂ | 0 ≤ z.im}, lineDeriv ℝ (ψ : ℂ → ℝ) z 1 • ξ z) +
        I • ∫ z in {z : ℂ | 0 ≤ z.im}, lineDeriv ℝ (ψ : ℂ → ℝ) z I • ξ z) +
      (2 : ℝ) • c • ∫ z in {z : ℂ | 0 ≤ z.im}, (ψ : ℂ → ℝ) z • η z := by
    simp only [halfPairing]
    module
  rw [hsplit, map_add, key, LinearMap.map_smul realPart (2 : ℝ), neg_smul, neg_add_cancel]

private theorem add_star_halfPairing (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η)
    (ψ : 𝓓(Ω, ℝ)) : halfPairing ξ η ψ + star (halfPairing ξ η ψ) = 0 := by
  have h0 := congrArg (Subtype.val) (realPart_smul_halfPairing h ψ 1 (by simp))
  rw [one_smul, realPart_apply_coe, ZeroMemClass.coe_zero, smul_eq_zero] at h0
  exact h0.resolve_left (by norm_num)

private theorem halfPairing_eq_zero (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η)
    (ψ : 𝓓(Ω, ℝ)) (hψ : ∀ x : ℝ, ψ (x : ℂ) = 0) : halfPairing ξ η ψ = 0 := by
  have hr := realPart_smul_halfPairing h ψ 1 (by simp)
  have hi := realPart_smul_halfPairing h ψ I (by simp [hψ])
  rw [one_smul] at hr
  rw [realPart_I_smul, neg_eq_zero] at hi
  rw [← realPart_add_I_smul_imaginaryPart (halfPairing ξ η ψ), hr, hi]
  simp

/-- **The equation away from the axis.** A solution of `\bar∂ξ = η` on `Ω ∩ {0 ≤ im}` with real
boundary values solves the distributional equation on the open upper part `Ω ∩ {0 < im}`, the
interior of `Ω ∩ {0 ≤ im}`: its test functions vanish near the real axis, where the boundary
condition is not seen. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.hasWeakConjWirtingerDerivOn_interior
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) :
    HasWeakConjWirtingerDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) ξ η := by
  have hint : interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) = (Ω : Set ℂ) ∩ {z | 0 < z.im} :=
    interior_inter_setOf_im_nonneg Ω.isOpen
  have hle : Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ≤ Ω := fun z hz ↦
    (interior_subset hz).1
  refine hasWeakConjWirtingerDerivOn_iff.2 ⟨h.1, h.2.1.mono_set interior_subset,
    h.2.2.1.mono_set interior_subset, fun φ ↦ ?_⟩
  have hψ : ((TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) : ℂ → ℝ) = φ := by
    simp [TestFunction.monoCLM_apply, hle]
  -- `φ` vanishes off the open upper part, in particular on the real axis.
  have hφ (z : ℂ) (hz : z ∉ {z : ℂ | 0 < z.im}) : z ∉ tsupport (φ : ℂ → ℝ) := fun hs ↦ by
    have := φ.tsupport_subset hs
    rw [Opens.coe_interior, hint] at this
    exact hz this.2
  have h0 := halfPairing_eq_zero h (TestFunction.monoCLM ℝ φ) fun x ↦ by
    rw [hψ]
    exact image_eq_zero_of_notMem_tsupport (hφ x (by simp))
  have hH (f : ℂ → F) (hf : ∀ z, z ∉ tsupport (φ : ℂ → ℝ) → f z = 0) :
      ∫ z in {z : ℂ | 0 ≤ z.im}, f z = ∫ z, f z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦
      hf z (hφ z fun h' ↦ hz (ofPred_subset_ofPred.2 (fun _ ↦ le_of_lt) h'))
  simp only [halfPairing, hψ] at h0
  rw [hH _ fun z hz ↦ by simp [lineDeriv_of_notMem_tsupport hz],
    hH _ fun z hz ↦ by simp [lineDeriv_of_notMem_tsupport hz],
    hH _ fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport hz]] at h0
  rw [eq_neg_of_add_eq_zero_left h0, neg_smul]

variable [ContinuousStar F]

/-! ### Splitting integrals on the doubled domain -/

/-- An integral of a reflected function against a real test function on the doubled domain is the
upper half-plane integral plus the conjugate of the reflected upper half-plane integral. -/
private theorem integral_smul_starSchwarzReflection {f : ℂ → F} (a : ℂ → ℝ)
    (ha : Integrable (fun z ↦ a z • starSchwarzReflection f z)) :
    ∫ z, a z • starSchwarzReflection f z =
      (∫ z in {z : ℂ | 0 ≤ z.im}, a z • f z) +
        star (∫ z in {z : ℂ | 0 ≤ z.im}, a (conj z) • f z) := by
  have hH : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  rw [Complex.integral_eq_setIntegral_add_comp_conj ha,
    integral_add (g := fun z ↦ a (conj z) • starSchwarzReflection f (conj z)) ha.integrableOn
      ((integrable_comp conjLIE _).2 ha).integrableOn,
    setIntegral_congr_set (Complex.setOf_le_im_ae_eq 0),
    setIntegral_congr_set (Complex.setOf_le_im_ae_eq 0), ← integral_star]
  congr 1 <;> refine setIntegral_congr_fun hH fun z hz ↦ ?_
  · rw [starSchwarzReflection_of_im_nonneg (le_of_lt hz.out)]
  · rw [starSchwarzReflection_of_im_neg (by simpa using hz.out), conj_conj, star_smul,
      star_trivial (a (conj z))]

/-! ### Weak Schwarz reflection -/

/-- **Reflection to the doubled domain.** On a conjugation-invariant open set, the reflections of
a weak solution of `\bar∂ξ = η` with real boundary values solve the distributional equation
`\bar∂ (Rξ) = Rη` on the whole set. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.hasWeakConjWirtingerDerivOn_starSchwarzReflection
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) :
    HasWeakConjWirtingerDerivOn volume Ω (starSchwarzReflection ξ) (starSchwarzReflection η) := by
  have := h.1
  have hU := locallyIntegrableOn_starSchwarzReflection hΩ h.2.1
  have hG := locallyIntegrableOn_starSchwarzReflection hΩ h.2.2.1
  refine hasWeakConjWirtingerDerivOn_iff.2 ⟨h.1, hU, hG, fun φ ↦ ?_⟩
  set φs := TestFunction.compConj hΩ φ
  -- The pairing of `φ` plus the conjugate of the pairing of `φ ∘ conj` vanishes.
  have hsym : halfPairing ξ η φ + star (halfPairing ξ η φs) = 0 := by
    have he := add_star_halfPairing h (φ + φs)
    have ho := halfPairing_eq_zero h (φ + -φs) fun x ↦ by
      simp [φs, TestFunction.compConj_apply, Complex.conj_ofReal]
    rw [halfPairing_add h] at he ho
    rw [halfPairing_neg h, ← sub_eq_add_neg, sub_eq_zero] at ho
    rw [ho, star_add] at he
    rw [ho]
    have h2 : (2 : ℂ) • (halfPairing ξ η φs + star (halfPairing ξ η φs)) = 0 := by
      rw [two_smul, ← he]
      abel
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  have hd (v : ℂ) : Integrable (fun z ↦ lineDeriv ℝ (φ : ℂ → ℝ) z v • starSchwarzReflection ξ z) :=
    integrable_lineDeriv_smul_of_locallyIntegrableOn hU φ v
  rw [integral_smul_starSchwarzReflection _ (hd 1),
    integral_smul_starSchwarzReflection _ (hd I),
    integral_smul_starSchwarzReflection _ (φ.integrable_smul hG)]
  have h1 (z : ℂ) : lineDeriv ℝ (φ : ℂ → ℝ) (conj z) 1 = lineDeriv ℝ (φs : ℂ → ℝ) z 1 := by
    rw [TestFunction.lineDeriv_compConj, map_one]
  have hI (z : ℂ) : lineDeriv ℝ (φ : ℂ → ℝ) (conj z) I = -lineDeriv ℝ (φs : ℂ → ℝ) z I := by
    rw [TestFunction.lineDeriv_compConj, conj_I, lineDeriv_neg, neg_neg]
  have h0 (z : ℂ) : (φ : ℂ → ℝ) (conj z) = (φs : ℂ → ℝ) z :=
    (TestFunction.compConj_apply hΩ φ z).symm
  simp only [h1, hI, h0, neg_smul, integral_neg, star_neg]
  simp only [halfPairing, star_add, star_smul, conj_I, Complex.star_def, map_ofNat] at hsym
  rw [← sub_eq_zero, ← hsym]
  module

/-- **Weak Schwarz reflection.** A locally integrable weak solution of `\bar∂ξ = 0` on
`Ω ∩ {0 ≤ im}` with real boundary values, for a conjugation-invariant open set `Ω` and
finite-dimensional coefficients, agrees almost everywhere on `Ω ∩ {0 ≤ im}` with a map
holomorphic on all of `Ω` that is conjugation-symmetric, hence real on the real axis. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.exists_differentiableOn_ae_eq
    [FiniteDimensional ℂ F] (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ 0) :
    ∃ v : ℂ → F, DifferentiableOn ℂ v Ω ∧ (∀ z ∈ Ω, v (conj z) = star (v z)) ∧
      (∀ x : ℝ, (x : ℂ) ∈ Ω → star (v x) = v x) ∧
      ξ =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] v := by
  have hw := h.hasWeakConjWirtingerDerivOn_starSchwarzReflection hΩ
  rw [starSchwarzReflection_zero] at hw
  obtain ⟨v, hv, hUv⟩ := hw.exists_differentiableOn_ae_eq
  have hUv' : ∀ᵐ z, z ∈ (Ω : Set ℂ) → starSchwarzReflection ξ z = v z :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).1 hUv
  -- `z ↦ star (v (conj z))` is continuous and agrees with `v` almost everywhere on `Ω`.
  have hsymm : EqOn (fun z ↦ star (v (conj z))) v Ω := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ Ω.isOpen
      (continuous_star.comp_continuousOn
        (hv.continuousOn.comp Complex.continuous_conj.continuousOn hΩ)) hv.continuousOn
    rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
    have hc := conjLIE.measurePreserving.quasiMeasurePreserving.ae hUv'
    have hne : ∀ᵐ z : ℂ, z.im ≠ 0 := by
      rw [ae_iff]
      simpa using Complex.volume_setOf_im_eq 0
    filter_upwards [hUv', hc, hne] with z hz hcz hnz hzΩ
    have hcz' := hcz (by simpa using hΩ hzΩ)
    simp only [conjLIE_apply] at hcz'
    rw [← hcz', starSchwarzReflection_conj hnz, star_star, hz hzΩ]
  refine ⟨v, hv, fun z hz ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · have := hsymm (hΩ hz)
    simp only [conj_conj] at this
    exact this.symm
  · simpa using hsymm hx
  · have hsub : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}),
        starSchwarzReflection ξ z = v z :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hUv
    filter_upwards [hsub, ae_restrict_mem (Ω.isOpen.measurableSet.inter measurableSet_im_nonneg)]
      with z hz hzH
    rw [← hz, starSchwarzReflection_of_im_nonneg hzH.2]

end TauCeti

/-! ### Pointwise reality of weak boundary values -/

open Complex MeasureTheory TopologicalSpace Set Filter Topology
open scoped ComplexConjugate

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F] [StarModule ℂ F]
  {Ω : Opens ℂ} {ξ η : ℂ → F}

variable [FiniteDimensional ℂ F] {p : ENNReal}

/-- The pointwise boundary values on a conjugation-invariant open set, for a finite exponent. -/
private theorem star_eq_of_continuousOn_of_mapsTo [ContinuousStar F]
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hη : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) {x : ℝ} (hx : (x : ℂ) ∈ Ω) :
    star (ξ x) = ξ x := by
  have hp1 : 1 < p := (by norm_num : (1 : ENNReal) < 2).trans hp
  have := FiniteDimensional.completeSpace ℂ F
  have hRξ : MemLpLoc p Ω (starSchwarzReflection ξ) := hξc.memLpLoc.starSchwarzReflection hΩ
  have hW := (h.hasWeakConjWirtingerDerivOn_starSchwarzReflection hΩ).memWkpLoc_one hp1 hp_top
    hRξ (hη.starSchwarzReflection hΩ)
  -- `g` is a representative of the reflection, continuous on `Ω`.
  set g := MeasureTheory.preciseRepresentative volume (starSchwarzReflection ξ)
  have hg : ContinuousAt g x :=
    (hW.continuousOn_preciseRepresentative hp).continuousAt (Ω.isOpen.mem_nhds hx)
  have hae := hRξ.ae_eq_preciseRepresentative hp1.le
  -- Off the real axis `g` agrees with the continuous functions it represents almost everywhere.
  have hside {s : Set ℂ} (hso : IsOpen s) {f : ℂ → F} (hf : ContinuousOn f ((Ω : Set ℂ) ∩ s))
      (hRf : EqOn (starSchwarzReflection ξ) f s) : EqOn f g ((Ω : Set ℂ) ∩ s) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ (Ω.isOpen.inter hso) hf
      ((hW.continuousOn_preciseRepresentative hp).mono inter_subset_left)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hae,
      ae_restrict_mem (Ω.isOpen.inter hso).measurableSet] with z hz hzs
    exact (hRf hzs.2).symm.trans hz
  have hsub : (Ω : Set ℂ) ∩ {z | 0 < z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    fun z hz ↦ ⟨hz.1, hz.2.out.le⟩
  have hup := hside (isOpen_lt continuous_const continuous_im) (hξc.mono hsub)
    fun z hz ↦ starSchwarzReflection_of_im_nonneg hz.out.le
  have hconj : MapsTo (starRingEnd ℂ) ((Ω : Set ℂ) ∩ {z | z.im < 0})
      ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := fun z hz ↦
    ⟨hΩ hz.1, by simpa using hz.2.out.le⟩
  have hdown := hside (isOpen_lt continuous_im continuous_const)
    (continuous_star.comp_continuousOn (hξc.comp continuous_conj.continuousOn hconj))
    fun z hz ↦ starSchwarzReflection_of_im_neg hz.out
  have hξx : ContinuousWithinAt ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) x := hξc x ⟨hx, by simp⟩
  have hΩx : (Ω : Set ℂ) ∈ 𝓝 (x : ℂ) := Ω.isOpen.mem_nhds hx
  -- The limit of `g` at `x` from above is `ξ x`.
  have hgx : g x = ξ x := by
    have : (𝓝[(Ω : Set ℂ) ∩ {z | 0 < z.im}] (x : ℂ)).NeBot := by
      rw [inter_comm, nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hΩx)]
      exact mem_closure_iff_nhdsWithin_neBot.1 (by simp)
    refine tendsto_nhds_unique (l := 𝓝[(Ω : Set ℂ) ∩ {z | 0 < z.im}] (x : ℂ))
      (hg.tendsto.mono_left nhdsWithin_le_nhds) ?_
    exact (hξx.tendsto.mono_left (nhdsWithin_mono _ hsub)).congr'
      (eventually_nhdsWithin_of_forall hup)
  -- The limit of `g` at `x` from below is `star (ξ x)`.
  have : (𝓝[(Ω : Set ℂ) ∩ {z | z.im < 0}] (x : ℂ)).NeBot := by
    rw [inter_comm, nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hΩx)]
    exact mem_closure_iff_nhdsWithin_neBot.1 (by simp)
  have hc : Tendsto (starRingEnd ℂ) (𝓝[(Ω : Set ℂ) ∩ {z | z.im < 0}] (x : ℂ))
      (𝓝[(Ω : Set ℂ) ∩ {z | 0 ≤ z.im}] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_conj.tendsto' _ _ (conj_ofReal x)).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall hconj⟩
  refine (tendsto_nhds_unique ((continuous_star.tendsto _).comp (hξx.tendsto.comp hc)) ?_).trans hgx
  exact (hg.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsWithin_of_forall fun z hz ↦ (hdown hz).symm)

/-- **Weak real boundary values are pointwise real.** Let `p > 2` and let `ξ` be continuous on
`Ω ∩ {0 ≤ im}`, solving `\bar∂ξ = η` weakly on `Ω ∩ {0 ≤ im}` with the real boundary condition,
for `η` locally `Lᵖ` up to the axis and finite-dimensional coefficients. Then `ξ` is real on
`Ω ∩ ℝ`. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.star_eq_of_continuousOn (hp : 2 < p)
    (hη : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) :
    ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x := by
  intro x hx
  have := FiniteDimensional.continuousStar ℝ F
  -- Shrink `Ω` to the conjugation-invariant open set `Ω ∩ conj Ω` and `p` to a finite exponent.
  let Ω' : Opens ℂ := ⟨(Ω : Set ℂ) ∩ conj ⁻¹' Ω, Ω.isOpen.inter (Ω.isOpen.preimage continuous_conj)⟩
  have hΩ' : Ω' ≤ Ω := fun z hz ↦ hz.1
  have hs : (Ω' : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    inter_subset_inter_left _ hΩ'
  exact star_eq_of_continuousOn_of_mapsTo (Ω := Ω') (fun z hz ↦ ⟨hz.2, by simpa using hz.1⟩)
    (lt_min hp (by norm_num)) (ne_top_of_le_ne_top ENNReal.ofNat_ne_top (min_le_right p 3))
    ((hη.mono_set hs).mono_exponent (min_le_left p 3)) (hξc.mono hs) (h.mono hΩ')
    ⟨hx, by simpa using hx⟩

/-- **Weak real boundary values are pointwise real, linear form.** Let `p > 2` and let `ξ` be
continuous on `Ω ∩ {0 ≤ im}`, solving `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the
real boundary condition, for a coefficient field `C` locally `Lᵖ` up to the axis and
finite-dimensional coefficients. Then `ξ` is real on `Ω ∩ ℝ`. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.star_eq_of_continuousOn_clm {C : ℂ → F →L[ℝ] F}
    (hp : 2 < p) (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z)) :
    ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x := by
  refine h.star_eq_of_continuousOn hp ?_ hξc
  convert (hC.clm_apply_continuousOn hξc).const_smul (-(2 : ℝ)⁻¹) using 1
  ext z
  simp [← Complex.coe_smul]

/-- **Check.** The constant `i`, which is not real on the axis, is not a weak real-boundary
solution of `\bar∂ξ = η` for any `η` locally `Lᵖ` up to the axis with `p > 2`, on an open set
meeting the real axis. -/
theorem not_hasWeakConjWirtingerDerivRealBoundaryOn_const_I_of_memLpLoc (hp : 2 < p) {x₀ : ℝ}
    (hx₀ : (x₀ : ℂ) ∈ Ω) {η : ℂ → ℂ} (hη : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η) :
    ¬ HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun _ ↦ I) η := fun h ↦ by
  have := h.star_eq_of_continuousOn hp hη continuousOn_const x₀ hx₀
  norm_num [Complex.ext_iff] at this

end TauCeti

namespace TauCeti

variable {Ω : Opens ℂ}

/-- **Check.** The even reflection `s + i|t|` of the identity, which reflects without
conjugating, is not a distributional solution of `\bar∂u = 0` on any open set meeting the lower
half-plane: there it is `conj`. -/
theorem not_hasWeakConjWirtingerDerivOn_re_add_I_mul_abs_im
    (hΩ : ((Ω : Set ℂ) ∩ {z | z.im < 0}).Nonempty) :
    ¬ HasWeakConjWirtingerDerivOn volume Ω (fun z ↦ (z.re : ℂ) + I * |z.im|) 0 := by
  intro h
  let Ω' : Opens ℂ := Ω ⊓ ⟨{z | z.im < 0}, isOpen_lt Complex.continuous_im continuous_const⟩
  have h' := (h.mono (inf_le_left : Ω' ≤ Ω)).congr_ae (v := conj) (by
    rw [Filter.EventuallyEq, ae_restrict_iff' Ω'.isOpen.measurableSet]
    filter_upwards [] with z hz
    have hz' : z.im < 0 := hz.2
    apply Complex.ext <;> simp [abs_of_neg hz'])
  have he := (hasWeakConjWirtingerDerivOn_conj (μ := volume) (Ω := Ω')).ae_eq h'
  have hμ : volume (Ω' : Set ℂ) = 0 := by
    simpa [Filter.EventuallyEq, ae_iff] using he
  exact (Ω'.isOpen.measure_pos volume hΩ).ne' hμ

end TauCeti

/-! ### Classical solutions and their boundary term -/

open Complex MeasureTheory TopologicalSpace Set Filter Topology
open scoped ContDiff Distributions ComplexConjugate ComplexStarModule

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {Ω : Opens ℂ} {ξ η : ℂ → F}

private theorem measurableSet_im_pos : MeasurableSet {z : ℂ | 0 < z.im} :=
  measurableSet_lt measurable_const Complex.measurable_im

/-- `Ω ∩ {0 ≤ im}` is a neighbourhood of every point of `Ω` off the real axis in the upper
half-plane. -/
private theorem inter_im_nonneg_mem_nhds {z : ℂ} (hz : z ∈ (Ω : Set ℂ)) (hz' : 0 < z.im) :
    (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ∈ 𝓝 z :=
  inter_mem (Ω.isOpen.mem_nhds hz)
    (mem_of_superset ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz')
      fun _ hw ↦ le_of_lt hw)

omit [NormedSpace ℂ F] in
/-- A map continuous on `Ω ∩ {0 ≤ im}` and vanishing outside the support of a test function is
integrable on the closed upper half-plane. -/
private theorem integrableOn_im_nonneg_of_continuousOn (χ : 𝓓(Ω, ℂ)) {h : ℂ → F}
    (hh : ContinuousOn h ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (h0 : ∀ z, z ∉ tsupport (χ : ℂ → ℂ) → h z = 0) :
    IntegrableOn h {z : ℂ | 0 ≤ z.im} := by
  have hK : IsCompact (tsupport (χ : ℂ → ℂ) ∩ {z : ℂ | 0 ≤ z.im}) :=
    χ.hasCompactSupport.isCompact.inter_right (isClosed_setOfPred_le_im 0)
  have hKΩ : tsupport (χ : ℂ → ℂ) ∩ {z : ℂ | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    fun z hz ↦ ⟨χ.tsupport_subset hz.1, hz.2⟩
  exact ((hh.mono hKΩ).integrableOn_compact hK).of_forall_sdiff_eq_zero measurableSet_im_nonneg
    fun z hz ↦ h0 z fun h ↦ hz.2 ⟨h, hz.1⟩

section ClassicalSolution

variable (hξ : ContDiffOn ℝ 1 ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
  (hη : ∀ z ∈ (Ω : Set ℂ), 0 < z.im → conjWirtingerDeriv ξ z 1 = η z)

include hξ in
/-- The product of a test function with `ξ` is `C¹` up to the real axis on the closed half-plane. -/
private theorem contDiffOn_smul (χ : 𝓓(Ω, ℂ)) :
    ContDiffOn ℝ 1 (fun z ↦ χ z • ξ z) {z : ℂ | 0 ≤ z.im} := by
  intro z hz
  by_cases hzΩ : z ∈ (Ω : Set ℂ)
  · have h := ((χ.contDiff.of_le (by simp)).contDiffOn.smul hξ) z ⟨hzΩ, hz⟩
    rwa [inter_comm, contDiffWithinAt_inter (Ω.isOpen.mem_nhds hzΩ)] at h
  · have h0 : (fun z ↦ χ z • ξ z) =ᶠ[𝓝 z] fun _ ↦ 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1
        fun h ↦ hzΩ (χ.tsupport_subset h)] with w hw
      simp [hw]
    exact (contDiffAt_const.congr_of_eventuallyEq h0).contDiffWithinAt

include hξ hη in
/-- Off the real axis, the integrand of the weak equation is the Cauchy–Riemann operator of the
product `χ ξ` minus `2 χ η`. -/
private theorem lineDeriv_add_I_mul_smul_eq (χ : 𝓓(Ω, ℂ)) {z : ℂ} (hz : 0 < z.im) :
    (lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I) • ξ z =
      (fderiv ℝ (fun z ↦ χ z • ξ z) z 1 + I • fderiv ℝ (fun z ↦ χ z • ξ z) z I) -
        (2 : ℂ) • (χ z • η z) := by
  by_cases hzΩ : z ∈ (Ω : Set ℂ)
  · have hχd : DifferentiableAt ℝ (χ : ℂ → ℂ) z := χ.contDiff.differentiable (by simp) z
    have hξd : DifferentiableAt ℝ ξ z :=
      (hξ.differentiableOn one_ne_zero).differentiableAt (inter_im_nonneg_mem_nhds hzΩ hz)
    have hη' := hη z hzΩ hz
    rw [conjWirtingerDeriv_apply] at hη'
    have hfd : HasFDerivAt (fun z ↦ χ z • ξ z)
        (χ z • fderiv ℝ ξ z + (fderiv ℝ (χ : ℂ → ℂ) z).smulRight (ξ z)) z :=
      hχd.hasFDerivAt.smul hξd.hasFDerivAt
    rw [hfd.fderiv, hχd.lineDeriv_eq_fderiv,
      hχd.lineDeriv_eq_fderiv, ← hη']
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_one]
    module
  · have ht : z ∉ tsupport (χ : ℂ → ℂ) := fun h ↦ hzΩ (χ.tsupport_subset h)
    have ht' : z ∉ tsupport (fun z ↦ χ z • ξ z) := fun h ↦
      ht (tsupport_smul_subset_left (fun z ↦ χ z) ξ h)
    simp [lineDeriv_of_notMem_tsupport ht, fderiv_of_notMem_tsupport ℝ ht',
      image_eq_zero_of_notMem_tsupport ht]

include hξ hη in
/-- **Integration by parts on the closed upper half-plane, with its boundary term.** For `ξ` that
is `C¹` up to the real axis on `Ω ∩ {0 ≤ im}` with `\bar∂ξ = η` off the axis, and a smooth complex
test function `χ` compactly supported in `Ω`,
`∫_{0 ≤ t} (∂_s χ + i ∂_t χ) ξ = -2 ∫_{0 ≤ t} χ η - i ∫_ℝ χ(s) ξ(s) ds`. -/
theorem setIntegral_im_nonneg_lineDeriv_add_I_mul_smul_eq (χ : 𝓓(Ω, ℂ)) :
    ∫ z in {z : ℂ | 0 ≤ z.im},
        (lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I) • ξ z =
      -(2 : ℂ) • (∫ z in {z : ℂ | 0 ≤ z.im}, χ z • η z) - I • ∫ s : ℝ, χ s • ξ s := by
  by_cases hF : CompleteSpace F
  swap
  · simp only [integral_of_not_completeSpace hF, smul_zero, sub_zero]
  set f : ℂ → F := fun z ↦ χ z • ξ z
  have hf := contDiffOn_smul hξ χ
  have hfc : HasCompactSupport f := χ.hasCompactSupport.smul_right
  have h1 := integrableOn_im_pos_fderiv_apply_of_contDiffOn hf hfc 1
  have hI := integrableOn_im_pos_fderiv_apply_of_contDiffOn hf hfc I
  have hL : IntegrableOn
      (fun z ↦ (lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I) • ξ z)
      {z : ℂ | 0 < z.im} := by
    refine (integrableOn_im_nonneg_of_continuousOn χ ?_ fun z hz ↦ ?_).mono_set
      fun z (hz : 0 < z.im) ↦ le_of_lt hz
    · simp_rw [← TestFunction.lineDerivOp_apply]
      exact (((LineDeriv.lineDerivOp (1 : ℂ) χ).continuous.add
        (continuous_const.mul (LineDeriv.lineDerivOp I χ).continuous)).continuousOn).smul
          hξ.continuousOn
    · simp [lineDeriv_of_notMem_tsupport hz]
  have hIs : IntegrableOn (fun z ↦ I • fderiv ℝ f z I) {z : ℂ | 0 < z.im} := hI.smul I
  have hA : IntegrableOn (fun z ↦ fderiv ℝ f z 1 + I • fderiv ℝ f z I) {z : ℂ | 0 < z.im} :=
    h1.add hIs
  have hB : IntegrableOn (fun z ↦ χ z • η z) {z : ℂ | 0 < z.im} := by
    refine IntegrableOn.congr_fun ((hA.sub hL).smul ((2 : ℂ)⁻¹))
      (fun z (hz : 0 < z.im) ↦ ?_) measurableSet_im_pos
    simp only [Pi.sub_apply, Pi.smul_apply, lineDeriv_add_I_mul_smul_eq hξ hη χ hz]
    module
  have hB2 : IntegrableOn (fun z ↦ (2 : ℂ) • (χ z • η z)) {z : ℂ | 0 < z.im} := hB.smul 2
  have hae := setOf_le_im_ae_eq (0 : ℝ)
  rw [setIntegral_congr_set hae, setIntegral_congr_set hae,
    setIntegral_congr_fun measurableSet_im_pos fun z hz ↦ lineDeriv_add_I_mul_smul_eq hξ hη χ hz,
    integral_sub hA hB2, integral_add h1 hIs, integral_smul, integral_smul,
    setIntegral_im_pos_fderiv_one_eq_zero_of_contDiffOn hf hfc,
    setIntegral_im_pos_fderiv_I_eq_neg_integral_of_contDiffOn hf hfc]
  module

variable [CompleteSpace F] [StarAddMonoid F] [StarModule ℂ F] [ContinuousStar F]

include hξ hη in
/-- **Classical solutions with real boundary values are weak solutions.** A map `ξ` that is `C¹`
up to the real axis on `Ω ∩ {0 ≤ im}`, solves `\bar∂ξ = η` at the points of `Ω` off the axis, and
takes real values on `Ω ∩ ℝ` (`star (ξ x) = ξ x`), is a weak solution of `\bar∂ξ = η` with real
boundary values. The values of `η` on the axis are irrelevant. -/
theorem hasWeakConjWirtingerDerivRealBoundaryOn_of_contDiffOn
    (hreal : ∀ x : ℝ, (x : ℂ) ∈ (Ω : Set ℂ) → star (ξ x) = ξ x) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η := by
  have hm : MeasurableSet ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
    Ω.isOpen.measurableSet.inter measurableSet_im_nonneg
  have hD := hξ.continuousOn_fderivWithin
    (by rw [inter_comm]; exact (uniqueDiffOn_setOfPred_le_im 0).inter Ω.isOpen) le_rfl
  have hηc : ContinuousOn
      (fun z ↦ (2 : ℂ)⁻¹ • (fderivWithin ℝ ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) z 1 +
        I • fderivWithin ℝ ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) z I))
      ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
    continuousOn_const.smul ((hD.clm_apply continuousOn_const).add
      (continuousOn_const.smul (hD.clm_apply continuousOn_const)))
  have hηae : (fun z ↦ (2 : ℂ)⁻¹ • (fderivWithin ℝ ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) z 1 +
        I • fderivWithin ℝ ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) z I)) =ᵐ[
      volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] η := by
    rw [EventuallyEq, ae_restrict_iff' hm]
    filter_upwards [Complex.ae_im_ne_zero] with z hz hzΩ
    have hz' : 0 < z.im := lt_of_le_of_ne hzΩ.2 (Ne.symm hz)
    rw [← hη z hzΩ.1 hz', conjWirtingerDeriv_apply, smul_eq_mul, mul_one,
      fderivWithin_of_mem_nhds (inter_im_nonneg_mem_nhds hzΩ.1 hz')]
  refine hasWeakConjWirtingerDerivRealBoundaryOn_iff.2 ⟨inferInstance,
    hξ.continuousOn.locallyIntegrableOn hm,
    (hηc.locallyIntegrableOn hm).congr hηae, fun χ hχ ↦ ?_⟩
  have hB : IsSelfAdjoint (∫ s : ℝ, χ s • ξ s) := by
    rw [IsSelfAdjoint, ← integral_star]
    congr 1
    funext s
    by_cases hs : (s : ℂ) ∈ (Ω : Set ℂ)
    · rw [star_smul, hreal s hs, Complex.star_def, conj_eq_iff_im.2 (hχ s)]
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hs (χ.tsupport_subset h)]
      simp
  rw [setIntegral_im_nonneg_lineDeriv_add_I_mul_smul_eq hξ hη χ, map_sub, realPart_I_smul,
    hB.imaginaryPart, realPart_smul]
  simp

end ClassicalSolution

/-! ### Checks -/

/-- **Check.** `z²` is holomorphic and real on the real axis, so it solves `\bar∂ξ = 0` weakly
with real boundary values on every open set. -/
theorem hasWeakConjWirtingerDerivRealBoundaryOn_sq :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun z : ℂ ↦ z ^ 2) 0 := by
  refine hasWeakConjWirtingerDerivRealBoundaryOn_of_contDiffOn
    (((contDiff_id (𝕜 := ℂ)).pow 2).restrict_scalars ℝ).contDiffOn (fun z _ _ ↦ ?_) fun x _ ↦ ?_
  · simp
  · simp [conj_ofReal]

/-- **Check.** `z e^{-conj z}` solves `\bar∂ξ = -ξ`, that is `∂_s ξ + i ∂_t ξ + 2ξ = 0`, and is
real on the real axis, so it is a weak solution with real boundary values on every open set. -/
theorem hasWeakConjWirtingerDerivRealBoundaryOn_mul_cexp_neg_conj :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω (fun z : ℂ ↦ z * cexp (-conj z))
      fun z ↦ -(z * cexp (-conj z)) := by
  have hd : ContDiff ℝ 1 fun z : ℂ ↦ z * cexp (-conj z) := by
    simpa only [Complex.conjCLE_apply, id_eq] using contDiff_id.mul conjCLE.contDiff.neg.cexp
  refine hasWeakConjWirtingerDerivRealBoundaryOn_of_contDiffOn hd.contDiffOn
    (fun z _ _ ↦ conjWirtingerDeriv_mul_cexp_neg_conj z) fun x _ ↦ ?_
  rw [Complex.star_def, map_mul, ← Complex.exp_conj, map_neg, conj_conj, conj_ofReal]

end TauCeti
