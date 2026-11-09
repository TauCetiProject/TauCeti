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
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Star
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

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

## Main results

* `TauCeti.starSchwarzReflection ξ`: `ξ` on `0 ≤ im`, and `star (ξ (conj z))` below the axis;
  for `F = ℂ` it is `TauCeti.schwarzReflection`.
* `HasWeakConjWirtingerDerivRealBoundaryOn.hasWeakConjWirtingerDerivOn_starSchwarzReflection`:
  on a conjugation-invariant open set, the reflections of a weak solution with real boundary
  values solve the distributional equation `\bar∂ (Rξ) = Rη` on the doubled domain.
* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.exists_differentiableOn_ae_eq`: **weak
  Schwarz reflection**. With finite-dimensional coefficients and `η = 0`, `ξ` agrees almost
  everywhere on `Ω ∩ {0 ≤ im}` with a map holomorphic on all of `Ω`, real on `Ω ∩ ℝ` and
  satisfying `v (conj z) = star (v z)`. It is a weak analogue of
  `TauCeti.differentiableOn_schwarzReflection_of_symmetric`; recovering that lemma from it would
  also need the half-plane boundary-term computation for smooth data, which is not proved here.
* Checks: the reflection of `z` is `z`, and the even reflection `s + i|t|`, which omits the
  conjugation, is not a weak solution below the axis.

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

/-! ### The reflection -/

section Reflection

variable [StarAddMonoid F] {ξ : ℂ → F}

/-- Schwarz reflection across the real axis with respect to the real structure `star` of the
coefficients: `ξ z` on the closed upper half-plane and `star (ξ (conj z))` below it. -/
def starSchwarzReflection (ξ : ℂ → F) (z : ℂ) : F :=
  if 0 ≤ z.im then ξ z else star (ξ (conj z))

theorem starSchwarzReflection_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) :
    starSchwarzReflection ξ z = ξ z := ite_eq_left_iff.2 fun h ↦ (h hz).elim

theorem starSchwarzReflection_of_im_neg {z : ℂ} (hz : z.im < 0) :
    starSchwarzReflection ξ z = star (ξ (conj z)) := ite_eq_right_iff.2 fun h ↦ (hz.not_ge h).elim

/-- For scalar functions the reflection is the classical Schwarz reflection. -/
theorem starSchwarzReflection_eq_schwarzReflection (f : ℂ → ℂ) :
    starSchwarzReflection f = schwarzReflection f := by
  ext z
  rw [schwarzReflection_def, starSchwarzReflection, Complex.star_def]

@[simp]
theorem starSchwarzReflection_zero : starSchwarzReflection (0 : ℂ → F) = 0 := by
  ext z
  simp [starSchwarzReflection]

/-- Off the real axis the reflection is conjugation-symmetric. -/
theorem starSchwarzReflection_conj {z : ℂ} (hz : z.im ≠ 0) :
    starSchwarzReflection ξ (conj z) = star (starSchwarzReflection ξ z) := by
  rcases hz.lt_or_gt with hz | hz
  · rw [starSchwarzReflection_of_im_nonneg (by simpa using hz.le),
      starSchwarzReflection_of_im_neg hz, star_star]
  · rw [starSchwarzReflection_of_im_neg (by simpa using hz),
      starSchwarzReflection_of_im_nonneg hz.le, conj_conj]

/-- **Check.** The reflection of the identity, which is real on the real axis, is the identity. -/
theorem starSchwarzReflection_id : starSchwarzReflection (id : ℂ → ℂ) = id := by
  ext1 z
  by_cases hz : 0 ≤ z.im
  · simp [starSchwarzReflection_of_im_nonneg hz]
  · simp [starSchwarzReflection_of_im_neg (not_le.1 hz)]

end Reflection

/-! ### Measure-theoretic preliminaries -/

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

/-! ### Test functions -/

/-- A real test function on a conjugation-invariant open set, composed with conjugation. -/
private def conjTest (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (φ : 𝓓(Ω, ℝ)) : 𝓓(Ω, ℝ) :=
  ⟨(φ : ℂ → ℝ) ∘ conjLIE, φ.contDiff.comp conjLIE.toContinuousLinearEquiv.contDiff,
    φ.hasCompactSupport.comp_homeomorph conjLIE.toHomeomorph, by
      intro z hz
      rw [← LinearIsometryEquiv.coe_toHomeomorph, tsupport_comp_eq_preimage] at hz
      simpa using hΩ (φ.tsupport_subset hz)⟩

private theorem conjTest_apply (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (φ : 𝓓(Ω, ℝ)) (z : ℂ) :
    conjTest hΩ φ z = φ (conj z) := rfl

private theorem lineDeriv_conjTest (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (φ : 𝓓(Ω, ℝ))
    (z v : ℂ) :
    lineDeriv ℝ (conjTest hΩ φ : ℂ → ℝ) z v = lineDeriv ℝ (φ : ℂ → ℝ) (conj z) (conj v) := by
  simp only [lineDeriv, conjTest_apply, map_add, Complex.real_smul, map_mul,
    Complex.conj_ofReal]

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
  have hξ := h.2.1.restrict_of_inter Ω.isOpen isClosed_im_nonneg
  have hη := h.2.2.1.restrict_of_inter Ω.isOpen isClosed_im_nonneg
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
  have hξ := h.2.1.restrict_of_inter Ω.isOpen isClosed_im_nonneg
  have hη := h.2.2.1.restrict_of_inter Ω.isOpen isClosed_im_nonneg
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

variable [ContinuousStar F]

/-- The reflection of a function locally integrable up to the boundary is locally integrable on
the doubled domain. -/
theorem locallyIntegrableOn_starSchwarzReflection
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) {f : ℂ → F}
    (hf : LocallyIntegrableOn f ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) :
    LocallyIntegrableOn (starSchwarzReflection f) Ω := by
  refine (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).2 fun K hKΩ hK ↦ ?_
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hHc : MeasurableSet {z : ℂ | z.im < 0} :=
    measurableSet_lt Complex.measurable_im measurable_const
  have hup : IntegrableOn (starSchwarzReflection f) (K ∩ {z | 0 ≤ z.im}) := by
    refine (hf.integrableOn_compact_subset (inter_subset_inter_left _ hKΩ)
      (hK.inter_right isClosed_im_nonneg)).congr_fun
      (fun z hz ↦ (starSchwarzReflection_of_im_nonneg hz.2).symm)
      (hKm.inter measurableSet_im_nonneg)
  have hdown : IntegrableOn (starSchwarzReflection f) (K ∩ {z | z.im < 0}) := by
    let K' : Set ℂ := (conjLIE : ℂ → ℂ) ⁻¹' K ∩ {z | 0 ≤ z.im}
    have hK' : IsCompact K' :=
      (conjLIE.toHomeomorph.isCompact_preimage.2 hK).inter_right isClosed_im_nonneg
    have hK'Ω : K' ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} := fun z hz ↦
      ⟨by simpa using hΩ (hKΩ hz.1), hz.2⟩
    have hi : IntegrableOn (fun z ↦ f (conj z)) ((conjLIE : ℂ → ℂ) ⁻¹' K') := by
      have := (conjLIE.measurePreserving.integrableOn_comp_preimage
        conjLIE.toHomeomorph.measurableEmbedding (f := f) (s := K')).2
        (hf.integrableOn_compact_subset hK'Ω hK')
      simpa [Function.comp_def] using this
    have hi' : IntegrableOn (fun z ↦ star (f (conj z))) (K ∩ {z | z.im < 0}) :=
      ((starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap.integrable_comp
        (hi.mono_set fun z hz ↦ ⟨by simpa using hz.1, by simpa using hz.2.le⟩))
    exact hi'.congr_fun (fun z hz ↦ (starSchwarzReflection_of_im_neg hz.2).symm)
      (hKm.inter hHc)
  refine (hup.union hdown).mono_set fun z hz ↦ ?_
  by_cases h : 0 ≤ z.im
  · exact Or.inl ⟨hz, h⟩
  · exact Or.inr ⟨hz, not_le.1 h⟩

/-! ### Splitting integrals on the doubled domain -/

/-- An integral of a reflected function against a real test function on the doubled domain is the
upper half-plane integral plus the conjugate of the reflected upper half-plane integral. -/
private theorem integral_smul_starSchwarzReflection {f : ℂ → F} (a : ℂ → ℝ)
    (ha : Integrable (fun z ↦ a z • starSchwarzReflection f z)) :
    ∫ z, a z • starSchwarzReflection f z =
      (∫ z in {z : ℂ | 0 ≤ z.im}, a z • f z) +
        star (∫ z in {z : ℂ | 0 ≤ z.im}, a (conj z) • f z) := by
  rw [← integral_add_compl measurableSet_im_nonneg ha]
  congr 1
  · exact setIntegral_congr_fun measurableSet_im_nonneg fun z hz ↦ by
      rw [starSchwarzReflection_of_im_nonneg hz]
  · have hpre : (conjLIE : ℂ → ℂ) ⁻¹' {z : ℂ | 0 ≤ z.im}ᶜ = {z : ℂ | 0 < z.im} := by
      ext z
      simp
    rw [← conjLIE.measurePreserving.setIntegral_preimage_emb
      conjLIE.toHomeomorph.measurableEmbedding, hpre, ← integral_star,
      ← setIntegral_congr_set Complex.setOf_im_pos_ae_eq_setOf_im_nonneg]
    refine setIntegral_congr_fun (measurableSet_lt measurable_const Complex.measurable_im)
      fun z hz ↦ ?_
    simp only [conjLIE_apply]
    rw [starSchwarzReflection_of_im_neg (by simpa using hz), conj_conj, star_smul,
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
  set φs := conjTest hΩ φ
  -- The pairing of `φ` plus the conjugate of the pairing of `φ ∘ conj` vanishes.
  have hsym : halfPairing ξ η φ + star (halfPairing ξ η φs) = 0 := by
    have he := add_star_halfPairing h (φ + φs)
    have ho := halfPairing_eq_zero h (φ + -φs) fun x ↦ by
      simp [φs, conjTest_apply, Complex.conj_ofReal]
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
    rw [lineDeriv_conjTest, map_one]
  have hI (z : ℂ) : lineDeriv ℝ (φ : ℂ → ℝ) (conj z) I = -lineDeriv ℝ (φs : ℂ → ℝ) z I := by
    rw [lineDeriv_conjTest, conj_I, lineDeriv_neg, neg_neg]
  have h0 (z : ℂ) : (φ : ℂ → ℝ) (conj z) = (φs : ℂ → ℝ) z := (conjTest_apply hΩ φ z).symm
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
