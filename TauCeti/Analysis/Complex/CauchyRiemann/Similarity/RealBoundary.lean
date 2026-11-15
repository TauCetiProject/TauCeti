/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RealBoundaryReflection
public import TauCeti.Analysis.Complex.CauchyRiemann.Similarity.Weak

/-!
# The Similarity Principle and Unique Continuation up to a Real Boundary

Combining Schwarz reflection across the real axis for the weak linear Cauchy–Riemann equation with
a real boundary condition (`TauCeti.Analysis.Complex.CauchyRiemann.RealBoundaryReflection`) with the
Sobolev vector similarity principle (`TauCeti.Analysis.Complex.CauchyRiemann.Similarity.Weak`)
extends local holomorphic factorization, unique continuation, isolated zeros, and positive integer
vanishing orders up to the real boundary `{z : ℂ | z.im = 0}`.

Let `F` be a finite-dimensional complex normed space equipped with a continuous conjugate-linear
involution `star`, let `2 < p < ∞`, and let `Ω ⊆ ℂ` be a conjugation-invariant open set. Suppose
`C` is locally `Lᵖ` on `Ω ∩ {0 ≤ im}` and `ξ : ℂ → F` is continuous on `Ω ∩ {0 ≤ im}`, takes
`star`-fixed ("real") values on `Ω ∩ ℝ`, and solves `∂ₛξ + i ∂ₜξ + C(z) ξ = 0` weakly with the real
boundary condition (`HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ (fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))`).
Then `starSchwarzReflection ξ` solves the reflected linear Cauchy–Riemann equation on all of `Ω`
with `Lᵖ_loc` coefficient `starSchwarzReflectionCoeff C`. Applying the interior Sobolev similarity
principle to `starSchwarzReflection ξ` at any interior or boundary point `z₀ ∈ Ω ∩ {0 ≤ im}` gives
a full disc `ball z₀ r ⊆ Ω` on which `starSchwarzReflection ξ = Φ σ` (and hence `ξ = Φ σ` on the
half-disc `ball z₀ r ∩ {0 ≤ im}`), with `Φ` a continuous `W^{1,p}_loc` family of invertible
`ℂ`-linear maps and `σ` holomorphic.

## Main results

* `TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivRealBoundaryOn`: local similarity
  factorization `ξ = Φ σ` on `ball z₀ r ∩ {0 ≤ im}` around any interior or real-boundary point.
* `TauCeti.eventually_eq_zero_or_eventually_ne_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn`:
  local zero dichotomy within `{0 ≤ im}` around any interior or real-boundary point.
* `TauCeti.eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_forall_isBigO`,
  `TauCeti.eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_eventually_eq_zero`,
  `TauCeti.eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_frequently_eq_zero`,
  `TauCeti.eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_Ioo`: unique continuation up to
  the real boundary from infinite-order vanishing, vanishing on a relative neighbourhood, an
  accumulating zero set in `{0 ≤ im}`, or vanishing on a nonempty open interval `(a, b) ⊆ Ω ∩ ℝ`.
* `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_hasWeakConjWirtingerDerivRealBoundaryOn`:
  interior and boundary zeros of a nontrivial solution are isolated in `Ω ∩ {0 ≤ im}`.
* `TauCeti.exists_pos_isTheta_pow_of_hasWeakConjWirtingerDerivRealBoundaryOn`: every interior or
  real-boundary zero of a nontrivial solution has a positive integer vanishing order within
  `{0 ≤ im}`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3 and Appendix C.
-/

public noncomputable section

open Asymptotics Complex Filter MeasureTheory Metric Set TopologicalSpace
open scoped ComplexConjugate NNReal ENNReal Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [StarAddMonoid F] [StarModule ℂ F] [ContinuousStar F]
  {p : ℝ≥0∞} {Ω : Opens ℂ} {C : ℂ → F →L[ℝ] F} {ξ : ℂ → F}

/-- **The Sobolev similarity principle up to a real boundary.** Let `2 < p < ∞`, let `Ω ⊆ ℂ` be a
conjugation-invariant open set, let `C` be locally `Lᵖ` on `Ω ∩ {0 ≤ im}`, and let `ξ : ℂ → F` be
continuous on `Ω ∩ {0 ≤ im}`, fixed by `star` on `Ω ∩ ℝ`, and a weak real-boundary solution of
`∂ₛξ + i ∂ₜξ + C(z) ξ = 0`. Around every point `z₀ ∈ Ω ∩ {0 ≤ im}` (interior or on the real axis)
there is a disc `ball z₀ r ⊆ Ω` carrying a continuous `W^{1,p}_loc` family `Φ` of invertible
complex-linear endomorphisms of `F` and a holomorphic map `σ : ℂ → F` such that
`starSchwarzReflection ξ = Φ σ` on `ball z₀ r` and `ξ = Φ σ` on `ball z₀ r ∩ {0 ≤ im}`. -/
theorem exists_similarity_of_hasWeakConjWirtingerDerivRealBoundaryOn
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (hξ : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    {z₀ : ℂ} (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → F →L[ℂ] F) (σ : ℂ → F),
      ContinuousOn Φ (ball z₀ r) ∧ MemWkpLoc p (ball z₀ r) 1 Φ ∧
      (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧ DifferentiableOn ℂ σ (ball z₀ r) ∧
      EqOn (starSchwarzReflection ξ) (fun z ↦ Φ z (σ z)) (ball z₀ r) ∧
      EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r ∩ {z | 0 ≤ z.im}) := by
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  obtain ⟨r, hr, hrΩ, Φ, σ, hΦc, hΦw, hΦu, hσ, hrefl⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id hp hp_top Ω.isOpen
      (hC.starSchwarzReflectionCoeff hΩ)
      (hξ.isWeakLinearCauchyRiemannOn_starSchwarzReflection hp1 hp_top hΩ hC hξc hξr) hz₀.1
  refine ⟨r, hr, hrΩ, Φ, σ, hΦc, hΦw, hΦu, hσ, hrefl, fun z hz ↦ ?_⟩
  rw [← starSchwarzReflection_of_im_nonneg (ξ := ξ) hz.2]
  exact hrefl hz.1

/-- At every point of `Ω`, the Schwarz reflection of a real-boundary weak solution has a local
similarity factorization (`TauCeti.HasSimilarityFactorizationAt`). -/
private theorem hasSimilarityFactorizationAt_starSchwarzReflection
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (hξ : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    {z : ℂ} (hz : z ∈ Ω) :
    HasSimilarityFactorizationAt (starSchwarzReflection ξ) z := by
  have := FiniteDimensional.completeSpace ℂ F
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  obtain ⟨r, hr, -, Φ, σ, hΦc, -, hΦu, hσ, hrefl⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id hp hp_top Ω.isOpen
      (hC.starSchwarzReflectionCoeff hΩ)
      (hξ.isWeakLinearCauchyRiemannOn_starSchwarzReflection hp1 hp_top hΩ hC hξc hξr) hz
  let restL := ContinuousLinearMap.restrictScalarsL ℂ F F ℝ ℝ
  obtain ⟨u, hu⟩ := hΦu z (mem_ball_self hr)
  have hΦcR : ContinuousOn (fun w ↦ (Φ w).restrictScalars ℝ) (ball z r) :=
    restL.continuous.comp_continuousOn hΦc
  have hunit : IsUnit ((Φ z).restrictScalars ℝ) :=
    hu ▸ ⟨((ContinuousLinearEquiv.unitsEquiv ℂ F u).restrictScalars ℝ).toUnit, rfl⟩
  exact .of_eqOn_ball hr hΦcR hunit hσ hrefl

/-- **Local zero dichotomy up to a real boundary.** Around any interior or real-boundary point
`z₀ ∈ Ω ∩ {0 ≤ im}`, a weak real-boundary solution either vanishes on a neighbourhood of `z₀` within
`{0 ≤ im}` or has no zeros in a punctured neighbourhood of `z₀` within `{0 ≤ im}`. -/
theorem eventually_eq_zero_or_eventually_ne_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (hξ : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    {z₀ : ℂ} (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :
    (∀ᶠ z in 𝓝[{z | 0 ≤ z.im}] z₀, ξ z = 0) ∨
      ∀ᶠ z in 𝓝[{z | 0 ≤ z.im} \ {z₀}] z₀, ξ z ≠ 0 := by
  have := FiniteDimensional.completeSpace ℂ F
  have hc := continuousOn_starSchwarzReflection_of_symmetric hΩ hξc hξr
  have h := eventually_eq_zero_or_eventually_ne_zero_of_hasSimilarityFactorizationAt Ω.isOpen hc
    (fun z hz _ ↦ hasSimilarityFactorizationAt_starSchwarzReflection hp hp_top hΩ hC hξc hξr hξ hz)
    hz₀.1
  rcases h with h0 | hne
  · left
    exact eventually_nhdsWithin_iff.2 (h0.mono fun z hzr hz ↦ by
      rwa [starSchwarzReflection_of_im_nonneg hz] at hzr)
  · right
    have hsub : {z : ℂ | 0 ≤ z.im} \ {z₀} ⊆ {z₀}ᶜ := fun _ hz ↦ hz.2
    refine eventually_nhdsWithin_iff.2 ((eventually_nhdsWithin_iff.1
      (hne.filter_mono (nhdsWithin_mono z₀ hsub))).mono fun z hz hzm ↦ ?_)
    simpa only [starSchwarzReflection_of_im_nonneg hzm.1] using hz hzm

/-- **Unique continuation from an infinite-order interior or boundary zero.** Let `Ω` be
preconnected and conjugation-invariant. If a weak real-boundary solution satisfies
`ξ = O((z - z₀) ^ n)` within `{0 ≤ im}` for every `n : ℕ` at some interior or boundary point
`z₀ ∈ Ω ∩ {0 ≤ im}`, then `ξ` vanishes on `Ω ∩ {0 ≤ im}`. -/
theorem eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_forall_isBigO
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (hξ : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    {z₀ : ℂ} (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
    (h₀ : ∀ n : ℕ, ξ =O[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  have := FiniteDimensional.completeSpace ℂ F
  have hc := continuousOn_starSchwarzReflection_of_symmetric hΩ hξc hξr
  have he := eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO Ω.isOpen hΩc hc
    (fun z hz _ ↦ hasSimilarityFactorizationAt_starSchwarzReflection hp hp_top hΩ hC hξc hξr hξ hz)
    hz₀.1 fun n ↦ isBigO_starSchwarzReflection_sub_pow hz₀.2 (h₀ n)
  intro z hz
  simpa only [starSchwarzReflection_of_im_nonneg hz.2] using he hz.1

/-- **Unique continuation from a relative neighbourhood.** On a preconnected conjugation-invariant
open set `Ω`, a weak real-boundary solution vanishing on a neighbourhood of `z₀ ∈ Ω ∩ {0 ≤ im}`
within `{0 ≤ im}` vanishes on `Ω ∩ {0 ≤ im}`. -/
theorem eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_eventually_eq_zero
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (hξ : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    {z₀ : ℂ} (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
    (h₀ : ∀ᶠ z in 𝓝[{z | 0 ≤ z.im}] z₀, ξ z = 0) :
    EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
  eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_forall_isBigO hp hp_top hΩ hΩc hC hξc
    hξr hξ hz₀ fun _ ↦ (isBigO_zero _ _).congr' (EventuallyEq.symm h₀) EventuallyEq.rfl

/-- **Identity theorem up to a real boundary.** On a preconnected conjugation-invariant open set
`Ω`, if the zeros of a weak real-boundary solution in `{0 ≤ im}` accumulate at some interior or
real-boundary point `z₀ ∈ Ω ∩ {0 ≤ im}`, then `ξ` vanishes on `Ω ∩ {0 ≤ im}`. -/
theorem eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_frequently_eq_zero
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (hξ : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    {z₀ : ℂ} (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
    (h₀ : ∃ᶠ z in 𝓝[{z | 0 ≤ z.im} \ {z₀}] z₀, ξ z = 0) :
    EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  rcases eventually_eq_zero_or_eventually_ne_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn hp
      hp_top hΩ hC hξc hξr hξ hz₀ with hev | hne
  · exact eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_eventually_eq_zero hp hp_top hΩ
      hΩc hC hξc hξr hξ hz₀ hev
  · exact (h₀.and_eventually hne).exists.elim fun _ h ↦ (h.2 h.1).elim

/-- **Boundary unique continuation from a real interval.** On a preconnected conjugation-invariant
open set `Ω`, if a weak real-boundary solution vanishes along a nonempty open real interval
`(a, b) ⊆ Ω ∩ ℝ`, then it vanishes on all of `Ω ∩ {0 ≤ im}`. -/
theorem eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_Ioo
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (hξ : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    {a b : ℝ} (hab : a < b) (hI : MapsTo Complex.ofReal (Ioo a b) Ω)
    (h₀ : ∀ x ∈ Ioo a b, ξ x = 0) :
    EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  let x₀ : ℝ := (a + b) / 2
  have hx₀ : x₀ ∈ Ioo a b := ⟨by dsimp [x₀]; linarith, by dsimp [x₀]; linarith⟩
  refine eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_frequently_eq_zero hp hp_top hΩ
    hΩc hC hξc hξr hξ ⟨hI hx₀, by simp⟩ ?_
  rw [Filter.frequently_iff]
  intro U hU
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1
    ((Complex.continuous_ofReal.tendsto x₀).eventually hV)
  let ε : ℝ := min (δ / 2) ((b - a) / 4)
  have hε : 0 < ε := lt_min (half_pos hδ) (by linarith)
  have hεle : ε ≤ (b - a) / 4 := min_le_right _ _
  have hx₁ : x₀ + ε ∈ Ioo a b := ⟨by dsimp [x₀]; linarith, by dsimp [x₀]; linarith⟩
  have hdist : dist (x₀ + ε) x₀ < δ := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hε]
    exact (min_le_left _ _).trans_lt (half_lt_self hδ)
  refine ⟨((x₀ + ε : ℝ) : ℂ), hVU ⟨hball hdist, by simp, ?_⟩, h₀ (x₀ + ε) hx₁⟩
  simp [ne_of_gt hε]

/-- **Isolated interior and boundary zeros.** On a preconnected conjugation-invariant open set `Ω`,
the zeros in `Ω ∩ {0 ≤ im}` of a weak real-boundary solution not identically zero on `Ω ∩ {0 ≤ im}`
are isolated in `Ω ∩ {0 ≤ im}`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_hasWeakConjWirtingerDerivRealBoundaryOn
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (hξ : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hne : ∃ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, ξ z ≠ 0) :
    {z | ξ z ≠ 0} ∈ codiscreteWithin ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  have := FiniteDimensional.completeSpace ℂ F
  obtain ⟨z₁, hz₁, hξ₁⟩ := hne
  have hc := continuousOn_starSchwarzReflection_of_symmetric hΩ hξc hξr
  have hcod := setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt Ω.isOpen hΩc hc
    (fun z hz _ ↦ hasSimilarityFactorizationAt_starSchwarzReflection hp hp_top hΩ hC hξc hξr hξ hz)
    ⟨z₁, hz₁.1, by rwa [starSchwarzReflection_of_im_nonneg hz₁.2]⟩
  refine Filter.mem_of_superset
    (Filter.inter_mem (Filter.codiscreteWithin_mono inter_subset_left hcod)
      (Filter.self_mem_codiscreteWithin _)) fun z ⟨hzr, hz⟩ ↦ ?_
  simpa only [mem_ofPred_eq, starSchwarzReflection_of_im_nonneg hz.2] using hzr

/-- **Positive integer vanishing orders at interior and real-boundary zeros.** On a preconnected
conjugation-invariant open set `Ω`, at every interior or real-boundary zero `z₀ ∈ Ω ∩ {0 ≤ im}` of
a weak real-boundary solution not identically zero on `Ω ∩ {0 ≤ im}`, `‖ξ z‖` is comparable within
`{0 ≤ im}` to `‖z - z₀‖ ^ m` for some positive integer `m`. -/
theorem exists_pos_isTheta_pow_of_hasWeakConjWirtingerDerivRealBoundaryOn
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (hξ : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hne : ∃ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, ξ z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (hξ₀ : ξ z₀ = 0) :
    ∃ m : ℕ, 0 < m ∧ (ξ =Θ[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ m) := by
  have := FiniteDimensional.completeSpace ℂ F
  obtain ⟨z₁, hz₁, hξ₁⟩ := hne
  have hc := continuousOn_starSchwarzReflection_of_symmetric hΩ hξc hξr
  obtain ⟨m, hm, hΘ, -⟩ := exists_analyticOrderAt_eq_of_hasSimilarityFactorizationAt Ω.isOpen hΩc
    hc
    (fun z hz _ ↦ hasSimilarityFactorizationAt_starSchwarzReflection hp hp_top hΩ hC hξc hξr hξ hz)
    ⟨z₁, hz₁.1, by rwa [starSchwarzReflection_of_im_nonneg hz₁.2]⟩ hz₀.1
    (by rw [starSchwarzReflection_of_im_nonneg hz₀.2, hξ₀])
  have heq : starSchwarzReflection ξ =ᶠ[𝓝[{z | 0 ≤ z.im}] z₀] ξ :=
    eventually_nhdsWithin_of_forall fun z hz ↦ starSchwarzReflection_of_im_nonneg hz
  exact ⟨m, hm, ⟨(hΘ.isBigO.mono nhdsWithin_le_nhds).congr' heq EventuallyEq.rfl,
    (hΘ.isBigO_symm.mono nhdsWithin_le_nhds).congr' EventuallyEq.rfl heq⟩⟩

end TauCeti
