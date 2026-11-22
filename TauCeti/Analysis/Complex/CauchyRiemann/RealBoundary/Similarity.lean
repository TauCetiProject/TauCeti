/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RealBoundary.Reflection
public import TauCeti.Analysis.Complex.CauchyRiemann.Similarity

/-!
# The similarity principle up to a real boundary

Let `F` be a finite-dimensional complex normed space whose real structure is its `star`
operation, let `Ω ⊆ ℂ` be a conjugation-invariant open set and write `Ω⁺ = Ω ∩ {0 ≤ im}` for its
closed upper part. Let `ξ` be continuous on `Ω⁺`, real on the real axis, and a weak solution of
`∂ₛξ + i ∂ₜξ + C ξ = 0` on `Ω⁺` with the real boundary condition, in the sense of
`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ (fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))`, for a
field `C` of real-linear endomorphisms of `F` that is locally `Lᵖ` up to the boundary, `p > 2`.
This is the boundary version of the similarity principle and its consequences, for the structure
`i` and the totally real boundary condition `ℝⁿ ⊆ ℂⁿ` (with `F = Fin n → ℂ`).

The reflection `TauCeti.starSchwarzReflection ξ` solves the reflected equation weakly on all of
`Ω` (`TauCeti.Analysis.Complex.CauchyRiemann.RealBoundary.Reflection`), so the interior theorems
of `TauCeti.Analysis.Complex.CauchyRiemann.Similarity` apply to it, and their conclusions
restrict to `Ω⁺`, where the reflection is `ξ`.

## Main results

* `TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivRealBoundaryOn`: near every point of
  `Ω`, boundary points included, `ξ = Φ σ` on the upper part of a disc, with `Φ` a continuous
  family of invertible complex-linear maps and `σ` holomorphic on the whole disc.
* `HasWeakConjWirtingerDerivRealBoundaryOn.hasSimilarityFactorizationAt_starSchwarzReflection`:
  the reflection has a similarity factorization at every point of `Ω`.
* `TauCeti.eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_eqOn_zero` and
  `TauCeti.eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_forall_isBigO`: unique
  continuation on a preconnected `Ω⁺`, from a nonempty open set or from a zero of infinite order,
  which may lie on the boundary.
* `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_hasWeakConjWirtingerDerivRealBoundaryOn`: the
  zeros of a solution not identically zero are isolated in `Ω⁺`, up to the boundary.
* `TauCeti.exists_analyticOrderAt_eq_of_hasWeakConjWirtingerDerivRealBoundaryOn`: each zero in
  `Ω⁺` of a solution not identically zero there has a finite positive order `m`, with
  `‖ξ z‖ ≍ ‖z - z₀‖ ^ m` within `Ω⁺`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications **52**, 2012, Section 2.3.
-/

public section

open Asymptotics Complex Filter Metric MeasureTheory Set TopologicalSpace Topology
open scoped ComplexConjugate ENNReal

namespace TauCeti

/-! ### The reflected solution -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [StarAddMonoid F] [StarModule ℂ F] [ContinuousStar F]
  {Ω : Opens ℂ} {ξ : ℂ → F} {C : ℂ → F →L[ℝ] F} {p : ℝ≥0∞}

/-- **Similarity factorization of the reflection.** Let `p > 2`, let `Ω` be conjugation invariant,
and let `ξ` be continuous on `Ω ∩ {0 ≤ im}` and real on `Ω ∩ ℝ`, solving
`∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the real boundary condition, for a
coefficient field `C` locally `Lᵖ` up to the boundary. Then the reflection of `ξ` has a similarity
factorization at every point of `Ω`. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.hasSimilarityFactorizationAt_starSchwarzReflection
    (hp : 2 < p) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) : HasSimilarityFactorizationAt (starSchwarzReflection ξ) z₀ :=
  hasSimilarityFactorizationAt_of_hasWeakConjWirtingerDerivOn hp (hC.starSchwarzReflectionCoeff hΩ)
    (continuousOn_starSchwarzReflection_of_symmetric hΩ hξc hξr)
    (h.hasWeakConjWirtingerDerivOn_starSchwarzReflectionCoeff hΩ) hz₀

/-- **The similarity principle up to a real boundary.** Let `p > 2`, let `Ω` be conjugation
invariant, and let `ξ` be continuous on `Ω ∩ {0 ≤ im}` and real on `Ω ∩ ℝ`, solving
`∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the real boundary condition, for a
coefficient field `C` locally `Lᵖ` up to the boundary. Then every point `z₀ ∈ Ω`, in particular
every real one, is the centre of a disc in `Ω` carrying a continuous family `Φ` of invertible
complex-linear maps and a holomorphic `σ` with `ξ = Φ σ` on the upper part of the disc. -/
theorem exists_similarity_of_hasWeakConjWirtingerDerivRealBoundaryOn (hp : 2 < p)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → F →L[ℂ] F) (σ : ℂ → F),
      ContinuousOn Φ (ball z₀ r) ∧ (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧
      EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨r, hr, hrΩ, Φ, σ, hΦ, hΦu, hσ, hξσ⟩ := exists_similarity_of_hasWeakConjWirtingerDerivOn
    hp (hC.starSchwarzReflectionCoeff hΩ)
    (continuousOn_starSchwarzReflection_of_symmetric hΩ hξc hξr)
    (h.hasWeakConjWirtingerDerivOn_starSchwarzReflectionCoeff hΩ) hz₀
  exact ⟨r, hr, hrΩ, Φ, σ, hΦ, hΦu, hσ, fun z hz ↦
    (starSchwarzReflection_of_im_nonneg hz.2.out).symm.trans (hξσ hz.1)⟩

omit [FiniteDimensional ℂ F] in
/-- The reflected solution on a preconnected open set containing `Ω ∩ {0 ≤ im}`, where it agrees
with `ξ`: the data to which the interior unique continuation theorems apply. -/
private theorem exists_opens_reflection (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΩc : IsPreconnected ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z)) :
    ∃ W : Opens ℂ, IsPreconnected (W : Set ℂ) ∧ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ W ∧
      MemLpLoc p W (starSchwarzReflectionCoeff C) ∧
      ContinuousOn (starSchwarzReflection ξ) W ∧
      HasWeakConjWirtingerDerivOn volume W (starSchwarzReflection ξ)
        (fun z ↦ (2 : ℂ)⁻¹ • -starSchwarzReflectionCoeff C z (starSchwarzReflection ξ z)) := by
  obtain ⟨W, hWΩ, hWo, hWc, hW⟩ :=
    exists_isPreconnected_isOpen_superset_inter_im_nonneg_of_symmetric Ω.isOpen hΩ hΩc
  exact ⟨⟨W, hWo⟩, hWc, hW, (hC.starSchwarzReflectionCoeff hΩ).mono_set hWΩ,
    (continuousOn_starSchwarzReflection_of_symmetric hΩ hξc hξr).mono hWΩ,
    (h.hasWeakConjWirtingerDerivOn_starSchwarzReflectionCoeff hΩ).mono hWΩ⟩

omit [NormedSpace ℂ F] [FiniteDimensional ℂ F] [StarModule ℂ F] [ContinuousStar F] in
/-- If the reflection of `ξ` vanishes on `T`, then `ξ` vanishes on every part of `T` in the closed
upper half-plane. -/
private theorem eqOn_zero_of_eqOn_starSchwarzReflection {S T : Set ℂ}
    (hS : S ⊆ {z | 0 ≤ z.im}) (hST : S ⊆ T) (h : EqOn (starSchwarzReflection ξ) 0 T) :
    EqOn ξ 0 S :=
  fun _ hz ↦ (starSchwarzReflection_of_im_nonneg (hS hz).out).symm.trans (h (hST hz))

/-- **Unique continuation up to a real boundary.** Let `p > 2`, let `Ω` be conjugation invariant
with `Ω ∩ {0 ≤ im}` preconnected, and let `ξ` be continuous on `Ω ∩ {0 ≤ im}` and real on `Ω ∩ ℝ`,
solving `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the real boundary condition, for a
coefficient field `C` locally `Lᵖ` up to the boundary. If `ξ` vanishes on a nonempty open subset
of `Ω ∩ {0 ≤ im}`, it vanishes on `Ω ∩ {0 ≤ im}`. -/
theorem eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_eqOn_zero (hp : 2 < p)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
    (h₀ : EqOn ξ 0 U) : EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨W, hWc, hW, hRC, hRc, hReq⟩ := exists_opens_reflection hΩ hΩc hC hξc hξr h
  refine eqOn_zero_of_eqOn_starSchwarzReflection inter_subset_right hW
    (eqOn_zero_of_hasWeakConjWirtingerDerivOn_of_eqOn_zero hp hWc hRC hRc hReq hU hUne
      (hUΩ.trans hW) fun z hz ↦ ?_)
  exact (starSchwarzReflection_of_im_nonneg (hUΩ hz).2.out).trans (h₀ hz)

/-- **Unique continuation from a zero of infinite order, up to a real boundary.** Let `p > 2`, let
`Ω` be conjugation invariant with `Ω ∩ {0 ≤ im}` preconnected, and let `ξ` be continuous on
`Ω ∩ {0 ≤ im}` and real on `Ω ∩ ℝ`, solving `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}`
with the real boundary condition, for a coefficient field `C` locally `Lᵖ` up to the boundary. If
`ξ` vanishes to infinite order within `{0 ≤ im}` at a point of `Ω ∩ {0 ≤ im}`, possibly on the
real axis, it vanishes on `Ω ∩ {0 ≤ im}`. -/
theorem eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_forall_isBigO (hp : 2 < p)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
    (h₀ : ∀ n : ℕ, ξ =O[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨W, hWc, hW, hRC, hRc, hReq⟩ := exists_opens_reflection hΩ hΩc hC hξc hξr h
  exact eqOn_zero_of_eqOn_starSchwarzReflection inter_subset_right hW
    (eqOn_zero_of_hasWeakConjWirtingerDerivOn_of_forall_isBigO hp hWc hRC hRc hReq (hW hz₀)
      fun n ↦ isBigO_starSchwarzReflection_sub_pow hz₀.2.out (h₀ n))

/-- **Isolated zeros up to a real boundary.** Let `p > 2`, let `Ω` be conjugation invariant with
`Ω ∩ {0 ≤ im}` preconnected, and let `ξ` be continuous on `Ω ∩ {0 ≤ im}` and real on `Ω ∩ ℝ`,
solving `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the real boundary condition, for a
coefficient field `C` locally `Lᵖ` up to the boundary. If `ξ` is not identically zero on
`Ω ∩ {0 ≤ im}`, its zeros form a discrete subset of `Ω ∩ {0 ≤ im}`, also near the real axis. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_hasWeakConjWirtingerDerivRealBoundaryOn
    (hp : 2 < p) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΩc : IsPreconnected ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hne : ∃ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, ξ z ≠ 0) :
    {z | ξ z ≠ 0} ∈ codiscreteWithin ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨W, hWc, hW, hRC, hRc, hReq⟩ := exists_opens_reflection hΩ hΩc hC hξc hξr h
  obtain ⟨z₁, hz₁, hξz₁⟩ := hne
  have hR := setOf_ne_zero_mem_codiscreteWithin_of_hasWeakConjWirtingerDerivOn hp hWc hRC hRc
    hReq ⟨z₁, hW hz₁, by rwa [starSchwarzReflection_of_im_nonneg hz₁.2.out]⟩
  filter_upwards [codiscreteWithin_mono hW hR, self_mem_codiscreteWithin _] with z hz hzΩ
  rwa [starSchwarzReflection_of_im_nonneg hzΩ.2.out] at hz

/-- **Positive orders up to a real boundary.** Let `p > 2`, let `Ω` be conjugation invariant with
`Ω ∩ {0 ≤ im}` preconnected, and let `ξ` be continuous on `Ω ∩ {0 ≤ im}` and real on `Ω ∩ ℝ`,
solving `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the real boundary condition, for a
coefficient field `C` locally `Lᵖ` up to the boundary, and not identically zero on
`Ω ∩ {0 ≤ im}`. At a zero `z₀ ∈ Ω ∩ {0 ≤ im}`, possibly on the real axis, there is a positive
`m` with `‖ξ z‖` comparable to `‖z - z₀‖ ^ m` for `z` near `z₀` in `{0 ≤ im}`; it is the analytic
order at `z₀` of the holomorphic factor of every similarity factorization of the reflection of
`ξ`. -/
theorem exists_analyticOrderAt_eq_of_hasWeakConjWirtingerDerivRealBoundaryOn (hp : 2 < p)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hne : ∃ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, ξ z ≠ 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (hξ₀ : ξ z₀ = 0) :
    ∃ m : ℕ, 0 < m ∧ (ξ =Θ[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ m) ∧
      ∀ (Φ : ℂ → F →L[ℝ] F) (σ : ℂ → F), ContinuousAt Φ z₀ → IsUnit (Φ z₀) →
        AnalyticAt ℂ σ z₀ → (∀ᶠ z in 𝓝 z₀, starSchwarzReflection ξ z = Φ z (σ z)) →
          analyticOrderAt σ z₀ = m := by
  obtain ⟨W, hWc, hW, hRC, hRc, hReq⟩ := exists_opens_reflection hΩ hΩc hC hξc hξr h
  obtain ⟨z₁, hz₁, hξz₁⟩ := hne
  obtain ⟨m, hm, hθ, hord⟩ := exists_analyticOrderAt_eq_of_hasWeakConjWirtingerDerivOn hp hWc hRC
    hRc hReq ⟨z₁, hW hz₁, by rwa [starSchwarzReflection_of_im_nonneg hz₁.2.out]⟩ (hW hz₀)
    (by rwa [starSchwarzReflection_of_im_nonneg hz₀.2.out])
  exact ⟨m, hm, EventuallyEq.trans_isTheta (eventually_nhdsWithin_of_forall fun z hz ↦
    (starSchwarzReflection_of_im_nonneg hz.out).symm) (hθ.mono nhdsWithin_le_nhds), hord⟩

end TauCeti
