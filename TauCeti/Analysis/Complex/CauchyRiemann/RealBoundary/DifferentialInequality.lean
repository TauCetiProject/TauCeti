/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RealBoundary.Similarity
import TauCeti.MeasureTheory.Function.RankOne

/-!
# The similarity principle up to a real boundary for a weak Cauchy–Riemann inequality

Let `F` be a finite-dimensional complex normed space whose real structure is its `star` operation,
`Ω ⊆ ℂ` a conjugation-invariant open set and `p > 2`. Let `ξ` be continuous on the closed upper
part `Ω ∩ {0 ≤ im}`, real on `Ω ∩ ℝ`, with weak conjugate Wirtinger derivative `G = bar∂ξ` on
`Ω ∩ {0 ≤ im}` in the sense of the real boundary condition
(`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn`), satisfying the differential inequality

`‖bar∂ξ‖ ≤ g ‖ξ‖` almost everywhere on `Ω ∩ {0 ≤ im}`,

for a function `g` which is only locally `Lᵖ` up to the real axis. Then `ξ` solves
`∂ₛξ + i ∂ₜξ + C ξ = 0` weakly with the real boundary condition, for a real-linear coefficient
field `C` locally `Lᵖ` up to the axis with `‖C‖ ≤ c g`
(`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.exists_coeff_of_norm_le`), and
the similarity principle up to a real boundary
(`TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivRealBoundaryOn`) and its consequences
apply: unique continuation, isolated zeros and positive orders, also at points of the axis.

The coefficient is the rank-one operator `C = -2 G ⟪ξ, ·⟫ / ‖ξ‖²` for an inner product
transported from a Euclidean space
(`MeasureTheory.AEStronglyMeasurable.exists_clm_apply_eq`), since `F` carries a real structure but
no preferred inner product. This is the boundary counterpart of
`TauCeti.Analysis.Complex.CauchyRiemann.Similarity.DifferentialInequality`, and the form in which
the boundary similarity principle applies to pseudoholomorphic discs with totally real boundary
values: frozen at a point of the boundary condition, such a disc satisfies a differential
inequality of this kind with a locally bounded `g`.

## Main results

* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.exists_coeff_of_norm_le`: the
  differential inequality gives a locally `Lᵖ` coefficient field.
* `TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_norm_le`: the local
  factorization `ξ = Φ σ` on the upper part of a disc about any point of `Ω`.
* `TauCeti.eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_norm_le_of_eqOn_zero` and
  `TauCeti.eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_norm_le_of_forall_isBigO`:
  unique continuation up to the boundary.
* `setOf_ne_zero_mem_codiscreteWithin_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_norm_le`:
  isolated zeros up to the boundary.
* `TauCeti.exists_analyticOrderAt_eq_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_norm_le`:
  positive orders up to the boundary.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the Carleman similarity principle, with the rank-one coefficient of its proof)
  and Section 2.3 (its boundary version by reflection).
-/

public section

open Asymptotics Complex Filter MeasureTheory Metric Set Topology TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [StarAddMonoid F] [StarModule ℂ F] {Ω : Opens ℂ} {p : ℝ≥0∞} {ξ G : ℂ → F} {g : ℂ → ℝ}

/-- **The coefficient of a weak inequality up to a real boundary.** If `ξ` is continuous on
`Ω ∩ {0 ≤ im}` and has weak conjugate Wirtinger derivative `G` there, with the real boundary
condition, and `‖G‖ ≤ g ‖ξ‖` almost everywhere on `Ω ∩ {0 ≤ im}` for a function `g` locally `Lᵖ`
up to the axis, then `bar∂ξ = -½ C ξ` for a real-linear coefficient field `C` locally `Lᵖ` up to
the axis: `ξ` solves `∂ₛξ + i ∂ₜξ + C ξ = 0` with the real boundary condition. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.exists_coeff_of_norm_le
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ G)
    (hg : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hξ : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hle : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), ‖G z‖ ≤ g z * ‖ξ z‖) :
    ∃ C : ℂ → F →L[ℝ] F, MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C ∧
      HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z) := by
  classical
  set S := (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}
  have hS : MeasurableSet S := Ω.isOpen.measurableSet.inter (measurableSet_le measurable_const
    Complex.measurable_im)
  -- `G` vanishes almost everywhere where `ξ` does; `G'` vanishes there everywhere
  set G' : ℂ → F := fun z ↦ if ξ z = 0 then 0 else G z with hG'_def
  have hG' : G' =ᵐ[volume.restrict S] G := by
    filter_upwards [hle] with z hz
    by_cases h0 : ξ z = 0
    · rw [h0, norm_zero, mul_zero, norm_le_zero_iff] at hz
      simp [hG'_def, h0, hz]
    · simp [hG'_def, h0]
  -- the rank-one coefficient carrying `ξ` to `G'`, for an inner product transported to `F`
  obtain ⟨c, hc0, C, hCm, hCx, hCn⟩ := AEStronglyMeasurable.exists_clm_apply_eq (𝕜 := ℂ)
    ((hasWeakConjWirtingerDerivRealBoundaryOn_iff.1 h).2.2.1.aestronglyMeasurable.congr hG'.symm)
    (hξ.aestronglyMeasurable hS) fun z h0 ↦ by simp [hG'_def, h0]
  refine ⟨fun z ↦ (-2 : ℂ) • (C z).restrictScalars ℝ, (hg.const_smul (2 * c)).of_le
    (((ContinuousLinearMap.restrictScalarsL ℂ F F ℝ ℂ).continuous.comp_aestronglyMeasurable
      hCm).fun_const_smul _) ?_, h.congr_ae_deriv ?_⟩
  · -- `‖C z‖ ≤ c ‖G' z‖ / ‖ξ z‖ ≤ c |g z|`
    filter_upwards [hle] with z hz
    have hG'g : ‖G' z‖ / ‖ξ z‖ ≤ |g z| := by
      by_cases h0 : ξ z = 0
      · simp [hG'_def, h0]
      · simp only [hG'_def, h0, ite_false]
        exact div_le_of_le_mul₀ (norm_nonneg _) (abs_nonneg _)
          (hz.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)))
    simp only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul, abs_mul, norm_smul,
      ContinuousLinearMap.norm_restrictScalars, norm_neg, Complex.norm_two, abs_two,
      abs_of_nonneg hc0, mul_assoc]
    gcongr
    exact (hCn z).trans (by gcongr)
  · -- `-½ C ξ = G' = G` almost everywhere
    filter_upwards [hG'] with z hz
    rw [_root_.smul_apply, ContinuousLinearMap.coe_restrictScalars', hCx, hz, smul_smul]
    norm_num

variable [ContinuousStar F]

/-- **The similarity principle up to a real boundary for a weak differential inequality.** Let
`p > 2`, let `Ω` be conjugation invariant, and let `ξ` be continuous on `Ω ∩ {0 ≤ im}` and real on
`Ω ∩ ℝ`, with weak conjugate Wirtinger derivative `G` there for the real boundary condition and
`‖G‖ ≤ g ‖ξ‖` almost everywhere, `g` locally `Lᵖ` up to the axis. Then every point `z₀ ∈ Ω`, in
particular every real one, is the centre of a disc in `Ω` carrying a continuous family `Φ` of
invertible complex-linear maps and a holomorphic `σ` with `ξ = Φ σ` on the upper part of the
disc. -/
theorem exists_similarity_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_norm_le (hp : 2 < p)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hg : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ G)
    (hle : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), ‖G z‖ ≤ g z * ‖ξ z‖) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → F →L[ℂ] F) (σ : ℂ → F),
      ContinuousOn Φ (ball z₀ r) ∧ (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧
      EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨C, hC, heq⟩ := h.exists_coeff_of_norm_le hg hξc hle
  exact exists_similarity_of_hasWeakConjWirtingerDerivRealBoundaryOn hp hΩ hC hξc hξr heq hz₀

/-- **Unique continuation up to a real boundary for a weak differential inequality.** Let `p > 2`,
let `Ω` be conjugation invariant with `Ω ∩ {0 ≤ im}` preconnected, and let `ξ` be continuous on
`Ω ∩ {0 ≤ im}` and real on `Ω ∩ ℝ`, with weak conjugate Wirtinger derivative `G` there for the real
boundary condition and `‖G‖ ≤ g ‖ξ‖` almost everywhere, `g` locally `Lᵖ` up to the axis. If `ξ`
vanishes on a nonempty open subset of `Ω ∩ {0 ≤ im}`, it vanishes on `Ω ∩ {0 ≤ im}`. -/
theorem eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_norm_le_of_eqOn_zero (hp : 2 < p)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hg : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ G)
    (hle : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), ‖G z‖ ≤ g z * ‖ξ z‖)
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
    (h₀ : EqOn ξ 0 U) : EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨C, hC, heq⟩ := h.exists_coeff_of_norm_le hg hξc hle
  exact eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_eqOn_zero hp hΩ hΩc hC hξc hξr heq
    hU hUne hUΩ h₀

/-- **Unique continuation from a zero of infinite order, up to a real boundary, for a weak
differential inequality.** Let `p > 2`, let `Ω` be conjugation invariant with `Ω ∩ {0 ≤ im}`
preconnected, and let `ξ` be continuous on `Ω ∩ {0 ≤ im}` and real on `Ω ∩ ℝ`, with weak conjugate
Wirtinger derivative `G` there for the real boundary condition and `‖G‖ ≤ g ‖ξ‖` almost
everywhere, `g` locally `Lᵖ` up to the axis. If `ξ` vanishes to infinite order within
`{0 ≤ im}` at a point of `Ω ∩ {0 ≤ im}`, possibly on the real axis, it vanishes on
`Ω ∩ {0 ≤ im}`. -/
theorem eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_norm_le_of_forall_isBigO
    (hp : 2 < p) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΩc : IsPreconnected ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hg : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ G)
    (hle : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), ‖G z‖ ≤ g z * ‖ξ z‖) {z₀ : ℂ}
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
    (h₀ : ∀ n : ℕ, ξ =O[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨C, hC, heq⟩ := h.exists_coeff_of_norm_le hg hξc hle
  exact eqOn_zero_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_forall_isBigO hp hΩ hΩc hC hξc hξr
    heq hz₀ h₀

/-- **Isolated zeros up to a real boundary for a weak differential inequality.** Let `p > 2`, let
`Ω` be conjugation invariant with `Ω ∩ {0 ≤ im}` preconnected, and let `ξ` be continuous on
`Ω ∩ {0 ≤ im}` and real on `Ω ∩ ℝ`, with weak conjugate Wirtinger derivative `G` there for the real
boundary condition and `‖G‖ ≤ g ‖ξ‖` almost everywhere, `g` locally `Lᵖ` up to the axis. If `ξ` is
not identically zero on `Ω ∩ {0 ≤ im}`, its zeros form a discrete subset of `Ω ∩ {0 ≤ im}`, also
near the real axis. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_norm_le
    (hp : 2 < p) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΩc : IsPreconnected ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hg : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ G)
    (hle : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), ‖G z‖ ≤ g z * ‖ξ z‖)
    (hne : ∃ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, ξ z ≠ 0) :
    {z | ξ z ≠ 0} ∈ codiscreteWithin ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨C, hC, heq⟩ := h.exists_coeff_of_norm_le hg hξc hle
  exact setOf_ne_zero_mem_codiscreteWithin_of_hasWeakConjWirtingerDerivRealBoundaryOn hp hΩ hΩc hC
    hξc hξr heq hne

/-- **Positive orders up to a real boundary for a weak differential inequality.** Let `p > 2`, let
`Ω` be conjugation invariant with `Ω ∩ {0 ≤ im}` preconnected, and let `ξ` be continuous on
`Ω ∩ {0 ≤ im}` and real on `Ω ∩ ℝ`, with weak conjugate Wirtinger derivative `G` there for the real
boundary condition and `‖G‖ ≤ g ‖ξ‖` almost everywhere, `g` locally `Lᵖ` up to the axis, and not
identically zero on `Ω ∩ {0 ≤ im}`. At a zero `z₀ ∈ Ω ∩ {0 ≤ im}`, possibly on the real axis,
there is a positive `m` with `‖ξ z‖` comparable to `‖z - z₀‖ ^ m` for `z` near `z₀` in
`{0 ≤ im}`; it is the analytic order at `z₀` of the holomorphic factor of every similarity
factorization of the reflection of `ξ`. -/
theorem exists_analyticOrderAt_eq_of_hasWeakConjWirtingerDerivRealBoundaryOn_of_norm_le
    (hp : 2 < p) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΩc : IsPreconnected ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hg : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ G)
    (hle : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), ‖G z‖ ≤ g z * ‖ξ z‖)
    (hne : ∃ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, ξ z ≠ 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (hξ₀ : ξ z₀ = 0) :
    ∃ m : ℕ, 0 < m ∧ (ξ =Θ[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ m) ∧
      ∀ (Φ : ℂ → F →L[ℝ] F) (σ : ℂ → F), ContinuousAt Φ z₀ → IsUnit (Φ z₀) →
        AnalyticAt ℂ σ z₀ → (∀ᶠ z in 𝓝 z₀, starSchwarzReflection ξ z = Φ z (σ z)) →
          analyticOrderAt σ z₀ = m := by
  obtain ⟨C, hC, heq⟩ := h.exists_coeff_of_norm_le hg hξc hle
  exact exists_analyticOrderAt_eq_of_hasWeakConjWirtingerDerivRealBoundaryOn hp hΩ hΩc hC hξc hξr
    heq hne hz₀ hξ₀

end TauCeti
