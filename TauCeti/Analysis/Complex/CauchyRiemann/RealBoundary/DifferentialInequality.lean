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
(`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.exists_memLpLoc_eq_neg_smul_of_norm_le`), and
the similarity principle up to a real boundary
(`TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivRealBoundaryOn`) and its consequences
apply: unique continuation, isolated zeros and positive orders, also at points of the axis.

The coefficient is the rank-one operator `C = -2 G ⟪ξ, ·⟫ / ‖ξ‖²` for an inner product
transported from a Euclidean space, since `F` carries a real structure but no preferred inner
product. This is the boundary counterpart of
`TauCeti.Analysis.Complex.CauchyRiemann.Similarity.DifferentialInequality`, and the form in which
the boundary similarity principle applies to pseudoholomorphic discs with totally real boundary
values: frozen at a point of the boundary condition, such a disc satisfies a differential
inequality of this kind with a locally bounded `g`.

## Main results

* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.exists_memLpLoc_eq_neg_smul_of_norm_le`: the
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

omit [FiniteDimensional ℂ F] [StarAddMonoid F] [StarModule ℂ F] in
/-- The rank-one coefficient `-2 y ⟪e x, e ·⟫ / ‖e x‖²` built from a vector `y` with
`‖y‖ ≤ c ‖x‖` has operator norm at most `2 ‖e‖ ‖e⁻¹‖ |c|`. -/
private theorem opNorm_le_of_forall_apply_eq_rankOneDivNormSq {E' : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] (e : F ≃L[ℂ] E') {y x : F} {c : ℝ}
    (hc : ‖y‖ ≤ c * ‖x‖) {R : F →L[ℝ] F}
    (hR : ∀ v, R v = (-2 : ℂ) • rankOneDivNormSq ℂ y (e x) (e v)) :
    ‖R‖ ≤ 2 * ‖(e : F →L[ℂ] E')‖ * ‖(e.symm : E' →L[ℂ] F)‖ * |c| := by
  have hxe : ‖x‖ ≤ ‖(e.symm : E' →L[ℂ] F)‖ * ‖e x‖ := by
    simpa using (e.symm : E' →L[ℂ] F).le_opNorm (e x)
  have hye : ‖y‖ / ‖e x‖ ≤ ‖(e.symm : E' →L[ℂ] F)‖ * |c| :=
    div_le_of_le_mul₀ (norm_nonneg _) (by positivity) (hc.trans (by
      calc c * ‖x‖ ≤ |c| * (‖(e.symm : E' →L[ℂ] F)‖ * ‖e x‖) :=
            mul_le_mul (le_abs_self _) hxe (norm_nonneg _) (abs_nonneg _)
        _ = _ := by ring))
  calc ‖R‖ ≤ 2 * (‖y‖ / ‖e x‖ * ‖(e : F →L[ℂ] E')‖) := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
        rw [hR, norm_smul, norm_neg, Complex.norm_two]
        calc 2 * ‖rankOneDivNormSq ℂ y (e x) (e v)‖
            ≤ 2 * (‖rankOneDivNormSq ℂ y (e x)‖ * (‖(e : F →L[ℂ] E')‖ * ‖v‖)) := by
              gcongr
              exact (ContinuousLinearMap.le_opNorm _ _).trans
                (by gcongr; exact (e : F →L[ℂ] E').le_opNorm v)
          _ = 2 * (‖y‖ / ‖e x‖ * ‖(e : F →L[ℂ] E')‖) * ‖v‖ := by
              rw [norm_rankOneDivNormSq]
              ring
    _ ≤ 2 * (‖(e.symm : E' →L[ℂ] F)‖ * |c| * ‖(e : F →L[ℂ] E')‖) := by gcongr
    _ = _ := by ring

/-- **The coefficient of a weak inequality up to a real boundary.** If `ξ` is continuous on
`Ω ∩ {0 ≤ im}` and has weak conjugate Wirtinger derivative `G` there, with the real boundary
condition, and `‖G‖ ≤ g ‖ξ‖` almost everywhere on `Ω ∩ {0 ≤ im}` for a function `g` locally `Lᵖ`
up to the axis, then `bar∂ξ = -½ C ξ` for a real-linear coefficient field `C` locally `Lᵖ` up to
the axis: `ξ` solves `∂ₛξ + i ∂ₜξ + C ξ = 0` with the real boundary condition. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.exists_memLpLoc_eq_neg_smul_of_norm_le
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ G)
    (hg : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hξ : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hle : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), ‖G z‖ ≤ g z * ‖ξ z‖) :
    ∃ C : ℂ → F →L[ℝ] F, MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C ∧
      HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z) := by
  set S := (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}
  have hS : MeasurableSet S := Ω.isOpen.measurableSet.inter (measurableSet_le measurable_const
    Complex.measurable_im)
  -- an inner product on `F`, transported from a Euclidean space
  let e : F ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ F)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let eL : F →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ F)) := e
  let eR : EuclideanSpace ℂ (Fin (Module.finrank ℂ F)) →L[ℂ] F := e.symm
  -- `C z = -2 G ⟪e ξ, e ·⟫ / ‖e ξ‖²`, assembled by a continuous linear map from the rank-one part
  let T : (EuclideanSpace ℂ (Fin (Module.finrank ℂ F)) →L[ℂ] F) →L[ℂ] F →L[ℝ] F :=
    ContinuousLinearMap.restrictScalarsL ℂ F F ℝ ℂ ∘L
      ((-2 : ℂ) • (ContinuousLinearMap.compL ℂ F _ F).flip eL)
  set C : ℂ → F →L[ℝ] F := fun z ↦ T (rankOneDivNormSq ℂ (G z) (e (ξ z))) with hC_def
  have hCapp (z : ℂ) (v : F) :
      C z v = (-2 : ℂ) • rankOneDivNormSq ℂ (G z) (e (ξ z)) (e v) := by
    simp [hC_def, T, eL]
  have hCm : AEStronglyMeasurable C (volume.restrict S) :=
    T.continuous.comp_aestronglyMeasurable
      ((hasWeakConjWirtingerDerivRealBoundaryOn_iff.1 h).2.2.1.aestronglyMeasurable.rankOneDivNormSq
        (e.continuous.comp_aestronglyMeasurable (hξ.aestronglyMeasurable hS)))
  have hc : 0 ≤ 2 * ‖eL‖ * ‖eR‖ := by positivity
  refine ⟨C, (hg.const_smul (2 * ‖eL‖ * ‖eR‖)).of_le hCm ?_, h.congr_ae_deriv ?_⟩
  · -- `‖C z‖ ≤ 2 ‖e‖ ‖e⁻¹‖ |g z|`
    filter_upwards [hle] with z hz
    rw [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc]
    exact opNorm_le_of_forall_apply_eq_rankOneDivNormSq e hz (hCapp z)
  · -- `-½ C ξ = G`, also where `ξ = 0`, since there `G = 0`
    filter_upwards [hle] with z hz
    by_cases h0 : ξ z = 0
    · rw [h0, norm_zero, mul_zero, norm_le_zero_iff] at hz
      simp [hz, h0]
    · rw [hCapp, rankOneDivNormSq_apply_self (𝕜 := ℂ) (G z) (x := e (ξ z))
        (e.map_ne_zero_iff.2 h0), smul_smul]
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
  obtain ⟨C, hC, heq⟩ := h.exists_memLpLoc_eq_neg_smul_of_norm_le hg hξc hle
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
  obtain ⟨C, hC, heq⟩ := h.exists_memLpLoc_eq_neg_smul_of_norm_le hg hξc hle
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
  obtain ⟨C, hC, heq⟩ := h.exists_memLpLoc_eq_neg_smul_of_norm_le hg hξc hle
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
  obtain ⟨C, hC, heq⟩ := h.exists_memLpLoc_eq_neg_smul_of_norm_le hg hξc hle
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
  obtain ⟨C, hC, heq⟩ := h.exists_memLpLoc_eq_neg_smul_of_norm_le hg hξc hle
  exact exists_analyticOrderAt_eq_of_hasWeakConjWirtingerDerivRealBoundaryOn hp hΩ hΩc hC hξc hξr
    heq hne hz₀ hξ₀

end TauCeti
