/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sphere.Hersch.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.AlgebraicTopology.Singular.BrouwerFixedPoint

/-!
# Hersch's conformal balancing lemma

Adapted from Giada Franz's local formalization of Hersch's balancing lemma.

Let `(X, μ)` be a finite measure space and `Φ : X → E` an almost everywhere strongly measurable
map into a finite-dimensional real inner product space, taking values almost everywhere on the
unit sphere, whose fibres over its points are null. Then some conformal map `T_a` of Hersch
(`TauCeti.herschMap`), `‖a‖ < 1`, balances `Φ`: `∫ T_a ∘ Φ dμ = 0`.

For `μ = 0`, take `a = 0`. Otherwise the proof follows Hersch. The barycentre
`G(a) = ∫ T_a ∘ Φ dμ` is continuous on the closed unit
ball by dominated convergence: `‖T_a‖ ≤ 1` there, and `a ↦ T_a(Φ q)` is continuous at `a₀`
unless `⟪a₀, Φ q⟫ = -1`, which happens only for `‖a₀‖ = 1` and `Φ q = -a₀`, on a null set. On
the unit sphere `T_v(x) = v` for almost every `x = Φ q`, so `G(v) = μ(X) v`. If `G` had no zero
in the open ball, `-G / ‖G‖` would be a continuous self-map of the closed ball with values on the
sphere. Its fixed point `a`, given by Brouwer's theorem, lies on the sphere, where
`-G(a) / ‖G(a)‖ = -a`, which is impossible.

For a nonconstant holomorphic map of a compact Riemann surface to the sphere the fibres are
finite, so the hypothesis holds for its area measure.

## Main result

* `TauCeti.exists_integral_herschMap_eq_zero`: Hersch's balancing lemma.

## References

* J. Hersch, *Quatre propriétés isopérimétriques de membranes sphériques homogènes*,
  C. R. Acad. Sci. Paris Sér. A-B 270 (1970), A1645–A1648.
* P. C. Yang and S.-T. Yau, *Eigenvalues of the Laplacian of compact Riemann surfaces and
  minimal submanifolds*, Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) 7 (1980), 55–63, p. 59.
* O. Chodosh, *Lecture notes on minimal surfaces*, proof of Theorem 34.5.
-/

public section

open Filter Metric MeasureTheory Set Topology RealInnerProductSpace

namespace TauCeti

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace X] {μ : Measure X} {Φ : X → E}

/-- For each fixed `a` in the closed unit ball, `⟪a, Φ q⟫ ≠ -1` almost everywhere. -/
private theorem ae_inner_ne_neg_one (hΦ : ∀ᵐ q ∂μ, Φ q ∈ sphere (0 : E) 1)
    (hfib : ∀ v ∈ sphere (0 : E) 1, μ (Φ ⁻¹' {v}) = 0) {a : E} (ha : ‖a‖ ≤ 1) :
    ∀ᵐ q ∂μ, ⟪a, Φ q⟫ ≠ -1 := by
  rcases ha.lt_or_eq with ha | ha
  · exact hΦ.mono fun q hq ↦ inner_ne_neg_one ha (mem_sphere_zero_iff_norm.1 hq).le
  · have hnull : ∀ᵐ q ∂μ, Φ q ≠ -a := by
      rw [ae_iff]
      simpa only [not_not, Set.preimage, mem_singleton_iff] using hfib (-a) (by simp [ha])
    filter_upwards [hΦ, hnull] with q hq hne
    intro hinner
    exact hne ((inner_eq_neg_one_iff_of_norm_eq_one (mem_sphere_zero_iff_norm.1 hq) ha).1
      (by rwa [real_inner_comm]))

/-- On the unit sphere, `∫ T_v ∘ Φ dμ = μ(X) v`. -/
private theorem integral_herschMap_of_norm_eq_one [CompleteSpace E]
    (hΦ : ∀ᵐ q ∂μ, Φ q ∈ sphere (0 : E) 1)
    (hfib : ∀ v ∈ sphere (0 : E) 1, μ (Φ ⁻¹' {v}) = 0) {v : E} (hv : ‖v‖ = 1) :
    ∫ q, herschMap v (Φ q) ∂μ = μ.real univ • v := by
  rw [← integral_const]
  refine integral_congr_ae ?_
  filter_upwards [ae_inner_ne_neg_one hΦ hfib hv.le] with q hq
  exact herschMap_of_norm_eq_one hv hq

variable [FiniteDimensional ℝ E]

/-- The barycentre `a ↦ ∫ T_a ∘ Φ dμ` is continuous on the closed unit ball. -/
private theorem continuousOn_integral_herschMap [IsFiniteMeasure μ] (hΦm : AEStronglyMeasurable Φ μ)
    (hΦ : ∀ᵐ q ∂μ, Φ q ∈ sphere (0 : E) 1) (hfib : ∀ v ∈ sphere (0 : E) 1, μ (Φ ⁻¹' {v}) = 0) :
    ContinuousOn (fun a ↦ ∫ q, herschMap a (Φ q) ∂μ) (closedBall (0 : E) 1) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  intro a ha
  rw [mem_closedBall_zero_iff] at ha
  refine continuousWithinAt_of_dominated (bound := fun _ ↦ 1)
    (Eventually.of_forall fun b ↦
      ((measurable_herschMap b).comp_aemeasurable hΦm.aemeasurable).aestronglyMeasurable)
    (eventually_nhdsWithin_of_forall fun b hb ↦ hΦ.mono fun q hq ↦
      norm_herschMap_le_one (mem_closedBall_zero_iff.1 hb) (mem_sphere_zero_iff_norm.1 hq))
    (integrable_const 1) ?_
  filter_upwards [ae_inner_ne_neg_one hΦ hfib ha] with q hq
  exact (continuousAt_herschMap_left hq).continuousWithinAt

/-- **Hersch's balancing lemma.** Let `μ` be a finite measure and `Φ` an almost everywhere
strongly measurable map into a finite-dimensional real inner product space, taking values on the
unit sphere almost everywhere, whose fibres over its points are null. Then there is `a` with
`‖a‖ < 1` such that the composition of `Φ` with Hersch's conformal map `T_a` has barycentre zero:
`∫ T_a ∘ Φ dμ = 0`. -/
theorem exists_integral_herschMap_eq_zero [IsFiniteMeasure μ]
    (hΦm : AEStronglyMeasurable Φ μ) (hΦ : ∀ᵐ q ∂μ, Φ q ∈ sphere (0 : E) 1)
    (hfib : ∀ v ∈ sphere (0 : E) 1, μ (Φ ⁻¹' {v}) = 0) :
    ∃ a ∈ ball (0 : E) 1, ∫ q, herschMap a (Φ q) ∂μ = 0 := by
  by_cases hμ : μ = 0
  · subst μ
    exact ⟨0, by simp, by simp⟩
  set G : E → E := fun a ↦ ∫ q, herschMap a (Φ q) ∂μ with hG
  have hc : 0 < μ.real univ := by
    rw [measureReal_def, ENNReal.toReal_pos_iff]
    exact ⟨Measure.measure_univ_pos.2 hμ, measure_lt_top μ univ⟩
  by_contra! hne
  have hG0 : ∀ a ∈ closedBall (0 : E) 1, G a ≠ 0 := by
    intro a ha
    rw [mem_closedBall_zero_iff] at ha
    rcases ha.lt_or_eq with ha | ha
    · exact hne a (mem_ball_zero_iff.2 ha)
    · simp only [hG]
      rw [integral_herschMap_of_norm_eq_one hΦ hfib ha]
      exact smul_ne_zero hc.ne' (by rintro rfl; simp at ha)
  have hGc := continuousOn_integral_herschMap hΦm hΦ hfib
  have hgc : ContinuousOn (fun a ↦ -(‖G a‖⁻¹ • G a)) (closedBall (0 : E) 1) :=
    ((hGc.norm.inv₀ fun a ha ↦ norm_ne_zero_iff.2 (hG0 a ha)).smul hGc).neg
  have hunit : ∀ a ∈ closedBall (0 : E) 1, ‖-(‖G a‖⁻¹ • G a)‖ = 1 := fun a ha ↦ by
    rw [norm_neg]
    exact norm_smul_inv_norm (hG0 a ha)
  have hgmaps : MapsTo (fun a ↦ -(‖G a‖⁻¹ • G a)) (closedBall (0 : E) 1)
      (closedBall (0 : E) 1) := by
    intro a ha
    exact mem_closedBall_zero_iff.2 (hunit a ha).le
  obtain ⟨a, ha, hfix⟩ := brouwerFixedPoint_compactConvex_continuousOn
    (isCompact_closedBall 0 1) (convex_closedBall 0 1) (nonempty_closedBall.2 zero_le_one)
    hgc hgmaps
  have hfix' : -(‖G a‖⁻¹ • G a) = a := hfix
  have hnorm : ‖a‖ = 1 := hfix' ▸ hunit a ha
  have hGa : G a = μ.real univ • a := integral_herschMap_of_norm_eq_one hΦ hfib hnorm
  rw [hGa] at hfix'
  have hneg : -a = a := by
    simpa [norm_smul_of_nonneg hc.le, hnorm, smul_smul, hc.ne'] using hfix'
  rw [neg_eq_iff_add_eq_zero, ← two_smul ℝ] at hneg
  have : a = 0 := (smul_eq_zero.1 hneg).resolve_left two_ne_zero
  simp [this] at hnorm

end TauCeti
