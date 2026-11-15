/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Order.LiminfLimsup
public import TauCeti.Analysis.Calculus.FDeriv.ImageCone
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz

/-!
# Densities for the Euclidean Hausdorff measure under bi-Lipschitz maps and in `k`-planes

The `k`-dimensional density of a set `S` in a metric space at a point `x` compares
`μHE[k] (S ∩ closedBall x r)` with `ω_k r ^ k`, the volume of a ball of radius `r` in
`EuclideanSpace ℝ (Fin k)`. This file proves general facts about these densities, none of which
involves rectifiability:

* a map that is `b`-Lipschitz on `G` with `a`-Lipschitz inverse moves a point of density one of `G`
  to a point of `ψ '' G` whose upper and lower densities lie between `(a b) ^ (-k)` and
  `(a b) ^ k`;
* **Lebesgue's density theorem in a `k`-plane**: every subset of an isometric copy of
  `EuclideanSpace ℝ (Fin k)` has density one at almost every one of its points. This is
  transported from Mathlib's `Besicovitch.ae_tendsto_measure_inter_div`;
* combining the two, every subset of a bi-Lipschitz image of a subset of a `k`-plane has its
  densities between `(a b) ^ (-k)` and `(a b) ^ k` almost everywhere;
* removing a part of density zero from a set does not lower its upper density;
* at a Haar density-one point of an arbitrary parameter set, the positive tangent cone is the
  whole space, relative derivatives are unique, and an inverse-Lipschitz parametrization has an
  antilipschitz derivative and positive directional lower Hausdorff density in every direction of
  its derivative range.

Together with the zero-density theorem
`TauCeti.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`, these are the ingredients of
the density theorem, approximate tangent plane uniqueness, and tangential differentiation on
rectifiable sets.

## Main results

* `LipschitzOnWith.limsup_euclideanHausdorffMeasure_image_inter_closedBall_div_le` and
  `LipschitzOnWith.le_liminf_euclideanHausdorffMeasure_image_inter_closedBall_div`: densities under
  bi-Lipschitz maps.
* `Isometry.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`: Lebesgue's density theorem
  for subsets of an isometric copy of `k`-dimensional Euclidean space.
* `Isometry.ae_limsup_le_and_le_liminf_euclideanHausdorffMeasure_inter_closedBall_div`: density
  bounds almost everywhere on a bi-Lipschitz image of a subset of a `k`-plane.
* `TauCeti.limsup_measure_inter_div_le_of_tendsto_diff`: a part of a set with density zero does not
  contribute to the upper density.
* `MeasureTheory.Measure.posTangentConeAt_eq_univ_of_tendsto_inter_closedBall_div`,
  `MeasureTheory.Measure.uniqueDiffWithinAt_of_tendsto_inter_closedBall_div`: Haar density-one
  points have full tangent cones and unique relative derivatives.
* `HasFDerivWithinAt.liminf_euclideanHausdorffMeasure_directional_closedBall_pos`,
  `HasFDerivWithinAt.range_le_of_tendsto_euclideanHausdorffMeasure_outside_cone_div`: directional
  lower Hausdorff density and cone containment of the derivative range at parameter density-one
  points.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §§11–12.
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Chapters 15–16.
-/

public section

open Filter Function Metric MeasureTheory Measure Set Module
open scoped ENNReal NNReal Pointwise Topology

namespace TauCeti

/-- Scaling the radius of a closed ball in `EuclideanSpace ℝ (Fin k)` by `c ≥ 0` scales its volume
by `c ^ k`. -/
private lemma volume_closedBall_mul (k : ℕ) {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) :
    volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) (c * r)) =
      ENNReal.ofReal c ^ k * volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) := by
  rw [addHaar_closedBall_mul volume 0 hc hr, finrank_euclideanSpace_fin, ENNReal.ofReal_pow hc]

/-- Rescaling the radius in a `k`-dimensional density quotient. -/
private lemma div_volume_closedBall_eq_mul (k : ℕ) (m : ℝ≥0∞) {c : ℝ≥0} (hc : 0 < c) {r : ℝ}
    (hr : 0 ≤ r) :
    m / volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) =
      (c : ℝ≥0∞) ^ k * (m / volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) (c * r))) := by
  rw [volume_closedBall_mul k c.coe_nonneg hr, ENNReal.ofReal_coe_nnreal, ← mul_div_assoc,
    ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ (ENNReal.coe_ne_zero.2 hc.ne'))
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)]

/-- Discarding a part of `E` whose density quotients tend to zero does not lower the upper
density: if `μ (E \ S ∩ t r) / d r → 0`, then the limsup of `μ (E ∩ t r) / d r` is at most that of
`μ (E ∩ S ∩ t r) / d r`. -/
theorem limsup_measure_inter_div_le_of_tendsto_diff {α X : Type*} [MeasurableSpace X]
    {μ : Measure X} {E S : Set X} {t : α → Set X} {d : α → ℝ≥0∞} {l : Filter α}
    (h : Tendsto (fun r => μ (E \ S ∩ t r) / d r) l (𝓝 0)) :
    limsup (fun r => μ (E ∩ t r) / d r) l ≤ limsup (fun r => μ (E ∩ S ∩ t r) / d r) l :=
  calc limsup (fun r => μ (E ∩ t r) / d r) l
      ≤ limsup (fun r => μ (E ∩ S ∩ t r) / d r + μ (E \ S ∩ t r) / d r) l := by
        refine limsup_le_limsup (Eventually.of_forall fun r => ?_)
        rw [← ENNReal.add_div]
        gcongr
        refine (measure_mono fun z hz => ?_).trans (measure_union_le _ _)
        by_cases hzS : z ∈ S
        exacts [Or.inl ⟨⟨hz.1, hzS⟩, hz.2⟩, Or.inr ⟨⟨hz.1, hzS⟩, hz.2⟩]
    _ = _ := ENNReal.limsup_add_of_right_tendsto_zero h _

end TauCeti

namespace LipschitzOnWith

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {ψ : X → Y} {G : Set X} {a b : ℝ≥0} {k : ℕ} {x : X}

/-- **Upper density under a bi-Lipschitz map.** Let `ψ` be `b`-Lipschitz on `G` with
`a`-Lipschitz inverse. If `G` has `k`-dimensional density one at `x ∈ G`, then the upper
`k`-dimensional density of `ψ '' G` at `ψ x` is at most `(a b) ^ k`. -/
theorem limsup_euclideanHausdorffMeasure_image_inter_closedBall_div_le
    (hψ : LipschitzOnWith b ψ G) (hψ' : AntilipschitzWith a (G.domRestrict ψ)) (ha : 0 < a)
    (hx : x ∈ G)
    (hG : Tendsto (fun r => μHE[k] (G ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1)) :
    limsup (fun r => μHE[k] (ψ '' G ∩ closedBall (ψ x) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) ≤
        ((a * b : ℝ≥0) : ℝ≥0∞) ^ k := by
  have hlim : Tendsto (fun r => ((a * b : ℝ≥0) : ℝ≥0∞) ^ k *
      (μHE[k] (G ∩ closedBall x (a * r)) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) (a * r)))) (𝓝[>] 0)
      (𝓝 (((a * b : ℝ≥0) : ℝ≥0∞) ^ k)) := by
    have := ENNReal.Tendsto.const_mul
      (hG.comp (tendsto_iff_comap.2 (comap_mulLeft_nhdsGT_zero (NNReal.coe_pos.2 ha)).ge))
      (Or.inr (ENNReal.pow_ne_top (ENNReal.coe_ne_top (r := a * b)) (n := k)))
    rwa [mul_one] at this
  rw [← hlim.limsup_eq]
  refine limsup_le_limsup (eventually_mem_nhdsWithin.mono fun r (hr : 0 < r) => ?_)
  -- A point of `ψ '' G` within `r` of `ψ x` is the image of a point of `G` within `a r` of `x`.
  have hsub : ψ '' G ∩ closedBall (ψ x) r ⊆ ψ '' (G ∩ closedBall x (a * r)) := by
    rintro _ ⟨⟨x', hx', rfl⟩, hd⟩
    refine ⟨x', ⟨hx', ?_⟩, rfl⟩
    have h := hψ'.le_mul_dist ⟨x', hx'⟩ ⟨x, hx⟩
    rw [Subtype.dist_eq] at h
    rw [mem_closedBall] at hd ⊢
    exact h.trans (by gcongr; exact hd)
  calc μHE[k] (ψ '' G ∩ closedBall (ψ x) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)
      ≤ (b : ℝ≥0∞) ^ k * μHE[k] (G ∩ closedBall x (a * r)) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) := by
        gcongr
        exact (measure_mono hsub).trans
          ((hψ.mono inter_subset_left).euclideanHausdorffMeasure_image_le k)
    _ = _ := by
        rw [mul_div_assoc, TauCeti.div_volume_closedBall_eq_mul k _ ha hr.le]
        push_cast
        ring

/-- **Lower density under a bi-Lipschitz map.** Let `ψ` be `b`-Lipschitz on `G` with
`a`-Lipschitz inverse. If `G` has `k`-dimensional density one at `x ∈ G`, then the lower
`k`-dimensional density of `ψ '' G` at `ψ x` is at least `(a b) ^ (-k)`. -/
theorem le_liminf_euclideanHausdorffMeasure_image_inter_closedBall_div
    (hψ : LipschitzOnWith b ψ G) (hψ' : AntilipschitzWith a (G.domRestrict ψ)) (ha : 0 < a)
    (hb : 0 < b) (hx : x ∈ G)
    (hG : Tendsto (fun r => μHE[k] (G ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1)) :
    (((a * b : ℝ≥0) : ℝ≥0∞) ^ k)⁻¹ ≤ liminf (fun r => μHE[k] (ψ '' G ∩ closedBall (ψ x) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) := by
  have hab : ((a * b : ℝ≥0) : ℝ≥0∞) ^ k ≠ ∞ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  rw [ENNReal.inv_le_iff_le_mul (fun _ => pow_ne_zero _ (ENNReal.coe_ne_zero.2 (mul_pos ha hb).ne'))
      (fun h => absurd h hab),
    ← ENNReal.liminf_const_mul_of_ne_top hab]
  -- The inverse of `ψ` on `ψ '' G` is `a`-Lipschitz.
  classical
  have : Nonempty X := ⟨x⟩
  have hinj : InjOn ψ G := injOn_iff_injective.2 hψ'.injective
  have hφ : LipschitzOnWith a (invFunOn ψ G) (ψ '' G) :=
    lipschitzOnWith_iff_restrict.2 (hψ'.to_rightInvOn' (fun _ hy => invFunOn_mem hy)
      fun _ hy => invFunOn_eq hy)
  have hlim := hG.comp (tendsto_iff_comap.2
    (comap_mulLeft_nhdsGT_zero (NNReal.coe_pos.2 (inv_pos.2 hb))).ge)
  rw [← hlim.liminf_eq]
  refine liminf_le_liminf (eventually_mem_nhdsWithin.mono fun r (hr : 0 < r) => ?_)
  -- Points of `G` within `r / b` of `x` are mapped within `r` of `ψ x`.
  have hr' : (b : ℝ) * ((b⁻¹ : ℝ≥0) * r) = r := by
    rw [NNReal.coe_inv, mul_inv_cancel_left₀ (NNReal.coe_pos.2 hb).ne']
  set S := G ∩ closedBall x ((b⁻¹ : ℝ≥0) * r)
  have hS : ψ '' S ⊆ ψ '' G ∩ closedBall (ψ x) r := by
    rintro _ ⟨x', ⟨hx', hd⟩, rfl⟩
    refine ⟨mem_image_of_mem _ hx', ?_⟩
    rw [mem_closedBall] at hd ⊢
    calc dist (ψ x') (ψ x) ≤ b * dist x' x := hψ.dist_le_mul x' hx' x hx
      _ ≤ b * ((b⁻¹ : ℝ≥0) * r) := by gcongr
      _ = r := hr'
  have hmeas : μHE[k] S ≤ (a : ℝ≥0∞) ^ k * μHE[k] (ψ '' G ∩ closedBall (ψ x) r) :=
    calc μHE[k] S = μHE[k] (invFunOn ψ G '' (ψ '' S)) := by
          rw [hinj.leftInvOn_invFunOn.image_image' inter_subset_left]
      _ ≤ (a : ℝ≥0∞) ^ k * μHE[k] (ψ '' S) :=
          (hφ.mono (image_mono inter_subset_left)).euclideanHausdorffMeasure_image_le k
      _ ≤ _ := by gcongr
  dsimp only [comp_apply]
  rw [TauCeti.div_volume_closedBall_eq_mul k _ hb (by positivity), hr']
  calc _ ≤ (b : ℝ≥0∞) ^ k * ((a : ℝ≥0∞) ^ k * μHE[k] (ψ '' G ∩ closedBall (ψ x) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) := by gcongr
    _ = _ := by
        rw [mul_div_assoc]
        push_cast
        ring

end LipschitzOnWith

namespace Isometry

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}

/-- **Lebesgue's density theorem in a `k`-plane.** Let `ι` be an isometry from `k`-dimensional
Euclidean space into `X`. Every subset `S` of its range has `k`-dimensional density one at
`μHE[k]`-almost every point of `S`. No measurability of `S` is needed. -/
theorem ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div
    {ι : EuclideanSpace ℝ (Fin k) → X} (hι : Isometry ι) {S : Set X} (hS : S ⊆ range ι) :
    ∀ᵐ x ∂μHE[k], x ∈ S → Tendsto (fun r => μHE[k] (S ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) := by
  set T := ι ⁻¹' S
  -- Balls about points of the range of `ι` meet `S` in isometric images of balls meeting `T`.
  have key (z : EuclideanSpace ℝ (Fin k)) (r : ℝ) :
      μHE[k] (S ∩ closedBall (ι z) r) = volume (T ∩ closedBall z r) := by
    have : S ∩ closedBall (ι z) r = ι '' (T ∩ closedBall z r) := by
      ext y
      constructor
      · rintro ⟨hy, hyr⟩
        obtain ⟨w, rfl⟩ := hS hy
        exact ⟨w, ⟨hy, by rwa [mem_closedBall, ← hι.dist_eq]⟩, rfl⟩
      · rintro ⟨w, ⟨hw, hwr⟩, rfl⟩
        exact ⟨hw, by rwa [mem_closedBall, hι.dist_eq]⟩
    rw [this, hι.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  have hT := ae_iff.1 (Besicovitch.ae_tendsto_measure_inter_div volume T)
  have hN := nonpos_iff_eq_zero.1 ((le_restrict_apply T _).trans_eq hT)
  rw [ae_iff]
  have himg (N : Set (EuclideanSpace ℝ (Fin k))) (h : volume N = 0) : μHE[k] (ι '' N) = 0 := by
    rwa [hι.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  refine measure_mono_null ?_ (himg _ hN)
  intro y hy
  replace hy := not_imp.1 hy
  obtain ⟨z, rfl⟩ := hS hy.1
  refine ⟨z, ⟨fun h => hy.2 (h.congr fun r => ?_), hy.1⟩, rfl⟩
  rw [key, addHaar_closedBall_center volume z r]

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **Densities of a bi-Lipschitz image of a subset of a `k`-plane.** Let `ι` be an isometry from
`k`-dimensional Euclidean space into `X`, and let `ψ` be `b`-Lipschitz on a subset `G` of its range
with `a`-Lipschitz inverse. Then every subset `T` of `ψ '' G` has upper density at most `(a b) ^ k`
and lower density at least `(a b) ^ (-k)` at `μHE[k]`-almost every point of `T`. -/
theorem ae_limsup_le_and_le_liminf_euclideanHausdorffMeasure_inter_closedBall_div
    {ι : EuclideanSpace ℝ (Fin k) → X} (hι : Isometry ι) {G : Set X} (hGι : G ⊆ range ι)
    {ψ : X → Y} {a b : ℝ≥0} (hψ : LipschitzOnWith b ψ G)
    (hψ' : AntilipschitzWith a (G.domRestrict ψ)) (ha : 0 < a) (hb : 0 < b) {T : Set Y}
    (hT : T ⊆ ψ '' G) :
    ∀ᵐ y ∂μHE[k], y ∈ T →
      limsup (fun r => μHE[k] (T ∩ closedBall y r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) ≤
          ((a * b : ℝ≥0) : ℝ≥0∞) ^ k ∧
      (((a * b : ℝ≥0) : ℝ≥0∞) ^ k)⁻¹ ≤ liminf (fun r => μHE[k] (T ∩ closedBall y r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) := by
  -- `T` is the image of the part `G'` of `G` that `ψ` maps into `T`.
  obtain ⟨G', hG'G, rfl⟩ : ∃ G' ⊆ G, ψ '' G' = T := by
    refine ⟨G ∩ ψ ⁻¹' T, inter_subset_left, Subset.antisymm ?_ fun y hy => ?_⟩
    · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
      exact hx
    · obtain ⟨x, hx, rfl⟩ := hT hy
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  have hψ₁ := hψ.mono hG'G
  have hψ₁' : AntilipschitzWith a (G'.domRestrict ψ) :=
    AntilipschitzWith.of_le_mul_dist fun x y => by
      simpa only [Subtype.dist_eq, domRestrict_apply] using
        hψ'.le_mul_dist ⟨x, hG'G x.2⟩ ⟨y, hG'G y.2⟩
  have hdens := ae_iff.1 (hι.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div
    (hG'G.trans hGι))
  -- The image of the points of `G'` where `G'` does not have density one is null.
  have himg (N : Set X) (hN : N ⊆ G') (h0 : μHE[k] N = 0) : μHE[k] (ψ '' N) = 0 :=
    nonpos_iff_eq_zero.1 (((hψ₁.mono hN).euclideanHausdorffMeasure_image_le k).trans_eq
      (by rw [h0, mul_zero]))
  rw [ae_iff]
  refine measure_mono_null ?_
    (himg _ inter_subset_right (measure_mono_null inter_subset_left hdens))
  intro y hy
  obtain ⟨⟨x, hx, rfl⟩, hy⟩ := not_imp.1 hy
  exact ⟨x, ⟨fun h => hy ⟨hψ₁.limsup_euclideanHausdorffMeasure_image_inter_closedBall_div_le
    hψ₁' ha hx (h hx), hψ₁.le_liminf_euclideanHausdorffMeasure_image_inter_closedBall_div
      hψ₁' ha hb hx (h hx)⟩, hx⟩, rfl⟩

end Isometry

namespace MeasureTheory.Measure

/-- A point at which a set `s` has density one with respect to a measure `μ` belongs to the closure
of `s`, with no measurability or Haar assumption on `s` or `μ`. -/
theorem mem_closure_of_tendsto_inter_closedBall_div {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] (μ : Measure X) {s : Set X} {x : X}
    (hs : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) :
    x ∈ closure s := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < μ (s ∩ closedBall x r) / μ (closedBall x r) :=
    (tendsto_order.1 hs).1 0 zero_lt_one
  obtain ⟨r, hr, _, hrε⟩ :=
    (hpos.and (Ioo_mem_nhdsGT hε)).exists
  have hne : (s ∩ closedBall x r).Nonempty :=
    nonempty_of_measure_ne_zero (μ := μ) fun h0 => by simp [h0] at hr
  obtain ⟨y, hys, hyr⟩ := hne
  exact ⟨y, hys, (dist_comm x y).trans_lt ((mem_closedBall.1 hyr).trans_lt hrε)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- At a Haar density-one point of an arbitrary set `s`, every vector belongs to the positive
tangent cone `posTangentConeAt s x`. No measurability of `s` is required. -/
theorem posTangentConeAt_eq_univ_of_tendsto_inter_closedBall_div (μ : Measure E)
    [μ.IsAddHaarMeasure] {s : Set E} {x : E}
    (hs : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) :
    posTangentConeAt s x = univ := by
  ext v
  simp only [mem_univ, iff_true]
  have hex (n : ℕ) : ∃ r : ℝ, 0 < r ∧ r < ((n : ℝ) + 1)⁻¹ ∧
      ∃ a ∈ closedBall v ((n : ℝ) + 1)⁻¹, x + r • a ∈ s := by
    have hε : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
    have hne := eventually_nonempty_inter_smul_of_density_one μ s x hs
      (closedBall v ((n : ℝ) + 1)⁻¹) measurableSet_closedBall
      (measure_closedBall_pos μ v hε).ne'
    obtain ⟨r, ⟨y, hys, hy⟩, hr0, hrε⟩ := (hne.and (Ioo_mem_nhdsGT hε)).exists
    obtain ⟨x', hx', _, ⟨a, ha, rfl⟩, rfl⟩ := hy
    rw [mem_singleton_iff.1 hx'] at hys
    exact ⟨r, hr0, hrε, a, ha, hys⟩
  choose r hr0 hrε a ha hxs using hex
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ha_lim : Tendsto a atTop (𝓝 v) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun n => mem_closedBall_iff_norm.1 (ha n)) hinv
  have hr_lim : Tendsto r atTop (𝓝 0) :=
    squeeze_zero (fun n => (hr0 n).le) (fun n => (hrε n).le) hinv
  refine mem_tangentConeAt_of_seq atTop (fun n => (⟨(r n)⁻¹, inv_nonneg.2 (hr0 n).le⟩ : ℝ≥0))
    (fun n => r n • a n) ?_ (Eventually.of_forall hxs) ?_
  · simpa only [zero_smul] using hr_lim.smul ha_lim
  · refine ha_lim.congr fun n => ?_
    change a n = (r n)⁻¹ • (r n • a n)
    rw [inv_smul_smul₀ (hr0 n).ne']

/-- At a Haar density-one point of an arbitrary set `s`, the tangent cone `tangentConeAt ℝ s x`
is the whole space. -/
theorem tangentConeAt_eq_univ_of_tendsto_inter_closedBall_div (μ : Measure E) [μ.IsAddHaarMeasure]
    {s : Set E} {x : E}
    (hs : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) :
    tangentConeAt ℝ s x = univ :=
  eq_univ_of_subset (fun _ hv => tangentConeAt_mono_field hv)
    (μ.posTangentConeAt_eq_univ_of_tendsto_inter_closedBall_div hs)

/-- At a Haar density-one point of an arbitrary set `s`, relative derivatives within `s` are
unique. -/
theorem uniqueDiffWithinAt_of_tendsto_inter_closedBall_div (μ : Measure E) [μ.IsAddHaarMeasure]
    {s : Set E} {x : E}
    (hs : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) :
    UniqueDiffWithinAt ℝ s x := by
  refine ⟨?_, μ.mem_closure_of_tendsto_inter_closedBall_div hs⟩
  rw [μ.tangentConeAt_eq_univ_of_tendsto_inter_closedBall_div hs, Submodule.span_univ,
    Submodule.top_coe]
  exact dense_univ

end MeasureTheory.Measure

namespace HasFDerivWithinAt

section Haar

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {f : U → V} {s : Set U} {x₀ : U} {A : U →L[ℝ] V} {L : ℝ≥0}

/-- At a Haar density-one point of the parameter set, an inverse-Lipschitz parametrization has an
antilipschitz derivative with the same constant. -/
theorem antilipschitzWith_of_tendsto_inter_closedBall_div (μ : Measure U) [μ.IsAddHaarMeasure]
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => μ (s ∩ closedBall x₀ r) / μ (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1)) :
    AntilipschitzWith L A :=
  hf.antilipschitzWith_of_tangentConeAt_eq_univ hx₀ hi
    (μ.tangentConeAt_eq_univ_of_tendsto_inter_closedBall_div hs)

/-- At a Haar density-one point of the parameter set, an inverse-Lipschitz parametrization has an
injective derivative. -/
theorem injective_of_tendsto_inter_closedBall_div (μ : Measure U) [μ.IsAddHaarMeasure]
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => μ (s ∩ closedBall x₀ r) / μ (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1)) :
    Injective A :=
  (hf.antilipschitzWith_of_tendsto_inter_closedBall_div μ hx₀ hi hs).injective

end Haar

section DirectionalDensity

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {f : U → V} {s : Set U} {E : Set V} {x₀ : U} {A : U →L[ℝ] V} {L : ℝ≥0}

/-- Volume of a translated rescaled closed ball `{x₀} + r • closedBall u c` in a finite-dimensional
real inner product space equals the volume of a closed ball of radius `c * r` in
`EuclideanSpace ℝ (Fin (finrank ℝ U))`. -/
private lemma volume_singleton_add_smul_closedBall (x₀ u : U) (c : ℝ) {r : ℝ} (hr : 0 < r) :
    volume ({x₀} + r • closedBall u c) =
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) (c * r)) := by
  have hset : ({x₀} : Set U) + r • closedBall u c = closedBall (x₀ + r • u) (c * r) := by
    ext y
    constructor
    · rintro ⟨x', hx', _, ⟨w, hw, rfl⟩, rfl⟩
      rw [mem_singleton_iff.1 hx']
      rw [mem_closedBall_iff_norm] at hw ⊢
      have hsub : x₀ + r • w - (x₀ + r • u) = r • (w - u) := by
        rw [smul_sub]
        abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith
    · intro hy
      refine ⟨x₀, rfl, r • (r⁻¹ • (y - x₀)), ⟨r⁻¹ • (y - x₀), ?_, rfl⟩, ?_⟩
      · rw [mem_closedBall_iff_norm] at hy ⊢
        have hsub : r⁻¹ • (y - x₀) - u = r⁻¹ • (y - (x₀ + r • u)) := by
          simp only [smul_sub, inv_smul_smul₀ hr.ne', sub_add_eq_sub_sub]
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_le_iff₀ hr]
        linarith
      · dsimp only
        rw [smul_inv_smul₀ hr.ne', add_sub_cancel]
  let e : EuclideanSpace ℝ (Fin (finrank ℝ U)) ≃ₗᵢ[ℝ] U := (stdOrthonormalBasis ℝ U).repr.symm
  have himg : e '' closedBall 0 (c * r) = closedBall (0 : U) (c * r) := by
    simpa only [LinearIsometryEquiv.coe_toIsometryEquiv, map_zero] using
      e.toIsometryEquiv.image_closedBall 0 (c * r)
  rw [hset, addHaar_closedBall_center volume (x₀ + r • u) (c * r),
    ← InnerProductSpace.euclideanHausdorffMeasure_eq_volume, ← himg,
    e.isometry.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]

/-- **Directional lower Hausdorff density of an inverse-Lipschitz differentiable image.** Let `f`
be differentiable within `s` at `x₀` with derivative `A`, and `L`-antilipschitz on `s`, where `s`
has Lebesgue density one at `x₀` and `f '' s ⊆ E`. Then along every direction `A u` with
`‖A u‖ < 1` and every angular radius `η > 0`, the portion of `E ∩ closedBall (f x₀) r` within
`r * η` of `f x₀ + r • A u` has strictly positive lower `(finrank ℝ U)`-dimensional Hausdorff
density. Neither `s` nor `E` need be measurable, `x₀` need not belong to `s`, and `f` need not be
globally Lipschitz. -/
theorem liminf_euclideanHausdorffMeasure_directional_closedBall_pos
    (hf : HasFDerivWithinAt f A s x₀) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E) {u : U} (hu : ‖A u‖ < 1) {η : ℝ} (hη : 0 < η) :
    0 < liminf (fun r =>
      μHE[finrank ℝ U] {z ∈ E ∩ closedBall (f x₀) r | ‖z - f x₀ - r • A u‖ ≤ r * η} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) := by
  classical
  set k := finrank ℝ U
  set L' : ℝ≥0 := L + 1
  have hi' : AntilipschitzWith L' (s.domRestrict f) := fun x y =>
    (hi x y).trans (by gcongr; exact le_add_of_nonneg_right zero_le_one)
  set η₀ : ℝ := min η (1 - ‖A u‖)
  have hη₀ : 0 < η₀ := lt_min hη (sub_pos.2 hu)
  set c : ℝ := η₀ / (2 * (‖A‖ + 1))
  have hc : 0 < c := by positivity
  set c' : ℝ≥0 := ⟨c, hc.le⟩
  have hc' : 0 < c' := hc
  set R₀ : ℝ := ‖u‖ + c + 1
  have hR₀ : 0 < R₀ := by positivity
  obtain ⟨δ, hδ, hδb⟩ := eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp (hf.isLittleO.bound (div_pos hη₀ (mul_pos two_pos hR₀))))
  -- Points of `s` in `{x₀} + r • closedBall u c` map into the directional ball in `E`.
  set B := closedBall u c
  set M : ℝ → Set V := fun r => {z ∈ E ∩ closedBall (f x₀) r | ‖z - f x₀ - r • A u‖ ≤ r * η}
  have hsub : ∀ r ∈ Ioo 0 (δ / R₀), f '' (s ∩ ({x₀} + r • B)) ⊆ M r := by
    rintro r ⟨hr0, hrδ⟩ _ ⟨x, ⟨hxs, x', hx', _, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    dsimp only at hxs ⊢
    rw [mem_singleton_iff.1 hx'] at hxs ⊢
    have hwu : ‖w - u‖ ≤ c := mem_closedBall_iff_norm.1 hw
    have hwR : ‖w‖ ≤ ‖u‖ + c := by
      calc ‖w‖ = ‖u + (w - u)‖ := by abel_nf
        _ ≤ ‖u‖ + ‖w - u‖ := norm_add_le _ _
        _ ≤ ‖u‖ + c := by linarith
    have hxδ : x₀ + r • w ∈ ball x₀ δ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr0]
      calc r * ‖w‖ ≤ r * R₀ := mul_le_mul_of_nonneg_left (by dsimp [R₀]; linarith) hr0.le
        _ < δ := (lt_div_iff₀ hR₀).1 hrδ
    have herr : ‖f (x₀ + r • w) - f x₀ - r • A u‖ ≤ r * η₀ := by
      have h1 := hδb (x₀ + r • w) hxδ hxs
      rw [add_sub_cancel_left] at h1
      have h2 : ‖A (r • w) - r • A u‖ ≤ r * (η₀ / 2) := by
        rw [← map_smul, ← map_sub, ← smul_sub, map_smul, norm_smul, Real.norm_eq_abs,
          abs_of_pos hr0]
        gcongr
        calc ‖A (w - u)‖ ≤ ‖A‖ * ‖w - u‖ := A.le_opNorm _
          _ ≤ ‖A‖ * c := by gcongr
          _ ≤ (‖A‖ + 1) * c := by nlinarith [hc]
          _ = η₀ / 2 := by dsimp [c]; field_simp
      have h1' : ‖f (x₀ + r • w) - f x₀ - A (r • w)‖ ≤ r * (η₀ / 2) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0] at h1
        refine h1.trans ?_
        have : ‖w‖ ≤ R₀ := by dsimp [R₀]; linarith
        calc η₀ / (2 * R₀) * (r * ‖w‖) ≤ η₀ / (2 * R₀) * (r * R₀) := by gcongr
          _ = r * (η₀ / 2) := by field_simp
      calc ‖f (x₀ + r • w) - f x₀ - r • A u‖
          = ‖(f (x₀ + r • w) - f x₀ - A (r • w)) + (A (r • w) - r • A u)‖ := by congr 1; abel
        _ ≤ ‖f (x₀ + r • w) - f x₀ - A (r • w)‖ + ‖A (r • w) - r • A u‖ := norm_add_le _ _
        _ ≤ r * (η₀ / 2) + r * (η₀ / 2) := add_le_add h1' h2
        _ = r * η₀ := by ring
    refine ⟨⟨hfs (mem_image_of_mem f hxs), ?_⟩,
      herr.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hr0.le)⟩
    rw [mem_closedBall, dist_eq_norm]
    calc ‖f (x₀ + r • w) - f x₀‖
        = ‖r • A u + (f (x₀ + r • w) - f x₀ - r • A u)‖ := by congr 1; abel
      _ ≤ ‖r • A u‖ + ‖f (x₀ + r • w) - f x₀ - r • A u‖ := norm_add_le _ _
      _ ≤ r * ‖A u‖ + r * η₀ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
          linarith
      _ ≤ r * 1 := by nlinarith [min_le_right η (1 - ‖A u‖)]
      _ = r := mul_one r
  -- Compare Hausdorff measure in the target with Lebesgue density in the parameter space.
  have : Nonempty U := ⟨x₀⟩
  have hinj : InjOn f s := injOn_iff_injective.2 hi'.injective
  have hφ : LipschitzOnWith L' (invFunOn f s) (f '' s) :=
    lipschitzOnWith_iff_restrict.2 (hi'.to_rightInvOn' (fun _ hy => invFunOn_mem hy)
      fun _ hy => invFunOn_eq hy)
  have hdens := tendsto_addHaar_inter_smul_one_of_density_one volume s x₀ hs B
    measurableSet_closedBall (measure_closedBall_pos volume u hc).ne' measure_closedBall_lt_top.ne
  have hlim : Tendsto (fun r : ℝ => (c' : ℝ≥0∞) ^ k *
      (volume (s ∩ ({x₀} + r • B)) / volume ({x₀} + r • B))) (𝓝[>] 0) (𝓝 ((c' : ℝ≥0∞) ^ k)) := by
    simpa only [mul_one] using ENNReal.Tendsto.const_mul hdens
      (Or.inr (ENNReal.pow_ne_top ENNReal.coe_ne_top))
  have hLtop : (L' : ℝ≥0∞) ^ k ≠ ∞ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hineq : (c' : ℝ≥0∞) ^ k ≤ (L' : ℝ≥0∞) ^ k *
      liminf (fun r => μHE[k] (M r) / volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r))
        (𝓝[>] 0) := by
    rw [← ENNReal.liminf_const_mul_of_ne_top hLtop, ← hlim.liminf_eq]
    refine liminf_le_liminf ?_
    filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR₀)] with r hr
    have hvol : volume (s ∩ ({x₀} + r • B)) ≤ (L' : ℝ≥0∞) ^ k * μHE[k] (M r) :=
      calc volume (s ∩ ({x₀} + r • B))
          = μHE[k] (s ∩ ({x₀} + r • B)) :=
              (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := U)).symm ▸ rfl
        _ = μHE[k] (invFunOn f s '' (f '' (s ∩ ({x₀} + r • B)))) := by
              rw [hinj.leftInvOn_invFunOn.image_image' inter_subset_left]
        _ ≤ (L' : ℝ≥0∞) ^ k * μHE[k] (f '' (s ∩ ({x₀} + r • B))) :=
              (hφ.mono (image_mono inter_subset_left)).euclideanHausdorffMeasure_image_le k
        _ ≤ (L' : ℝ≥0∞) ^ k * μHE[k] (M r) := by gcongr; exact hsub r hr
    rw [volume_singleton_add_smul_closedBall x₀ u c hr.1, show c * r = (c' : ℝ) * r from rfl,
      ← TauCeti.div_volume_closedBall_eq_mul k _ hc' hr.1.le, ← mul_div_assoc]
    gcongr
  have hc0 : (0 : ℝ≥0∞) < (c' : ℝ≥0∞) ^ k :=
    ENNReal.pow_pos (ENNReal.coe_pos.2 hc') k
  refine pos_iff_ne_zero.2 fun h0 => hc0.ne' ?_
  rw [h0, mul_zero, nonpos_iff_eq_zero] at hineq
  exact hineq

/-- At a Lebesgue density-one point of the parameter set, the image of an inverse-Lipschitz
differentiable parametrization has strictly positive upper Hausdorff density. -/
theorem limsup_euclideanHausdorffMeasure_inter_closedBall_div_pos
    (hf : HasFDerivWithinAt f A s x₀) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E) :
    0 < limsup (fun r => μHE[finrank ℝ U] (E ∩ closedBall (f x₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) := by
  have hpos := hf.liminf_euclideanHausdorffMeasure_directional_closedBall_pos hi hs hfs
    (u := 0) (by simp) zero_lt_one
  refine hpos.trans_le ((liminf_le_limsup).trans (limsup_le_limsup ?_))
  refine Eventually.of_forall fun r => ?_
  gcongr
  exact sep_subset _ _

/-- **Derivative range lies in every density-zero cone.** If `E` contains `f '' s`, `s` has
Lebesgue density one at `x₀`, `f` is differentiable within `s` at `x₀` with derivative `A` and
`L`-antilipschitz on `s`, and `E` has `(finrank ℝ U)`-dimensional Hausdorff density zero outside
every cone around a closed subspace `P`, then `range A ≤ P`. -/
theorem range_le_of_tendsto_euclideanHausdorffMeasure_outside_cone_div
    (hf : HasFDerivWithinAt f A s x₀) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E) {P : Submodule ℝ V} (hP : IsClosed (P : Set V))
    (hcone : ∀ ε > (0 : ℝ), Tendsto (fun r =>
      μHE[finrank ℝ U] {z ∈ E ∩ closedBall (f x₀) r | ε * dist z (f x₀) <
        infDist (z - f x₀) (P : Set V)} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0)) :
    LinearMap.range A.toLinearMap ≤ P := by
  rintro _ ⟨u₀, rfl⟩
  by_contra hu₀P
  have hAu₀ : A u₀ ≠ 0 := fun h0 => hu₀P (h0 ▸ P.zero_mem)
  have : 0 < ‖A u₀‖ := norm_pos_iff.2 hAu₀
  set u := (2 * ‖A u₀‖)⁻¹ • u₀
  have hAu_norm : ‖A u‖ < 1 := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : (2 * ‖A u₀‖)⁻¹ * ‖A u₀‖ = 1 / 2 := by field_simp
    linarith
  have hAuP : A u ∉ (P : Set V) := by
    intro hmem
    refine hu₀P ?_
    have : (2 * ‖A u₀‖) • A u = A u₀ := by
      rw [map_smul, smul_inv_smul₀ (by positivity)]
    exact this ▸ P.smul_mem (2 * ‖A u₀‖) hmem
  set d := infDist (A u) (P : Set V)
  have hd : 0 < d := (hP.notMem_iff_infDist_pos ⟨0, P.zero_mem⟩).1 hAuP
  have hlow := hf.liminf_euclideanHausdorffMeasure_directional_closedBall_pos hi hs hfs
    hAu_norm (show 0 < d / 3 by positivity)
  have hzero := (hcone (d / 3) (by positivity)).liminf_eq
  refine hlow.ne' (le_antisymm ?_ zero_le)
  rw [← hzero]
  refine liminf_le_liminf ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hinc : {z ∈ E ∩ closedBall (f x₀) r | ‖z - f x₀ - r • A u‖ ≤ r * (d / 3)} ⊆
      {z ∈ E ∩ closedBall (f x₀) r | d / 3 * dist z (f x₀) < infDist (z - f x₀) (P : Set V)} := by
    rintro z ⟨hzE, hzd⟩
    refine ⟨hzE, ?_⟩
    have hrd : r * d ≤ infDist (r • A u) (P : Set V) := by
      rw [le_infDist ⟨0, P.zero_mem⟩]
      intro p hp
      have hp' : r⁻¹ • p ∈ (P : Set V) := P.smul_mem r⁻¹ hp
      have h1 : d ≤ dist (A u) (r⁻¹ • p) := infDist_le_dist_of_mem hp'
      have h2 : dist (r • A u) p = r * dist (A u) (r⁻¹ • p) := by
        rw [dist_eq_norm, dist_eq_norm, ← smul_inv_smul₀ hr.ne' p, ← smul_sub,
          inv_smul_smul₀ hr.ne', norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith
    have htri : infDist (r • A u) (P : Set V) ≤
        infDist (z - f x₀) (P : Set V) + dist (r • A u) (z - f x₀) :=
      infDist_le_infDist_add_dist
    have hdist_u : dist (r • A u) (z - f x₀) ≤ r * (d / 3) := by
      rwa [dist_comm, dist_eq_norm]
    have hzr : dist z (f x₀) ≤ r := mem_closedBall.1 hzE.2
    nlinarith
  gcongr

end DirectionalDensity

end HasFDerivWithinAt
