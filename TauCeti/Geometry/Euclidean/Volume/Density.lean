/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Order.LiminfLimsup
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz

/-!
# Densities for the Euclidean Hausdorff measure under bi-Lipschitz maps and in `k`-planes

The `k`-dimensional density of a set `S` in a metric space at a point `x` compares
`μHE[k] (S ∩ closedBall x r)` with `ω_k r ^ k`, the volume of a ball of radius `r` in
`EuclideanSpace ℝ (Fin k)`. This file proves two general facts about these densities, neither of
which involves rectifiability:

* a map that is `b`-Lipschitz on `G` with `a`-Lipschitz inverse moves a point of density one of `G`
  to a point of `ψ '' G` whose upper and lower densities lie between `(a b) ^ (-k)` and
  `(a b) ^ k`;
* **Lebesgue's density theorem in a `k`-plane**: every subset of an isometric copy of
  `EuclideanSpace ℝ (Fin k)` has density one at almost every one of its points. This is
  transported from Mathlib's `Besicovitch.ae_tendsto_measure_inter_div`.

Together with the zero-density theorem
`TauCeti.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`, these are the ingredients of
the density theorem for rectifiable sets.

## Main results

* `LipschitzOnWith.limsup_euclideanHausdorffMeasure_image_inter_closedBall_div_le` and
  `LipschitzOnWith.le_liminf_euclideanHausdorffMeasure_image_inter_closedBall_div`: densities under
  bi-Lipschitz maps.
* `Isometry.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`: Lebesgue's density theorem
  for subsets of an isometric copy of `k`-dimensional Euclidean space.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11.
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Theorem 16.2.
-/

public section

open Filter Function Metric MeasureTheory Measure Set Module
open scoped ENNReal NNReal Topology

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
        rw [mul_div_assoc, TauCeti.div_volume_closedBall_eq_mul k _ ha hr.le, ← mul_assoc,
          ← mul_pow, ← ENNReal.coe_mul, mul_comm b a]

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
  rw [TauCeti.div_volume_closedBall_eq_mul k _ hb (by positivity), hr', ENNReal.coe_mul, mul_pow,
    mul_comm ((a : ℝ≥0∞) ^ k), mul_assoc]
  gcongr
  rw [← mul_div_assoc]
  gcongr

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

end Isometry
