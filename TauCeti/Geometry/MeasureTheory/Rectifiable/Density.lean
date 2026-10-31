/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Order.LiminfLimsup
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.Geometry.MeasureTheory.Rectifiable.Bilipschitz
import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz

/-!
# The density theorem for rectifiable sets

Let `E` be a countably `k`-rectifiable subset of a finite-dimensional real inner product space,
measurable for the normalized Euclidean Hausdorff measure `μHE[k]`, with locally finite `μHE[k]`
measure. The **density theorem** states that `E` has `k`-dimensional density one at
`μHE[k]`-almost every point of `E`:

`μHE[k] (E ∩ closedBall x r) / (ω_k r ^ k) → 1` as `r → 0⁺`,

where `ω_k r ^ k` is the volume of a ball of radius `r` in `EuclideanSpace ℝ (Fin k)`
(`TauCeti.CountablyRectifiable.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`).
Local finiteness cannot be dropped: in the plane, the union of the lines through pairs of points of
a countable dense set is countably `1`-rectifiable but has infinite `μHE[1]` measure in every ball.

The density theorem is the first step towards approximate tangent planes of rectifiable sets, and
the form in which the structure theorem for sets of finite perimeter identifies the perimeter
measure with Hausdorff measure on the reduced boundary.

## Main results

* `LipschitzOnWith.limsup_euclideanHausdorffMeasure_image_inter_closedBall_div_le` and
  `LipschitzOnWith.le_liminf_euclideanHausdorffMeasure_image_inter_closedBall_div`: a map that is
  `b`-Lipschitz on `G` with `a`-Lipschitz inverse moves a point of density one of `G` to a point
  of `ψ '' G` whose upper and lower densities lie between `(a b) ^ (-k)` and `(a b) ^ k`.
* `Isometry.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`: Lebesgue's density theorem
  for subsets of an isometric copy of `k`-dimensional Euclidean space, in the normalization of
  `μHE[k]`.
* `TauCeti.CountablyRectifiable.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`: the
  density theorem.

## The argument

Up to a null set, `E` is covered by images of Borel pieces on which a Lipschitz parametrization is
within a relative error `δ` of an injective linear map `A`
(`LipschitzWith.exists_linear_approximation_cover`). On each piece, the parametrization is
`(1 + δ)`-Lipschitz with `(1 - δ)⁻¹`-Lipschitz inverse when read from the image of the piece under
the approximating injective linear map `A`. This image lies in the `k`-plane `range A`, where
Lebesgue's density theorem gives density one almost everywhere. The distortion estimates then
bound the upper and lower densities of `E` by `((1 + δ) / (1 - δ)) ^ (±k)` almost everywhere on
each piece, since the part of `E` outside the piece has density zero at almost every point of the
piece (`TauCeti.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`). Letting `δ → 0`
gives density one.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (the density of rectifiable sets).
* H. Federer, *Geometric Measure Theory*, 3.2.18 and 3.2.19 (decomposition of Lipschitz maps into
  pieces close to linear maps, and densities of rectifiable sets).
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

/-- Multiplication by a positive constant preserves the filter of right neighbourhoods of `0`. -/
private lemma tendsto_const_mul_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r => c * r) (𝓝[>] 0) (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2
    ⟨((continuous_const.mul continuous_id).tendsto' 0 0 (mul_zero c)).mono_left nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin.mono fun _ hr => mul_pos hc hr⟩

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
      (hG.comp (TauCeti.tendsto_const_mul_nhdsGT_zero (NNReal.coe_pos.2 ha)))
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
  have hlim := hG.comp (TauCeti.tendsto_const_mul_nhdsGT_zero (NNReal.coe_pos.2 (inv_pos.2 hb)))
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

namespace TauCeti

section Pieces

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] {k : ℕ}

/-- Bounds on the densities of a subset `T` of the bi-Lipschitz image `ψ '' G` of a subset `G` of a
`k`-plane, at almost every point of `T`. -/
private theorem ae_limsup_le_and_le_liminf {ι : EuclideanSpace ℝ (Fin k) → X} (hι : Isometry ι)
    {G : Set X} (hGι : G ⊆ range ι) {ψ : X → Y} {a b : ℝ≥0} (hψ : LipschitzOnWith b ψ G)
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

end Pieces

section Approximation

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {f : U → V} {P : Set U} {A : U →L[ℝ] V} {ε : ℝ≥0}

/-- A map within relative error `ε` of `A` on `P` has `‖f x - f y‖ ≥ (1 - ε) ‖A x - A y‖` there. -/
private lemma mul_norm_sub_le_of_approx
    (happ : ∀ x ∈ P, ∀ y ∈ P, ‖f x - f y - A (x - y)‖ ≤ ε * ‖A (x - y)‖) {x y : U} (hx : x ∈ P)
    (hy : y ∈ P) : (1 - ε : ℝ) * ‖A x - A y‖ ≤ ‖f x - f y‖ := by
  have h := happ x hx y hy
  rw [map_sub] at h
  have := norm_sub_norm_le (A x - A y) (f x - f y)
  rw [norm_sub_rev (A x - A y)] at this
  linarith

/-- A map within relative error `ε < 1` of an injective linear map `A` on `P`, read through `A`,
is `(1 + ε)`-Lipschitz on `A '' P` with `(1 - ε)⁻¹`-Lipschitz inverse. -/
private lemma lipschitzOnWith_and_antilipschitzWith_of_approx (hA : Injective A) (hε : ε < 1)
    (happ : ∀ x ∈ P, ∀ y ∈ P, ‖f x - f y - A (x - y)‖ ≤ ε * ‖A (x - y)‖) :
    LipschitzOnWith (1 + ε) (f ∘ invFun A) (A '' P) ∧
      AntilipschitzWith (1 - ε)⁻¹ ((A '' P).domRestrict (f ∘ invFun A)) := by
  have hinv (x : U) : invFun A (A x) = x := leftInverse_invFun hA x
  have hε' : (0 : ℝ) < ((1 - ε : ℝ≥0) : ℝ) := NNReal.coe_pos.2 (tsub_pos_of_lt hε)
  refine ⟨LipschitzOnWith.of_dist_le_mul ?_, AntilipschitzWith.of_le_mul_dist ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h := happ x hx y hy
    rw [map_sub] at h
    simp only [comp_apply, hinv, dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
    calc ‖f x - f y‖ = ‖(f x - f y - (A x - A y)) + (A x - A y)‖ := by rw [sub_add_cancel]
      _ ≤ ε * ‖A x - A y‖ + ‖A x - A y‖ := norm_add_le_of_le h le_rfl
      _ = (1 + ε) * ‖A x - A y‖ := by ring
  · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
    simp only [Subtype.dist_eq, domRestrict_apply, comp_apply, hinv, dist_eq_norm, NNReal.coe_inv]
    rw [le_inv_mul_iff₀ hε', NNReal.coe_sub hε.le, NNReal.coe_one]
    exact mul_norm_sub_le_of_approx happ hx hy

/-- A map within relative error `ε < 1` of an injective linear map on `P` is injective on `P`. -/
private lemma injOn_of_approx (hA : Injective A) (hε : ε < 1)
    (happ : ∀ x ∈ P, ∀ y ∈ P, ‖f x - f y - A (x - y)‖ ≤ ε * ‖A (x - y)‖) : InjOn f P := by
  intro x hx y hy hxy
  have h := mul_norm_sub_le_of_approx happ hx hy
  rw [hxy, sub_self, norm_zero] at h
  have hε' : (0 : ℝ) < 1 - ε := sub_pos.2 (by exact_mod_cast hε)
  exact hA (sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm
    (nonpos_of_mul_nonpos_right h hε') (norm_nonneg _))))

end Approximation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E : Set V}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The range of an injective linear map from `k`-dimensional Euclidean space is the range of an
isometry from that space. -/
private lemma exists_isometry_range_eq (A : EuclideanSpace ℝ (Fin k) →L[ℝ] V) (hA : Injective A) :
    ∃ ι : EuclideanSpace ℝ (Fin k) → V, Isometry ι ∧ range ι = range A := by
  set L := LinearMap.range (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] V)
  have hL : finrank ℝ L = k := by
    rw [LinearMap.finrank_range_of_inj hA, finrank_euclideanSpace_fin]
  let e := ((stdOrthonormalBasis ℝ L).reindex (finCongr hL)).repr.symm
  refine ⟨L.subtypeₗᵢ ∘ e, L.subtypeₗᵢ.isometry.comp e.isometry, Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := LinearMap.mem_range.1 (e z).2
    exact ⟨x, hx⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨e.symm ⟨A x, x, rfl⟩, by simp⟩

omit [FiniteDimensional ℝ V] in
/-- On a piece `f '' P` where the Lipschitz map `f` is within relative error `ε < 1` of an injective
linear map, a set `E` of finite measure has its densities controlled almost everywhere: the part of
`E` in the piece has upper density at most `((1 - ε)⁻¹ (1 + ε)) ^ k` and lower density at least the
inverse, and the part of `E` off the piece has density zero. -/
private theorem ae_density_bounds_of_approx (hEm : NullMeasurableSet E μHE[k])
    (hfin : μHE[k] E ≠ ∞) {f : EuclideanSpace ℝ (Fin k) → V} {K : ℝ≥0} (hf : LipschitzWith K f)
    {P : Set (EuclideanSpace ℝ (Fin k))} (hPm : MeasurableSet P)
    {A : EuclideanSpace ℝ (Fin k) →L[ℝ] V} (hA : P.Nonempty → Injective A) {ε : ℝ≥0} (hε : ε < 1)
    (happ : ∀ x ∈ P, ∀ y ∈ P, ‖f x - f y - A (x - y)‖ ≤ ε * ‖A (x - y)‖) :
    ∀ᵐ y ∂μHE[k], y ∈ E ∩ f '' P →
      limsup (fun r => μHE[k] (E ∩ f '' P ∩ closedBall y r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) ≤
          (((1 - ε)⁻¹ * (1 + ε) : ℝ≥0) : ℝ≥0∞) ^ k ∧
      ((((1 - ε)⁻¹ * (1 + ε) : ℝ≥0) : ℝ≥0∞) ^ k)⁻¹ ≤
        liminf (fun r => μHE[k] (E ∩ f '' P ∩ closedBall y r) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) ∧
      Tendsto (fun r => μHE[k] (E \ f '' P ∩ closedBall y r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · exact ae_of_all _ fun y hy => by simp at hy
  replace hA := hA hP
  obtain ⟨hlip, hanti⟩ := lipschitzOnWith_and_antilipschitzWith_of_approx hA hε happ
  obtain ⟨ι, hι, hιA⟩ := exists_isometry_range_eq A hA
  -- Read through `A`, the piece is a bi-Lipschitz image of the subset `A '' P` of a `k`-plane.
  have himage : (f ∘ invFun A) '' (A '' P) = f '' P := by
    rw [image_image]
    exact image_congr fun x _ => by rw [comp_apply, leftInverse_invFun hA x]
  have hdens := ae_limsup_le_and_le_liminf hι (hιA ▸ image_subset_range _ _) hlip hanti
    (inv_pos.2 (tsub_pos_of_lt hε)) (add_pos_of_pos_of_nonneg one_pos (by positivity))
    (T := E ∩ f '' P) (himage ▸ inter_subset_right)
  -- The part of `E` off the piece has density zero at almost every point of the piece.
  have hmeas : MeasurableSet (f '' P) :=
    hPm.image_of_continuousOn_injOn hf.continuous.continuousOn (injOn_of_approx hA hε happ)
  have hzero := ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div k
    (hEm.diff hmeas.nullMeasurableSet) (ne_top_of_le_ne_top hfin (measure_mono sdiff_subset))
  filter_upwards [hdens, hzero] with y h1 h2 hy
  exact ⟨(h1 hy).1, (h1 hy).2, h2 fun h => h.2 hy.2⟩

/-- The density theorem for a rectifiable set of finite measure. -/
private theorem CountablyRectifiable.ae_tendsto_of_ne_top (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) (hfin : μHE[k] E ≠ ∞) :
    ∀ᵐ x ∂μHE[k], x ∈ E → Tendsto (fun r => μHE[k] (E ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) := by
  classical
  set D : Set V → V → ℝ → ℝ≥0∞ := fun S y r =>
    μHE[k] (S ∩ closedBall y r) / volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)
  obtain ⟨F, hF, hcover⟩ := hE.exists_lipschitzWith_cover
  choose KF hKF using hF
  -- Relative errors `ε n → 0` and the resulting distortion constants `c n → 1`.
  obtain ⟨ε, hε0, hε1, hεlim⟩ : ∃ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n) ∧ (∀ n, ε n < 1) ∧
      Tendsto ε atTop (𝓝 0) := by
    refine ⟨fun n => ((n : ℝ≥0) + 1)⁻¹ / 2, fun n => by positivity, fun n => ?_, by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).div_const 2⟩
    calc ((n : ℝ≥0) + 1)⁻¹ / 2 ≤ 1 / 2 := by
          gcongr
          exact inv_le_one_of_one_le₀ le_add_self
      _ < 1 := by norm_num
  set c : ℕ → ℝ≥0∞ := fun n => (((1 - ε n)⁻¹ * (1 + ε n) : ℝ≥0) : ℝ≥0∞) ^ k
  have hclim : Tendsto c atTop (𝓝 1) := by
    have h : Tendsto (fun n => (1 - ε n)⁻¹ * (1 + ε n)) atTop (𝓝 ((1 - 0)⁻¹ * (1 + 0))) :=
      ((tendsto_const_nhds.sub hεlim).inv₀ (by simp)).mul (tendsto_const_nhds.add hεlim)
    have := ((ENNReal.continuous_pow k).tendsto _).comp ((ENNReal.continuous_coe.tendsto _).comp h)
    rwa [tsub_zero, inv_one, add_zero, mul_one, ENNReal.coe_one, one_pow] at this
  choose P A hPm hAinj happ hPcover using fun n m =>
    (hKF m).exists_linear_approximation_cover (NNReal.coe_pos.2 (hε0 n))
  -- On each piece `F m '' P n m j`, the densities of `E` are controlled almost everywhere.
  have hpiece (n m j : ℕ) := ae_density_bounds_of_approx hEm hfin (hKF m) (hPm n m j)
    (hAinj n m j) (hε1 n) (happ n m j)
  -- Almost every point of `E` lies in a piece for every `n`.
  have hcov : ∀ᵐ y ∂μHE[k], y ∈ E → ∀ n, ∃ m j, y ∈ F m '' P n m j := by
    have h2 (n m : ℕ) : μHE[k] (range (F m) \ ⋃ j, F m '' P n m j) = 0 := by
      simpa only [finrank_euclideanSpace_fin] using hPcover n m
    rw [ae_iff]
    refine measure_mono_null ?_ (measure_union_null hcover
      (measure_iUnion_null fun n => measure_iUnion_null fun m => h2 n m))
    intro y hy
    obtain ⟨hyE, hy⟩ := not_imp.1 hy
    simp only [not_forall, not_exists] at hy
    obtain ⟨n, hn⟩ := hy
    by_cases hyF : y ∈ ⋃ m, range (F m)
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hyF
      exact Or.inr (mem_iUnion₂.2 ⟨n, m, hm, fun h => by
        obtain ⟨j, hj⟩ := mem_iUnion.1 h
        exact hn m j hj⟩)
    · exact Or.inl ⟨hyE, hyF⟩
  filter_upwards [hcov, ae_all_iff.2 fun n => ae_all_iff.2 fun m => ae_all_iff.2 fun j =>
    hpiece n m j] with y hcovy hpy hyE
  have hbounds (n : ℕ) : limsup (D E y) (𝓝[>] 0) ≤ c n ∧ (c n)⁻¹ ≤ liminf (D E y) (𝓝[>] 0) := by
    obtain ⟨m, j, hy⟩ := hcovy hyE n
    obtain ⟨hsup, hinf, hzero⟩ := hpy n m j ⟨hyE, hy⟩
    refine ⟨?_, hinf.trans (liminf_le_liminf (Eventually.of_forall fun r => ?_))⟩
    · calc limsup (D E y) (𝓝[>] 0)
          ≤ limsup (D (E ∩ F m '' P n m j) y + D (E \ F m '' P n m j) y) (𝓝[>] 0) := by
            refine limsup_le_limsup (Eventually.of_forall fun r => ?_)
            simp only [D, Pi.add_apply]
            rw [← ENNReal.add_div]
            gcongr
            refine (measure_mono fun z hz => ?_).trans (measure_union_le _ _)
            by_cases hzF : z ∈ F m '' P n m j
            exacts [Or.inl ⟨⟨hz.1, hzF⟩, hz.2⟩, Or.inr ⟨⟨hz.1, hzF⟩, hz.2⟩]
        _ = limsup (D (E ∩ F m '' P n m j) y) (𝓝[>] 0) :=
            ENNReal.limsup_add_of_right_tendsto_zero hzero _
        _ ≤ c n := hsup
    · simp only [D]
      gcongr
      exact inter_subset_left
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · exact le_of_tendsto' (by simpa using tendsto_inv_iff.2 hclim) fun n => (hbounds n).2
  · exact ge_of_tendsto' hclim fun n => (hbounds n).1

/-- **The density theorem for rectifiable sets.** A countably `k`-rectifiable subset `E` of a
finite-dimensional real inner product space, measurable for `μHE[k]` and with locally finite
`μHE[k]` measure, has `k`-dimensional density one at `μHE[k]`-almost every point of `E`:
`μHE[k] (E ∩ closedBall x r) / (ω_k r ^ k) → 1` as `r → 0⁺`, where `ω_k r ^ k` is the volume of a
ball of radius `r` in `EuclideanSpace ℝ (Fin k)`. -/
theorem CountablyRectifiable.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → Tendsto (fun r => μHE[k] (E ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) := by
  -- Localize to the bounded pieces `E ∩ ball 0 n`, which have finite measure.
  have hfin (n : ℕ) : μHE[k] (E ∩ ball 0 n) ≠ ∞ := by
    rw [inter_comm, ← Measure.restrict_apply measurableSet_ball]
    exact measure_ball_lt_top.ne
  filter_upwards [ae_all_iff.2 fun n => (hE.mono inter_subset_left).ae_tendsto_of_ne_top
    (hEm.inter measurableSet_ball.nullMeasurableSet) (hfin n)] with x hx hxE
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  have hxn : x ∈ ball (0 : V) n := mem_ball_zero_iff.2 hn
  refine (hx n ⟨hxE, hxn⟩).congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (eventually_closedBall_subset (isOpen_ball.mem_nhds hxn))] with r hr
  rw [inter_assoc, inter_eq_right.2 hr]

end TauCeti
