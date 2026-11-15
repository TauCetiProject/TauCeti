/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Calculus.Deriv.Slope
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Outer parallel volume of sets in affine subspaces

Let `A` be an affine subspace of dimension `k` in a finite-dimensional real inner product space
`E` of dimension `n`, and let `K ⊆ A`. The outer parallel set `K + t • closedBall 0 1` is
squeezed between two products in the orthogonal coordinates `A.direction × A.directionᗮ`
based at a point of `A`: it contains `K` times the ball of radius `t` in `A.directionᗮ`, and it
is contained in its own trace on `A` times that ball. Measuring the trace on `A` with the
Euclidean Hausdorff measure `μHE[k]`, which is volume on `A`, and writing `P t` for the parallel
set and `β t` for the volume of the ball of radius `t` in `A.directionᗮ`, this gives

`μHE[k] K * β t ≤ volume (P t) ≤ μHE[k] (P t ∩ A) * β t`.

For compact `K` the trace on `A` is the closed `t`-thickening of `K` inside `A`, whose measure
tends to `μHE[k] K`. Hence the volume of the outer parallel set divided by the volume of the
ball of radius `t` in `A.directionᗮ` tends to `μHE[k] K`: the `k`-dimensional Minkowski content
of `K` is its `k`-dimensional Euclidean Hausdorff measure.

Since `K` is null in `E` when `k < n`, the right derivative at `0` of the parallel volume
`t ↦ volume (K + t • closedBall 0 1)` follows. When `k = n - 1` it is `2 * μHE[n - 1] K`, twice
the area of `K`, because the ball of radius `t` in a line has length `2 t`; when `k ≤ n - 2` it
is zero. Taking `A` to be the affine span, this applies to every lower-dimensional compact convex
set.

The product coordinates are Mathlib's `Submodule.measurableEquivProd`, which preserves volume by
`Submodule.measurePreserving_measurableEquivProd`. Coordinates on `A` itself are its directions
added to a base point, as in Mathlib's `IsometryEquiv.vaddConst`.

## Main results

* `TauCeti.euclideanHausdorffMeasure_mul_volume_closedBall_le_volume_add_smul_closedBall` and
  `TauCeti.volume_add_smul_closedBall_le_euclideanHausdorffMeasure_inter_mul_volume_closedBall`:
  the two product bounds.
* `TauCeti.tendsto_volume_real_add_smul_closedBall_div`: the Minkowski content of a compact
  subset of an affine subspace is its Euclidean Hausdorff measure.
* `TauCeti.hasDerivWithinAt_volume_real_add_smul_closedBall_of_finrank_add_one_eq`: in
  codimension one the right derivative of parallel volume is twice the area.
* `TauCeti.hasDerivWithinAt_volume_real_add_smul_closedBall_of_finrank_add_two_le`: in
  codimension at least two it vanishes.

## References

* J. A. Tropp, *Lectures on Convex Geometry*, Lecture 8, for outer parallel volumes of convex
  bodies, including lower-dimensional ones.
* H. Federer, *Geometric Measure Theory*, Springer, 1969, §3.2.37–3.2.39, for Minkowski content.
-/

public section

open Filter MeasureTheory Metric Module Set Topology
open scoped ENNReal Pointwise RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Lower product bound for outer parallel volume.** If `K` lies in an affine subspace `A`,
then the volume of `K + t • closedBall 0 1` is at least the Euclidean Hausdorff measure of `K` in
the dimension of `A` times the volume of the ball of radius `t` in the orthogonal complement of
the direction of `A`. -/
theorem euclideanHausdorffMeasure_mul_volume_closedBall_le_volume_add_smul_closedBall
    {A : AffineSubspace ℝ E} {K : Set E} (hKA : K ⊆ A) (t : ℝ) :
    μHE[finrank ℝ A.direction] K * volume (closedBall (0 : A.directionᗮ) t) ≤
      volume (K + t • closedBall (0 : E) 1) := by
  rcases lt_or_ge t 0 with ht | ht
  · simp [closedBall_eq_empty.2 ht]
  rcases K.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
  · simp
  lift q to A using hKA hq
  have : Nonempty A := ⟨q⟩
  set Φ := A.direction.measurableEquivProd (q : E)
  set g := fun v : A.direction ↦ ((v +ᵥ q : A) : E)
  have hsub : Φ ⁻¹' ((g ⁻¹' K) ×ˢ closedBall 0 t) ⊆ K + t • closedBall (0 : E) 1 := by
    rintro x ⟨h₁, h₂⟩
    simp only [g, mem_preimage, AffineSubspace.coe_vadd, vadd_eq_add] at h₁
    rw [mem_closedBall_zero_iff, ← Submodule.norm_coe] at h₂
    rw [smul_unitClosedBall_of_nonneg ht, ← A.direction.measurableEquivProd_fst_add_add_snd q x]
    exact add_mem_add h₁ (mem_closedBall_zero_iff.2 h₂)
  calc μHE[finrank ℝ A.direction] K * volume (closedBall (0 : A.directionᗮ) t)
      = volume (Φ ⁻¹' ((g ⁻¹' K) ×ˢ closedBall 0 t)) := by
        rw [Submodule.volume_preimage_measurableEquivProd_prod, A.volume_preimage_coe_vadd q,
          inter_eq_left.2 hKA]
    _ ≤ volume (K + t • closedBall (0 : E) 1) := measure_mono hsub

/-- **Upper product bound for outer parallel volume.** If `K` lies in an affine subspace `A`,
then the volume of `K + t • closedBall 0 1` is at most the Euclidean Hausdorff measure of its
trace on `A`, in the dimension of `A`, times the volume of the ball of radius `t` in the
orthogonal complement of the direction of `A`. -/
theorem volume_add_smul_closedBall_le_euclideanHausdorffMeasure_inter_mul_volume_closedBall
    {A : AffineSubspace ℝ E} {K : Set E} (hKA : K ⊆ A) {t : ℝ} (ht : 0 ≤ t) :
    volume (K + t • closedBall (0 : E) 1) ≤
      μHE[finrank ℝ A.direction] ((K + t • closedBall (0 : E) 1) ∩ A) *
        volume (closedBall (0 : A.directionᗮ) t) := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
  · simp
  lift q to A using hKA hq
  have : Nonempty A := ⟨q⟩
  set Φ := A.direction.measurableEquivProd (q : E)
  set g := fun v : A.direction ↦ ((v +ᵥ q : A) : E)
  have hsub : K + t • closedBall (0 : E) 1 ⊆
      Φ ⁻¹' ((g ⁻¹' (K + t • closedBall (0 : E) 1)) ×ˢ closedBall 0 t) := by
    rw [smul_unitClosedBall_of_nonneg ht]
    rintro _ ⟨k, hk, b, hb, rfl⟩
    obtain ⟨h₁, h₂⟩ := A.direction.norm_measurableEquivProd_le
      (AffineSubspace.vsub_mem_direction (hKA hk) q.2) (k + b)
    rw [add_sub_cancel_left] at h₁ h₂
    rw [mem_closedBall_zero_iff] at hb
    simp only [g, mem_preimage, mem_prod, AffineSubspace.coe_vadd, vadd_eq_add]
    rw [mem_closedBall_zero_iff, ← Submodule.norm_coe]
    exact ⟨⟨k, hk, _, mem_closedBall_zero_iff.2 (h₁.trans hb), add_sub_cancel k _⟩, h₂.trans hb⟩
  calc volume (K + t • closedBall (0 : E) 1)
      ≤ volume (Φ ⁻¹' ((g ⁻¹' (K + t • closedBall (0 : E) 1)) ×ˢ closedBall 0 t)) :=
        measure_mono hsub
    _ = _ := by
      rw [Submodule.volume_preimage_measurableEquivProd_prod, A.volume_preimage_coe_vadd q]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For compact `K` in an affine subspace `A` with base point `q`, the directions `v` of `A` with
`v +ᵥ q` in the outer parallel set `K + t • closedBall 0 1` form the closed `t`-thickening of the
directions `v` with `v +ᵥ q ∈ K`. -/
theorem preimage_coe_vadd_add_smul_closedBall {A : AffineSubspace ℝ E} [Nonempty A] (q : A)
    {K : Set E} (hK : IsCompact K) (hKA : K ⊆ A) {t : ℝ} (ht : 0 ≤ t) :
    (fun v : A.direction ↦ ((v +ᵥ q : A) : E)) ⁻¹' (K + t • closedBall (0 : E) 1) =
      cthickening t ((fun v : A.direction ↦ ((v +ᵥ q : A) : E)) ⁻¹' K) := by
  set g := fun v : A.direction ↦ ((v +ᵥ q : A) : E)
  have hg : Isometry g := A.isometry_coe_vadd q
  have hrange : range g = A := A.range_coe_vadd q
  rw [smul_unitClosedBall_of_nonneg ht, hK.add_closedBall_zero ht]
  ext v
  have h := Metric.infEDist_image hg (x := v) (t := g ⁻¹' K)
  rw [image_preimage_eq_of_subset (hKA.trans hrange.symm.subset)] at h
  simp only [mem_preimage, mem_cthickening_iff, h]

/-- **Minkowski content of a compact subset of an affine subspace.** If `K` is compact and lies
in an affine subspace `A`, the volume of `K + t • closedBall 0 1` divided by the volume of the
ball of radius `t` in the orthogonal complement of the direction of `A` tends to the Euclidean
Hausdorff measure of `K` in the dimension of `A` as `t → 0⁺`. -/
theorem tendsto_volume_real_add_smul_closedBall_div {A : AffineSubspace ℝ E} {K : Set E}
    (hK : IsCompact K) (hKA : K ⊆ A) :
    Tendsto (fun t : ℝ ↦ volume.real (K + t • closedBall (0 : E) 1) /
        volume.real (closedBall (0 : A.directionᗮ) t))
      (𝓝[>] 0) (𝓝 ((μHE[finrank ℝ A.direction] : Measure E).real K)) := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
  · simp
  lift q to A using hKA hq
  have : Nonempty A := ⟨q⟩
  set g := fun v : A.direction ↦ ((v +ᵥ q : A) : E)
  have hKg : IsCompact (g ⁻¹' K) := (A.isometry_coe_vadd q).isClosedEmbedding.isCompact_preimage hK
  have hKmeas : volume (g ⁻¹' K) = μHE[finrank ℝ A.direction] K := by
    rw [A.volume_preimage_coe_vadd q, inter_eq_left.2 hKA]
  -- The upper bound is the volume of the thickening of `g ⁻¹' K`, which tends to its volume.
  have hupper : Tendsto (fun t : ℝ ↦ volume.real (cthickening t (g ⁻¹' K))) (𝓝[>] 0)
      (𝓝 ((μHE[finrank ℝ A.direction] : Measure E).real K)) := by
    rw [measureReal_def, ← hKmeas]
    exact ((ENNReal.tendsto_toReal hKg.measure_lt_top.ne).comp
      (tendsto_measure_cthickening_of_isCompact hKg)).mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  all_goals
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hb := measureReal_closedBall_pos volume (0 : A.directionᗮ) ht
  -- Both bounds pass from `ℝ≥0∞` to `ℝ` through `ENNReal.toReal_mono` and `ENNReal.toReal_mul`.
  · rw [le_div_iff₀ hb]
    simpa only [measureReal_def, ENNReal.toReal_mul] using ENNReal.toReal_mono
      (hK.add ((isCompact_closedBall 0 1).smul t)).measure_lt_top.ne
      (euclideanHausdorffMeasure_mul_volume_closedBall_le_volume_add_smul_closedBall hKA t)
  · have h := volume_add_smul_closedBall_le_euclideanHausdorffMeasure_inter_mul_volume_closedBall
      hKA ht.le
    rw [← A.volume_preimage_coe_vadd q, preimage_coe_vadd_add_smul_closedBall q hK hKA ht.le] at h
    rw [div_le_iff₀ hb]
    simpa only [measureReal_def, ENNReal.toReal_mul] using ENNReal.toReal_mono
      (ENNReal.mul_ne_top hKg.isBounded.cthickening.measure_lt_top.ne
        measure_closedBall_lt_top.ne) h

/-- A subset of an affine subspace of positive codimension has parallel volume `0` at radius
`0`. -/
private theorem volume_real_add_zero_smul_closedBall {A : AffineSubspace ℝ E} {K : Set E}
    (hKA : K ⊆ A) (hA : finrank ℝ A.direction < finrank ℝ E) :
    volume.real (K + (0 : ℝ) • closedBall (0 : E) 1) = 0 := by
  have hA' : A ≠ ⊤ := by
    rintro rfl
    rw [AffineSubspace.direction_top, finrank_top] at hA
    exact lt_irrefl _ hA
  rw [zero_smul_set (nonempty_closedBall.2 zero_le_one), add_zero, measureReal_def,
    measure_mono_null hKA (Measure.addHaar_affineSubspace volume A hA'), ENNReal.toReal_zero]

/-- **Right derivative of parallel volume in codimension one.** If a compact set `K` lies in an
affine hyperplane, the parallel volume `t ↦ volume (K + t • closedBall 0 1)` has right
derivative `2 * μHE[n - 1] K` at `0`, where `n` is the dimension of the ambient space. This
applies to every compact convex set of affine dimension `n - 1`, with `A` its affine span. -/
theorem hasDerivWithinAt_volume_real_add_smul_closedBall_of_finrank_add_one_eq
    {A : AffineSubspace ℝ E} {K : Set E} (hK : IsCompact K) (hKA : K ⊆ A)
    (hA : finrank ℝ A.direction + 1 = finrank ℝ E) :
    HasDerivWithinAt (fun t : ℝ ↦ volume.real (K + t • closedBall (0 : E) 1))
      (2 * (μHE[finrank ℝ E - 1] : Measure E).real K) (Ioi 0) 0 := by
  have hW : finrank ℝ A.directionᗮ = 1 := by
    have := A.direction.finrank_add_finrank_orthogonal
    omega
  rw [hasDerivWithinAt_iff_tendsto_slope, sdiff_singleton_eq_self (lt_irrefl _),
    show finrank ℝ E - 1 = finrank ℝ A.direction by omega]
  refine ((tendsto_volume_real_add_smul_closedBall_div hK hKA).const_mul 2).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [slope_def_field, volume_real_add_zero_smul_closedBall hKA (by omega),
    volume_real_closedBall_of_finrank_eq_one hW 0 ht.le, sub_zero, sub_zero]
  field_simp

/-- **Right derivative of parallel volume in codimension at least two.** If a compact set `K`
lies in an affine subspace of codimension at least two, the parallel volume
`t ↦ volume (K + t • closedBall 0 1)` has right derivative `0` at `0`. This applies to every
compact convex set of affine dimension at most `n - 2`, with `A` its affine span. -/
theorem hasDerivWithinAt_volume_real_add_smul_closedBall_of_finrank_add_two_le
    {A : AffineSubspace ℝ E} {K : Set E} (hK : IsCompact K) (hKA : K ⊆ A)
    (hA : finrank ℝ A.direction + 2 ≤ finrank ℝ E) :
    HasDerivWithinAt (fun t : ℝ ↦ volume.real (K + t • closedBall (0 : E) 1)) 0
      (Ioi 0) 0 := by
  set m := finrank ℝ A.directionᗮ
  have hm : 2 ≤ m := by
    have := A.direction.finrank_add_finrank_orthogonal
    omega
  set c := volume.real (closedBall (0 : A.directionᗮ) 1)
  -- The ball of radius `t` in the normal space has volume `c * t ^ m`, which is `o(t)`.
  have hsmall : Tendsto (fun t : ℝ ↦ t ^ (m - 1) * c) (𝓝[>] 0) (𝓝 0) := by
    have h := ((continuous_pow (m - 1)).tendsto (0 : ℝ)).mul_const c
    rw [zero_pow (by omega), zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  rw [hasDerivWithinAt_iff_tendsto_slope, sdiff_singleton_eq_self (lt_irrefl _)]
  have h := (tendsto_volume_real_add_smul_closedBall_div hK hKA).mul hsmall
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hb : volume.real (closedBall (0 : A.directionᗮ) t) = t ^ (m - 1) * c * t := by
    rw [Measure.addHaar_real_closedBall' _ _ ht.le, mul_right_comm, ← pow_succ,
      Nat.sub_add_cancel (by omega)]
  have hb0 := measureReal_closedBall_pos volume (0 : A.directionᗮ) ht
  rw [slope_def_field, volume_real_add_zero_smul_closedBall hKA (by omega), sub_zero, sub_zero]
  rw [hb] at hb0 ⊢
  have hc : c ≠ 0 := fun hc ↦ by simp [hc] at hb0
  field_simp

end TauCeti
