/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

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
set. Such a set is null, so its perimeter vanishes, while the right derivative is twice the area
of its topological boundary `K` in codimension one: for degenerate bodies the right derivative is
neither the perimeter nor the area of the boundary.

The product coordinates are Mathlib's `Submodule.measurableEquivProd`, which preserves volume by
`Submodule.measurePreserving_measurableEquivProd`.

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

/-- The product of two sets in orthogonal coordinates along a subspace has the product volume. -/
private theorem volume_preimage_measurableEquivProd (V : Submodule ℝ E) (p : E) (S : Set V)
    (T : Set Vᗮ) : volume (V.measurableEquivProd p ⁻¹' S ×ˢ T) = volume S * volume T := by
  have hΦ : MeasurePreserving (V.measurableEquivProd p) volume volume := by
    simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
      V.measurePreserving_measurableEquivProd p
  rw [hΦ.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]

/-- A point is recovered from its orthogonal coordinates along a subspace. -/
private theorem eq_measurableEquivProd_add (V : Submodule ℝ E) (p x : E) :
    x = ((V.measurableEquivProd p x).1 : E) + p + (V.measurableEquivProd p x).2 := by
  conv_lhs => rw [← (V.measurableEquivProd p).symm_apply_apply x]
  rw [Submodule.measurableEquivProd_symm_apply, vadd_eq_add]
  abel

/-- If `k - p ∈ V`, both orthogonal coordinates of `x` along `V` based at `p` are at most as far
from those of `k` as `x` is from `k`. -/
private theorem norm_measurableEquivProd_le (V : Submodule ℝ E) {p k : E} (hkp : k - p ∈ V)
    (x : E) :
    ‖((V.measurableEquivProd p x).1 : E) + p - k‖ ≤ ‖x - k‖ ∧
      ‖((V.measurableEquivProd p x).2 : E)‖ ≤ ‖x - k‖ := by
  have hx := eq_measurableEquivProd_add V p x
  generalize V.measurableEquivProd p x = q at hx ⊢
  obtain ⟨v, w⟩ := q
  have hb : x - k = ((v : E) + p - k) + w := by
    rw [hx]
    abel
  have hvk : (v : E) + p - k ∈ V := by
    convert V.sub_mem v.2 hkp using 1
    abel
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((v : E) + p - k) w
    (Submodule.inner_right_of_mem_orthogonal hvk w.2)
  rw [← hb] at hpyth
  constructor <;>
    nlinarith [norm_nonneg ((v : E) + p - k), norm_nonneg (w : E), norm_nonneg (x - k)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem isometry_coe_add (V : Submodule ℝ E) (p : E) :
    Isometry fun v : V ↦ (v : E) + p :=
  (isometry_add_right p).comp isometry_subtype_coe

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem range_coe_add {A : AffineSubspace ℝ E} {p : E} (hp : p ∈ A) :
    range (fun v : A.direction ↦ (v : E) + p) = A := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact AffineSubspace.vadd_mem_of_mem_direction v.2 hp
  · intro hx
    exact ⟨⟨x - p, (AffineSubspace.vsub_right_mem_direction_iff_mem hp x).2 hx⟩,
      sub_add_cancel x p⟩

/-- Volume on the direction of `A`, transported to `A` through a base point, is the Euclidean
Hausdorff measure of the matching dimension. -/
private theorem volume_preimage_coe_add {A : AffineSubspace ℝ E} {p : E} (hp : p ∈ A)
    (S : Set E) :
    volume ((fun v : A.direction ↦ (v : E) + p) ⁻¹' S) =
      μHE[finrank ℝ A.direction] (S ∩ A) := by
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
    (isometry_coe_add A.direction p).euclideanHausdorffMeasure_preimage, range_coe_add hp]

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
  rcases K.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp
  have hpA := hKA hp
  set Φ := A.direction.measurableEquivProd p
  set g := fun v : A.direction ↦ (v : E) + p
  have hsub : Φ ⁻¹' ((g ⁻¹' K) ×ˢ closedBall 0 t) ⊆ K + t • closedBall (0 : E) 1 := by
    rintro x ⟨h₁, h₂⟩
    rw [smul_unitClosedBall_of_nonneg ht, eq_measurableEquivProd_add A.direction p x]
    exact add_mem_add h₁ (mem_closedBall_zero_iff.2 (mem_closedBall_zero_iff.1 h₂))
  calc μHE[finrank ℝ A.direction] K * volume (closedBall (0 : A.directionᗮ) t)
      = volume (Φ ⁻¹' ((g ⁻¹' K) ×ˢ closedBall 0 t)) := by
        rw [volume_preimage_measurableEquivProd, volume_preimage_coe_add hpA,
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
  rcases K.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp
  have hpA := hKA hp
  set Φ := A.direction.measurableEquivProd p
  set g := fun v : A.direction ↦ (v : E) + p
  have hsub : K + t • closedBall (0 : E) 1 ⊆
      Φ ⁻¹' ((g ⁻¹' (K + t • closedBall (0 : E) 1)) ×ˢ closedBall 0 t) := by
    rw [smul_unitClosedBall_of_nonneg ht]
    rintro _ ⟨k, hk, b, hb, rfl⟩
    obtain ⟨h₁, h₂⟩ := norm_measurableEquivProd_le A.direction
      (AffineSubspace.vsub_mem_direction (hKA hk) hpA) (k + b)
    rw [add_sub_cancel_left] at h₁ h₂
    rw [mem_closedBall_zero_iff] at hb
    exact ⟨⟨k, hk, _, mem_closedBall_zero_iff.2 (h₁.trans hb), add_sub_cancel k _⟩,
      mem_closedBall_zero_iff.2 (h₂.trans hb)⟩
  calc volume (K + t • closedBall (0 : E) 1)
      ≤ volume (Φ ⁻¹' ((g ⁻¹' (K + t • closedBall (0 : E) 1)) ×ˢ closedBall 0 t)) :=
        measure_mono hsub
    _ = _ := by rw [volume_preimage_measurableEquivProd, volume_preimage_coe_add hpA]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For compact `K ⊆ A`, the trace on `A` of the outer parallel set of radius `t` corresponds,
in coordinates along the direction of `A`, to the closed `t`-thickening of `K`. -/
private theorem preimage_coe_add_add_smul_closedBall {A : AffineSubspace ℝ E} {K : Set E}
    (hK : IsCompact K) (hKA : K ⊆ A) {p : E} (hp : p ∈ A) {t : ℝ} (ht : 0 ≤ t) :
    (fun v : A.direction ↦ (v : E) + p) ⁻¹' (K + t • closedBall (0 : E) 1) =
      cthickening t ((fun v : A.direction ↦ (v : E) + p) ⁻¹' K) := by
  rw [smul_unitClosedBall_of_nonneg ht, hK.add_closedBall_zero ht]
  ext v
  have h := Metric.infEDist_image (isometry_coe_add A.direction p) (x := v)
    (t := (fun v : A.direction ↦ (v : E) + p) ⁻¹' K)
  rw [image_preimage_eq_of_subset (hKA.trans (range_coe_add hp).symm.subset)] at h
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
  rcases K.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp
  have hpA := hKA hp
  set g := fun v : A.direction ↦ (v : E) + p
  have hg := isometry_coe_add A.direction p
  have hKg : IsCompact (g ⁻¹' K) := isCompact_of_isClosed_isBounded
    (hK.isClosed.preimage hg.continuous) (hg.antilipschitzWith.isBounded_preimage hK.isBounded)
  have hKmeas : volume (g ⁻¹' K) = μHE[finrank ℝ A.direction] K := by
    rw [volume_preimage_coe_add hpA, inter_eq_left.2 hKA]
  -- The upper bound is the volume of the thickening of `g ⁻¹' K`, which tends to its volume.
  have hupper : Tendsto (fun t : ℝ ↦ volume.real (cthickening t (g ⁻¹' K))) (𝓝[>] 0)
      (𝓝 ((μHE[finrank ℝ A.direction] : Measure E).real K)) := by
    rw [measureReal_def, ← hKmeas]
    exact ((ENNReal.tendsto_toReal hKg.measure_lt_top.ne).comp
      (tendsto_measure_cthickening_of_isCompact hKg)).mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  all_goals
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hb : 0 < volume.real (closedBall (0 : A.directionᗮ) t) :=
      ENNReal.toReal_pos (measure_closedBall_pos volume 0 ht).ne' measure_closedBall_lt_top.ne
    have hfin : volume (K + t • closedBall (0 : E) 1) ≠ ∞ :=
      (hK.add ((isCompact_closedBall 0 1).smul t)).measure_lt_top.ne
  · rw [le_div_iff₀ hb, measureReal_def, measureReal_def, measureReal_def,
      ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono hfin
      (euclideanHausdorffMeasure_mul_volume_closedBall_le_volume_add_smul_closedBall hKA t)
  · have h := volume_add_smul_closedBall_le_euclideanHausdorffMeasure_inter_mul_volume_closedBall
      hKA ht.le
    rw [← volume_preimage_coe_add hpA, preimage_coe_add_add_smul_closedBall hK hKA hpA ht.le] at h
    rw [div_le_iff₀ hb, measureReal_def, measureReal_def, measureReal_def,
      ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hKg.isBounded.cthickening.measure_lt_top.ne
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
  have : Nontrivial A.directionᗮ := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  -- The unit ball of a line has length `2`.
  have hball : volume.real (closedBall (0 : A.directionᗮ) 1) = 2 := by
    rw [measureReal_def, InnerProductSpace.volume_closedBall, hW, Nat.cast_one,
      ENNReal.ofReal_one, one_pow, one_mul, pow_one, ENNReal.toReal_ofReal (by positivity),
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    field_simp
  rw [hasDerivWithinAt_iff_tendsto_slope, sdiff_singleton_eq_self (lt_irrefl _),
    show finrank ℝ E - 1 = finrank ℝ A.direction by omega]
  refine ((tendsto_volume_real_add_smul_closedBall_div hK hKA).const_mul 2).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [slope_def_field, volume_real_add_zero_smul_closedBall hKA (by omega),
    Measure.addHaar_real_closedBall' _ _ ht.le, hW, hball, sub_zero, sub_zero]
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
  have hb0 : 0 < volume.real (closedBall (0 : A.directionᗮ) t) :=
    ENNReal.toReal_pos (measure_closedBall_pos volume 0 ht).ne' measure_closedBall_lt_top.ne
  rw [slope_def_field, volume_real_add_zero_smul_closedBall hKA (by omega), sub_zero, sub_zero]
  rw [hb] at hb0 ⊢
  have hc : c ≠ 0 := fun hc ↦ by simp [hc] at hb0
  field_simp

end TauCeti
