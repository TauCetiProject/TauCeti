/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.TangentialFDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Check: the tangential area formula on `ℝ × ℤ`

Let `M = ℝ × ℤ ⊆ ℝ²` be the union of the horizontal lines at integer heights (`integerLines`),
`k = 1`, `f(t, m) = t` (`firstCoord`) and `g(t, m) = 2^{-|m|}` for `t ∈ [0, 1]`, `0` otherwise
(`weight`). Both sides of the tangential area formula
`∫_M g J dH¹ = ∫_ℝ Σ_{x ∈ M ∩ f⁻¹(y)} g(x) dy` are `3`:

* the tangential Jacobian of `f` along `M` is `1` at every point of `M`
  (`tangentialJacobian_integerLines`), computed from the chart `t ↦ (t, m)` by
  `HasFDerivWithinAt.tangentialJacobian_mul_normDet`;
* so the left side is `Σ_{m ∈ ℤ} 2^{-|m|} = 1 + 2 · 1 = 3` (`lintegral_integerLines`);
* every fibre `M ∩ f⁻¹(y)`, `y ∈ [0, 1]`, is `{(y, m) : m ∈ ℤ}`, with sum `3`
  (`tsum_fibre`), so the right side is `3` (`lintegral_tsum_fibre`).

The fibres are infinite and the weight is positive on all of their points (`infinite_fibre`,
`weight_pos`): a fibre sum set to `∞` whenever infinitely many terms are positive would make the
right side `∞`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §12 (the area formula on rectifiable sets).
-/

open MeasureTheory Measure Set Metric Module Filter Topology Function
open scoped ENNReal NNReal

public noncomputable section

namespace TauCeti.Examples.IntegerLines

open TauCeti

/-- The point `(t, s)` of the plane `ℝ²`. -/
def pt (t s : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  t • EuclideanSpace.single 0 1 + s • EuclideanSpace.single 1 1

/-- The first coordinate of `(t, s)` is `t`. -/
@[simp]
theorem pt_apply_zero (t s : ℝ) : pt t s 0 = t := by simp [pt]

/-- The second coordinate of `(t, s)` is `s`. -/
@[simp]
theorem pt_apply_one (t s : ℝ) : pt t s 1 = s := by simp [pt]

/-- Every point of `ℝ²` is `(x₀, x₁)`. -/
theorem eq_pt (x : EuclideanSpace ℝ (Fin 2)) : x = pt (x 0) (x 1) := by
  ext i
  fin_cases i <;> simp

/-- Each horizontal line `t ↦ (t, s)` is an isometric embedding of `ℝ`. -/
theorem isometry_pt (s : ℝ) : Isometry fun t ↦ pt t s :=
  Isometry.of_dist_eq fun a b ↦ by
    simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.sqrt_sq_eq_abs]

/-- `ℝ × ℤ`: the union of the horizontal lines of `ℝ²` at integer heights. -/
def integerLines : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∃ m : ℤ, x 1 = m}

/-- The first coordinate `f(t, s) = t`. -/
def firstCoord (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  x 0

/-- The weight `g(t, s) = 2^{-|s|}` for `t ∈ [0, 1]`, `0` otherwise. -/
def weight (x : EuclideanSpace ℝ (Fin 2)) : ℝ≥0∞ :=
  (Icc (0 : ℝ) 1).indicator 1 (x 0) * ENNReal.ofReal ((2 : ℝ) ^ (-|x 1|))

/-- The weight is measurable. -/
theorem measurable_weight : Measurable weight := by
  refine Measurable.mul ((measurable_const.indicator measurableSet_Icc).comp
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).measurable)
    (ENNReal.measurable_ofReal.comp ?_)
  exact measurable_const.pow (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).abs.neg.measurable

/-- `ℝ × ℤ` is the union of the lines `t ↦ (t, m)`, `m ∈ ℤ`. -/
theorem integerLines_eq_iUnion : integerLines = ⋃ m : ℤ, range fun t ↦ pt t m := by
  ext x
  simp only [integerLines, mem_ofPred_eq, mem_iUnion, mem_range]
  refine ⟨fun ⟨m, hm⟩ ↦ ⟨m, x 0, by rw [← hm, ← eq_pt]⟩, ?_⟩
  rintro ⟨m, t, rfl⟩
  exact ⟨m, pt_apply_one t m⟩

/-- The line `t ↦ (t, s)` is the set of points with second coordinate `s`. -/
theorem range_pt (s : ℝ) : (range fun t ↦ pt t s) = {x | x 1 = s} := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨x 0, by rw [eq_pt x, ← show x 1 = s from hx]; simp⟩⟩
  rintro ⟨t, rfl⟩
  exact pt_apply_one t s

/-- Each horizontal line is measurable. -/
theorem measurableSet_range_pt (s : ℝ) : MeasurableSet (range fun t ↦ pt t s) := by
  rw [range_pt]
  exact measurableSet_eq_fun (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).measurable
    measurable_const

/-- `ℝ × ℤ` is measurable. -/
theorem measurableSet_integerLines : MeasurableSet integerLines := by
  rw [integerLines_eq_iUnion]
  exact MeasurableSet.iUnion fun m ↦ measurableSet_range_pt m

/-- Away from its own line, a point of `ℝ × ℤ` is at distance at least `1`. -/
theorem one_le_dist {x y : EuclideanSpace ℝ (Fin 2)} {m m' : ℤ} (hx : x 1 = m) (hy : y 1 = m')
    (hmm' : m ≠ m') : 1 ≤ dist x y := by
  have h1 : (1 : ℝ) ≤ |(m : ℝ) - m'| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmm')
  calc (1 : ℝ) ≤ |x 1 - y 1| := by rwa [hx, hy]
    _ = ‖(x - y) 1‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖x - y‖ := PiLp.norm_apply_le _ _
    _ = dist x y := (dist_eq_norm x y).symm

/-- Within distance `r < 1` of a point of the line at height `m`, `ℝ × ℤ` is that line. -/
theorem diff_image_inter_closedBall_eq_empty (m : ℤ) (t : ℝ) {r : ℝ} (hr : r < 1) :
    (integerLines \ (fun t ↦ pt t m) '' univ) ∩ closedBall (pt t m) r = ∅ := by
  refine eq_empty_of_forall_notMem fun z ⟨⟨⟨m', hm'⟩, hz⟩, hzr⟩ ↦ ?_
  have hne : m' ≠ m := by
    rintro rfl
    exact hz ⟨z 0, mem_univ _, by rw [← hm']; exact (eq_pt z).symm⟩
  exact (one_le_dist hm' (pt_apply_one t m) hne).not_gt ((mem_closedBall.mp hzr).trans_lt hr)

/-- **The tangential Jacobian is `1`.** At every point of `ℝ × ℤ` the tangential Jacobian of the
first coordinate along `ℝ × ℤ` is `1`: on the chart `t ↦ (t, m)`, both the chart and `f` composed
with it have norm determinant `1`. -/
theorem tangentialJacobian_integerLines {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ integerLines) :
    tangentialJacobian 1 integerLines firstCoord x = 1 := by
  obtain ⟨m, hm⟩ := hx
  set e₀ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  let A : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) := (ContinuousLinearMap.id ℝ ℝ).smulRight e₀
  have hA (t : ℝ) : A t = t • e₀ := rfl
  have hpt : (fun t ↦ pt t m) = fun t ↦ t • e₀ + (m : ℝ) • EuclideanSpace.single 1 1 := rfl
  have hf : HasFDerivWithinAt (fun t ↦ pt t m) A univ (x 0) := by
    have h : HasFDerivAt (fun t : ℝ ↦ t • e₀) A (x 0) := by
      simpa using (hasFDerivAt_id (𝕜 := ℝ) (x 0)).smul_const e₀
    rw [hpt]
    exact (h.add_const _).hasFDerivWithinAt
  have hinj : Injective A := fun a b h ↦ by simpa [hA, e₀] using congrArg (· 0) h
  have hi : AntilipschitzWith 1 (univ.domRestrict fun t ↦ pt t m) :=
    ((isometry_pt m).comp isometry_subtypeVal).antilipschitzWith
  have hsub : (fun t ↦ pt t m) '' univ ⊆ integerLines := by
    rintro _ ⟨t, -, rfl⟩
    exact ⟨m, pt_apply_one t m⟩
  have hdens : Tendsto (fun r ↦ volume (univ ∩ closedBall (x 0) r) /
      volume (closedBall (0 : ℝ) r)) (𝓝[>] 0) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [univ_inter, Real.volume_closedBall, Real.volume_closedBall,
      ENNReal.div_self (by simpa using hr) ENNReal.ofReal_ne_top]
  have hdiff : Tendsto (fun r ↦ μHE[finrank ℝ ℝ] ((integerLines \ (fun t ↦ pt t m) '' univ) ∩
      closedBall (pt (x 0) m) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ ℝ))) r)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with r ⟨_, hr⟩
    rw [eq_comm, ENNReal.div_eq_zero_iff]
    left
    rw [diff_image_inter_closedBall_eq_empty m (x 0) hr, measure_empty]
  have hgf : HasFDerivWithinAt (firstCoord ∘ fun t ↦ pt t m) (ContinuousLinearMap.id ℝ ℝ) univ
      (x 0) := by
    have : (firstCoord ∘ fun t ↦ pt t m) = id := funext fun t ↦ by simp [firstCoord]
    rw [this]
    exact HasFDerivAt.hasFDerivWithinAt (hasFDerivAt_id _)
  have h := hf.tangentialJacobian_mul_normDet hinj hi (mem_univ _) hsub hdens hdiff hgf
  have hnA : A.toLinearMap.normDet = 1 := by
    rw [LinearMap.normDet_eq_norm_apply_one, ContinuousLinearMap.coe_coe, hA, one_smul]
    simp [e₀]
  rw [hnA, mul_one, ContinuousLinearMap.coe_id, LinearMap.normDet_id, finrank_self,
    ← show x 1 = m from hm, ← eq_pt] at h
  exact h

/-- `Σ_{m ∈ ℤ} 2^{-|m|} = 3`. -/
theorem tsum_two_rpow_neg_abs : ∑' m : ℤ, ENNReal.ofReal ((2 : ℝ) ^ (-|(m : ℝ)|)) = 3 := by
  have h (m : ℤ) : ENNReal.ofReal ((2 : ℝ) ^ (-|(m : ℝ)|)) = 2⁻¹ ^ m.natAbs := by
    rw [Real.rpow_neg zero_le_two, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast,
      Real.rpow_natCast, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat, ENNReal.inv_pow]
  simp_rw [h]
  rw [tsum_of_nat_of_neg_add_one CompleteLattice.summable CompleteLattice.summable]
  have hpos : ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (-((n : ℤ) + 1)).natAbs = 1 := by
    have hn (n : ℕ) : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    simp_rw [hn, pow_succ', ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two,
      inv_inv]
    exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
  rw [hpos]
  simp only [Int.natAbs_natCast, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  norm_num

/-- The weight integrates to `2^{-|m|}` over the line at height `m`. -/
theorem lintegral_range_pt (m : ℤ) :
    ∫⁻ x in range (fun t ↦ pt t m), weight x ∂μHE[1] = ENNReal.ofReal ((2 : ℝ) ^ (-|(m : ℝ)|)) := by
  rw [← (isometry_pt m).map_euclideanHausdorffMeasure,
    lintegral_map measurable_weight (isometry_pt m).continuous.measurable,
    show (μHE[1] : Measure ℝ) = volume by
      simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)]
  simp only [weight, pt_apply_zero, pt_apply_one]
  rw [lintegral_mul_const (f := (Icc (0 : ℝ) 1).indicator 1)
      _ (measurable_const.indicator measurableSet_Icc),
    lintegral_indicator_one measurableSet_Icc, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
    one_mul]

/-- **The left side is `3`.** `∫_M J g dH¹ = Σ_{m ∈ ℤ} 2^{-|m|} = 3`. -/
theorem lintegral_integerLines :
    ∫⁻ x in integerLines, ENNReal.ofReal (tangentialJacobian 1 integerLines firstCoord x) *
      weight x ∂μHE[1] = 3 := by
  rw [setLIntegral_congr_fun measurableSet_integerLines fun x hx ↦ by
    rw [tangentialJacobian_integerLines hx, ENNReal.ofReal_one, one_mul]]
  rw [integerLines_eq_iUnion, lintegral_iUnion (fun m : ℤ ↦ measurableSet_range_pt (m : ℝ))]
  · simp_rw [lintegral_range_pt]
    exact tsum_two_rpow_neg_abs
  · intro m m' hmm'
    rw [Function.onFun, range_pt, range_pt]
    exact disjoint_left.mpr fun x hx hx' ↦ hmm' (by exact_mod_cast hx.symm.trans hx')

/-- The fibre of `f` over `y` in `ℝ × ℤ` is `{(y, m) : m ∈ ℤ}`. -/
theorem integerLines_inter_preimage (y : ℝ) :
    integerLines ∩ firstCoord ⁻¹' {y} = range fun m : ℤ ↦ pt y m := by
  ext x
  simp only [integerLines, firstCoord, mem_inter_iff, mem_ofPred_eq, mem_preimage,
    mem_singleton_iff, mem_range]
  refine ⟨fun ⟨⟨m, hm⟩, hy⟩ ↦ ⟨m, by rw [eq_pt x, hm, hy]⟩, ?_⟩
  rintro ⟨m, rfl⟩
  exact ⟨⟨m, pt_apply_one y m⟩, pt_apply_zero y m⟩

/-- **The fibre sums.** Over `y ∈ [0, 1]` the fibre sum is `Σ_{m ∈ ℤ} 2^{-|m|} = 3`, and it is `0`
elsewhere. -/
theorem tsum_fibre (y : ℝ) :
    ∑' x : ↥(integerLines ∩ firstCoord ⁻¹' {y}), weight x = (Icc (0 : ℝ) 1).indicator 3 y := by
  have hinj : Injective fun m : ℤ ↦ pt y m := fun a b h ↦ by
    simpa using congrArg (· 1) h
  rw [tsum_congr_set_coe weight (integerLines_inter_preimage y), tsum_range weight hinj]
  simp only [weight, pt_apply_zero, pt_apply_one]
  rw [ENNReal.tsum_mul_left, tsum_two_rpow_neg_abs]
  by_cases hy : y ∈ Icc (0 : ℝ) 1 <;> simp [hy]

/-- **The right side is `3`.** `∫_ℝ Σ_{x ∈ M ∩ f⁻¹(y)} g(x) dy = ∫_0^1 3 dy = 3`. -/
theorem lintegral_tsum_fibre :
    ∫⁻ y, ∑' x : ↥(integerLines ∩ firstCoord ⁻¹' {y}), weight x ∂μHE[1] = 3 := by
  simp_rw [tsum_fibre, show (μHE[1] : Measure ℝ) = volume by
    simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)]
  rw [lintegral_indicator measurableSet_Icc]
  simp [Real.volume_Icc]

/-- Every fibre of `f` in `ℝ × ℤ` is infinite. -/
theorem infinite_fibre (y : ℝ) : (integerLines ∩ firstCoord ⁻¹' {y}).Infinite := by
  rw [integerLines_inter_preimage]
  exact infinite_range_of_injective fun a b h ↦ by simpa using congrArg (· 1) h

/-- The weight is positive on the fibres over `[0, 1]`. -/
theorem weight_pos {x : EuclideanSpace ℝ (Fin 2)} (hx : x 0 ∈ Icc (0 : ℝ) 1) : 0 < weight x := by
  simp only [weight, indicator_of_mem hx, Pi.one_apply, one_mul, ENNReal.ofReal_pos]
  positivity

end TauCeti.Examples.IntegerLines
