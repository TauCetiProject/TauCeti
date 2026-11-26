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
import TauCeti.Topology.Algebra.InfiniteSum.Real

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
  (`tsum_fiber`), so the right side is `3` (`lintegral_tsum_fiber`).

The fibres are infinite, and over `[0, 1]` the weight is positive on all of their points
(`infinite_fiber`, `weight_pos`): a fibre sum set to `∞` whenever infinitely many terms are
positive would make the right side `∞`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §12 (the area formula on rectifiable sets).
-/

open MeasureTheory Measure Set Metric Module Filter Topology Function
open scoped ENNReal NNReal

public noncomputable section

namespace TauCeti.Examples.IntegerLines

open TauCeti

/-- Each horizontal line `t ↦ (t, s)` is an isometric embedding of `ℝ`. -/
private theorem isometry_line (s : ℝ) : Isometry fun t : ℝ ↦ !₂[t, s] :=
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
theorem integerLines_eq_iUnion : integerLines = ⋃ m : ℤ, range fun t : ℝ ↦ !₂[t, (m : ℝ)] := by
  ext x
  simp only [integerLines, mem_ofPred_eq, mem_iUnion, mem_range]
  refine ⟨fun ⟨m, hm⟩ ↦ ⟨m, x 0, ?_⟩, ?_⟩
  · ext i
    fin_cases i <;> simp [hm]
  · rintro ⟨m, t, rfl⟩
    exact ⟨m, by simp⟩

/-- The line `t ↦ (t, s)` is the set of points with second coordinate `s`. -/
private theorem range_line (s : ℝ) : (range fun t : ℝ ↦ !₂[t, s]) = {x | x 1 = s} := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨x 0, ?_⟩⟩
  · rintro ⟨t, rfl⟩
    simp
  · rw [mem_ofPred_eq] at hx
    ext i
    fin_cases i <;> simp [hx]

/-- Each horizontal line is measurable. -/
private theorem measurableSet_range_line (s : ℝ) : MeasurableSet (range fun t : ℝ ↦ !₂[t, s]) := by
  rw [range_line]
  exact measurableSet_eq_fun (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).measurable
    measurable_const

/-- `ℝ × ℤ` is measurable. -/
theorem measurableSet_integerLines : MeasurableSet integerLines := by
  rw [integerLines_eq_iUnion]
  exact MeasurableSet.iUnion fun m ↦ measurableSet_range_line m

/-- Two points of `ℝ²` whose second coordinates are distinct integers are at distance at
least `1`. -/
private theorem one_le_dist_of_ne {x y : EuclideanSpace ℝ (Fin 2)} {m m' : ℤ} (hx : x 1 = m)
    (hy : y 1 = m') (hmm' : m ≠ m') : 1 ≤ dist x y := by
  have h1 : (1 : ℝ) ≤ |(m : ℝ) - m'| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmm')
  calc (1 : ℝ) ≤ |x 1 - y 1| := by rwa [hx, hy]
    _ = ‖(x - y) 1‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖x - y‖ := PiLp.norm_apply_le _ _
    _ = dist x y := (dist_eq_norm x y).symm

/-- Within distance `r < 1` of a point of the line at height `m`, `ℝ × ℤ` is that line. -/
private theorem diff_image_inter_closedBall_eq_empty (m : ℤ) (t : ℝ) {r : ℝ} (hr : r < 1) :
    (integerLines \ (fun t : ℝ ↦ !₂[t, (m : ℝ)]) '' univ) ∩ closedBall !₂[t, (m : ℝ)] r = ∅ := by
  refine eq_empty_of_forall_notMem fun z ⟨⟨⟨m', hm'⟩, hz⟩, hzr⟩ ↦ ?_
  have hne : m' ≠ m := by
    rintro rfl
    refine hz ⟨z 0, mem_univ _, ?_⟩
    ext i
    fin_cases i <;> simp [hm']
  exact (one_le_dist_of_ne hm' (by simp) hne).not_gt ((mem_closedBall.mp hzr).trans_lt hr)

/-- **The tangential Jacobian is `1`.** At every point of `ℝ × ℤ` the tangential Jacobian of the
first coordinate along `ℝ × ℤ` is `1`. -/
theorem tangentialJacobian_integerLines {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ integerLines) :
    tangentialJacobian 1 integerLines firstCoord x = 1 := by
  -- On the chart `t ↦ (t, m)`, both the chart and `f` composed with it have norm determinant `1`.
  obtain ⟨m, hm⟩ := hx
  set e₀ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  let A : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) := (ContinuousLinearMap.id ℝ ℝ).smulRight e₀
  have hA (t : ℝ) : A t = t • e₀ := by simp [A]
  have hline : (fun t : ℝ ↦ !₂[t, (m : ℝ)]) = fun t ↦ t • e₀ + !₂[0, (m : ℝ)] := by
    funext t
    ext i
    fin_cases i <;> simp [e₀]
  have hf : HasFDerivWithinAt (fun t : ℝ ↦ !₂[t, (m : ℝ)]) A univ (x 0) := by
    have h : HasFDerivAt (fun t : ℝ ↦ t • e₀) A (x 0) := by
      simpa using (hasFDerivAt_id (𝕜 := ℝ) (x 0)).smul_const e₀
    rw [hline]
    exact (h.add_const _).hasFDerivWithinAt
  have hinj : Injective A := fun a b h ↦ by simpa [hA, e₀] using congrArg (· 0) h
  have hi : AntilipschitzWith 1 (univ.domRestrict fun t : ℝ ↦ !₂[t, (m : ℝ)]) :=
    ((isometry_line m).comp isometry_subtypeVal).antilipschitzWith
  have hsub : (fun t : ℝ ↦ !₂[t, (m : ℝ)]) '' univ ⊆ integerLines := by
    rintro _ ⟨t, -, rfl⟩
    exact ⟨m, by simp⟩
  have hdens : Tendsto (fun r ↦ volume (univ ∩ closedBall (x 0) r) /
      volume (closedBall (0 : ℝ) r)) (𝓝[>] 0) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [univ_inter, Real.volume_closedBall, Real.volume_closedBall,
      ENNReal.div_self (by simpa using hr) ENNReal.ofReal_ne_top]
  have hdiff : Tendsto (fun r ↦ μHE[finrank ℝ ℝ]
      ((integerLines \ (fun t : ℝ ↦ !₂[t, (m : ℝ)]) '' univ) ∩ closedBall !₂[x 0, (m : ℝ)] r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ ℝ))) r)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with r ⟨_, hr⟩
    rw [eq_comm, ENNReal.div_eq_zero_iff]
    left
    rw [diff_image_inter_closedBall_eq_empty m (x 0) hr, measure_empty]
  have hgf : HasFDerivWithinAt (firstCoord ∘ fun t : ℝ ↦ !₂[t, (m : ℝ)])
      (ContinuousLinearMap.id ℝ ℝ) univ (x 0) := by
    have : (firstCoord ∘ fun t : ℝ ↦ !₂[t, (m : ℝ)]) = id := funext fun t ↦ by simp [firstCoord]
    rw [this]
    exact HasFDerivAt.hasFDerivWithinAt (hasFDerivAt_id _)
  have h := hf.tangentialJacobian_mul_normDet hinj hi (mem_univ _) hsub hdens hdiff hgf
  have hnA : A.toLinearMap.normDet = 1 := by
    rw [LinearMap.normDet_eq_norm_apply_one]
    simp [hA, e₀]
  have hx : !₂[x 0, (m : ℝ)] = x := by
    ext i
    fin_cases i <;> simp [hm]
  simpa [hnA, hx] using h

/-- `Σ_{m ∈ ℤ} 2^{-|m|} = 3`. -/
private theorem tsum_two_rpow_neg_abs : ∑' m : ℤ, ENNReal.ofReal ((2 : ℝ) ^ (-|(m : ℝ)|)) = 3 := by
  have h (m : ℤ) : (2 : ℝ) ^ (-|(m : ℝ)|) = 2⁻¹ ^ m.natAbs := by
    rw [← Int.cast_abs, ← Nat.cast_natAbs, Real.rpow_neg zero_le_two,
      Real.rpow_natCast, inv_pow]
  simp_rw [h]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity)
    (summable_pow_natAbs (by norm_num) (by norm_num)), tsum_pow_natAbs (by norm_num) (by norm_num)]
  norm_num

/-- On `ℝ`, the constant `c` on `[0, 1]` integrates to `c` against `H¹`. -/
private theorem lintegral_indicator_Icc (c : ℝ≥0∞) :
    ∫⁻ t, (Icc (0 : ℝ) 1).indicator (fun _ ↦ c) t ∂μHE[1] = c := by
  rw [show (μHE[1] : Measure ℝ) = volume by
      simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ),
    lintegral_indicator measurableSet_Icc]
  simp [Real.volume_Icc]

/-- The weight integrates to `2^{-|m|}` over the line at height `m`. -/
private theorem lintegral_range_line (m : ℤ) :
    ∫⁻ x in range (fun t : ℝ ↦ !₂[t, (m : ℝ)]), weight x ∂μHE[1] =
      ENNReal.ofReal ((2 : ℝ) ^ (-|(m : ℝ)|)) := by
  rw [← (isometry_line m).map_euclideanHausdorffMeasure,
    lintegral_map measurable_weight (isometry_line m).continuous.measurable]
  simpa [weight, ← indicator_mul_const] using lintegral_indicator_Icc _

/-- **The left side is `3`.** `∫_M J g dH¹ = Σ_{m ∈ ℤ} 2^{-|m|} = 3`. -/
theorem lintegral_integerLines :
    ∫⁻ x in integerLines, ENNReal.ofReal (tangentialJacobian 1 integerLines firstCoord x) *
      weight x ∂μHE[1] = 3 := by
  rw [setLIntegral_congr_fun measurableSet_integerLines fun x hx ↦ by
    rw [tangentialJacobian_integerLines hx, ENNReal.ofReal_one, one_mul]]
  rw [integerLines_eq_iUnion, lintegral_iUnion (fun m : ℤ ↦ measurableSet_range_line (m : ℝ))]
  · simp_rw [lintegral_range_line]
    exact tsum_two_rpow_neg_abs
  · intro m m' hmm'
    rw [Function.onFun, range_line, range_line]
    exact disjoint_left.mpr fun x hx hx' ↦ hmm' (by exact_mod_cast hx.symm.trans hx')

/-- The points `(y, m)`, `m ∈ ℤ`, are pairwise distinct. -/
private theorem injective_line_int (y : ℝ) : Injective fun m : ℤ ↦ !₂[y, (m : ℝ)] :=
  fun a b h ↦ by simpa using congrArg (· 1) h

/-- The fibre of `f` over `y` in `ℝ × ℤ` is `{(y, m) : m ∈ ℤ}`. -/
theorem integerLines_inter_preimage (y : ℝ) :
    integerLines ∩ firstCoord ⁻¹' {y} = range fun m : ℤ ↦ !₂[y, (m : ℝ)] := by
  ext x
  simp only [integerLines, firstCoord, mem_inter_iff, mem_ofPred_eq, mem_preimage,
    mem_singleton_iff, mem_range]
  refine ⟨fun ⟨⟨m, hm⟩, hy⟩ ↦ ⟨m, ?_⟩, ?_⟩
  · ext i
    fin_cases i <;> simp [hm, hy]
  · rintro ⟨m, rfl⟩
    exact ⟨⟨m, by simp⟩, by simp⟩

/-- **The fibre sums.** Over `y ∈ [0, 1]` the fibre sum is `Σ_{m ∈ ℤ} 2^{-|m|} = 3`, and it is `0`
elsewhere. -/
theorem tsum_fiber (y : ℝ) :
    ∑' x : ↥(integerLines ∩ firstCoord ⁻¹' {y}), weight x = (Icc (0 : ℝ) 1).indicator 3 y := by
  rw [tsum_congr_set_coe weight (integerLines_inter_preimage y),
    tsum_range weight (injective_line_int y)]
  simp only [weight, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ENNReal.tsum_mul_left, tsum_two_rpow_neg_abs]
  by_cases hy : y ∈ Icc (0 : ℝ) 1 <;> simp [hy]

/-- **The right side is `3`.** `∫_ℝ Σ_{x ∈ M ∩ f⁻¹(y)} g(x) dy = ∫_0^1 3 dy = 3`. -/
theorem lintegral_tsum_fiber :
    ∫⁻ y, ∑' x : ↥(integerLines ∩ firstCoord ⁻¹' {y}), weight x ∂μHE[1] = 3 := by
  simp_rw [tsum_fiber]
  exact lintegral_indicator_Icc 3

/-- Every fibre of `f` in `ℝ × ℤ` is infinite. -/
theorem infinite_fiber (y : ℝ) : (integerLines ∩ firstCoord ⁻¹' {y}).Infinite := by
  rw [integerLines_inter_preimage]
  exact infinite_range_of_injective (injective_line_int y)

/-- The weight is positive on the fibres over `[0, 1]`. -/
theorem weight_pos {x : EuclideanSpace ℝ (Fin 2)} (hx : x 0 ∈ Icc (0 : ℝ) 1) : 0 < weight x := by
  simp only [weight, indicator_of_mem hx, Pi.one_apply, one_mul, ENNReal.ofReal_pos]
  positivity

end TauCeti.Examples.IntegerLines
