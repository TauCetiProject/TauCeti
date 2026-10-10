/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Basic
public import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Exact Gromov–Wasserstein distance between uniform two-point spaces

For nonnegative off-diagonal distances `a` and `b`, the uniform two-point kernels have
Gromov–Wasserstein distance `2 ^ (-1 / p) * |a - b|`. The matching coupling is optimal.
The exponent `p = ∞` is included: its factor is one. Positive `a` and `b` are the ordinary
two-point metric spaces; allowing zero also covers the one-point degenerations.

The upper bound evaluates the matching coupling. The lower bound uses the triangle inequality
through the zero one-point kernel and the already established one-point distance formula.
Thus these calculations certify objectives and optimal couplings for the generic GW API.

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*,
  J. Mach. Learn. Res. 26 (2025), for distortion and the size lower bound.

All distances use the convention without a factor of `1 / 2`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- The scalar distance kernel of two labelled points with off-diagonal distance `a`.
For `a > 0` this is the distance matrix of a two-point metric space. -/
def twoPointKernel (a : ℝ) (q : Fin 2 × Fin 2) : ℝ :=
  if q.1 = q.2 then 0 else a

/-- The defining formula for the two-point distance matrix. -/
@[simp]
theorem twoPointKernel_apply (a : ℝ) (i j : Fin 2) :
    twoPointKernel a (i, j) = if i = j then 0 else a := by rfl

private theorem uniformTwoPoint_prod_offDiagonal :
    ((PMF.uniformOfFintype (Fin 2)).toMeasure.prod
      (PMF.uniformOfFintype (Fin 2)).toMeasure) {q | q.1 ≠ q.2} = (2 : ℝ≥0∞)⁻¹ := by
  have h : {q : Fin 2 × Fin 2 | q.1 ≠ q.2} = {(0, 1), (1, 0)} := by
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp
  rw [h, ← singleton_union, measure_union (by simp) (measurableSet_singleton _)]
  simp only [← singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_fin, Nat.cast_ofNat]
  rw [← mul_two, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

/-- The discrepancy of two matching uniform two-point kernels has an explicit `Lᵖ` norm.
The formula includes `p = ∞`, since `∞.toReal = 0`. -/
theorem eLpNorm_twoPointKernel_edist (a b : ℝ) {p : ℝ≥0∞} (hp : p ≠ 0) :
    eLpNorm (fun q ↦ edist (twoPointKernel a q) (twoPointKernel b q)) p
      ((PMF.uniformOfFintype (Fin 2)).toMeasure.prod
        (PMF.uniformOfFintype (Fin 2)).toMeasure) =
      (2 : ℝ≥0∞) ^ (-1 / p.toReal) * ENNReal.ofReal |a - b| := by
  have h : (fun q ↦ edist (twoPointKernel a q) (twoPointKernel b q)) =
      {q : Fin 2 × Fin 2 | q.1 ≠ q.2}.indicator (fun _ ↦ edist a b) := by
    funext q
    by_cases hq : q.1 = q.2 <;> simp [twoPointKernel, hq]
  rw [h, eLpNorm_indicator_const' (Set.toFinite _).measurableSet.nullMeasurableSet
    (by rw [uniformTwoPoint_prod_offDiagonal]; norm_num) hp,
    enorm_eq_self, uniformTwoPoint_prod_offDiagonal, ENNReal.inv_rpow,
    ← ENNReal.rpow_neg]
  simp [edist_dist, Real.dist_eq, neg_div, mul_comm]

/-- The matching coupling of the two labelled points has the predicted distortion. -/
theorem gromovWassersteinDistortion_twoPoint_diagonal (a b : ℝ) {p : ℝ≥0∞}
    (hp : p ≠ 0) :
    gromovWassersteinDistortion p (twoPointKernel a) (twoPointKernel b)
      (PMF.uniformOfFintype (Fin 2)).toMeasure.diagonalCoupling =
      (2 : ℝ≥0∞) ^ (-1 / p.toReal) * ENNReal.ofReal |a - b| := by
  rw [← (PMF.uniformOfFintype (Fin 2)).toMeasure.measurePreserving_diagonal.map_eq]
  exact (gromovWassersteinDistortion_map_prodMk
    (MeasurePreserving.id (PMF.uniformOfFintype (Fin 2)).toMeasure)
    (MeasurePreserving.id (PMF.uniformOfFintype (Fin 2)).toMeasure)
    (measurable_of_countable (twoPointKernel a)).aestronglyMeasurable
    (measurable_of_countable (twoPointKernel b)).aestronglyMeasurable p).trans
      (eLpNorm_twoPointKernel_edist a b hp)

private theorem gromovWassersteinEDist_twoPoint_dirac (a : ℝ) {p : ℝ≥0∞} (hp : p ≠ 0) :
    gromovWassersteinEDist p (PMF.uniformOfFintype (Fin 2)).toMeasure (twoPointKernel a)
      (Measure.dirac ()) (fun _ : Unit × Unit ↦ (0 : ℝ)) =
      (2 : ℝ≥0∞) ^ (-1 / p.toReal) * ENNReal.ofReal |a| := by
  rw [gromovWassersteinEDist_dirac_right () _ (measurable_of_countable _).aestronglyMeasurable]
  simpa [twoPointKernel] using eLpNorm_twoPointKernel_edist a 0 hp

/-- The exact GW distance between uniform two-point kernels, including the infinite exponent.
The nonnegative distances may vanish; positive ones give genuine two-point metric spaces. -/
theorem gromovWassersteinEDist_twoPoint {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    gromovWassersteinEDist p (PMF.uniformOfFintype (Fin 2)).toMeasure (twoPointKernel a)
      (PMF.uniformOfFintype (Fin 2)).toMeasure (twoPointKernel b) =
      (2 : ℝ≥0∞) ^ (-1 / p.toReal) * ENNReal.ofReal |a - b| := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  refine le_antisymm ((gromovWassersteinEDist_le
    (PMF.uniformOfFintype (Fin 2)).toMeasure.isCoupling_diagonalCoupling p _ _).trans_eq
      (gromovWassersteinDistortion_twoPoint_diagonal a b hp0)) ?_
  have lower (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      (2 : ℝ≥0∞) ^ (-1 / p.toReal) * ENNReal.ofReal (a - b) ≤
        gromovWassersteinEDist p (PMF.uniformOfFintype (Fin 2)).toMeasure (twoPointKernel a)
          (PMF.uniformOfFintype (Fin 2)).toMeasure (twoPointKernel b) := by
    rw [ENNReal.ofReal_sub _ hb, ENNReal.mul_sub (by intros; finiteness), tsub_le_iff_right]
    have h := gromovWassersteinEDist_triangle (μ := (PMF.uniformOfFintype (Fin 2)).toMeasure)
      (ν := (PMF.uniformOfFintype (Fin 2)).toMeasure) (ρ := Measure.dirac ())
      (ωX := twoPointKernel a) (ωY := twoPointKernel b) (ωW := fun _ ↦ (0 : ℝ)) hp
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aestronglyMeasurable aestronglyMeasurable_const
    simpa [gromovWassersteinEDist_twoPoint_dirac _ hp0, abs_of_nonneg ha, abs_of_nonneg hb]
      using h
  rcases le_total b a with h | h
  · simpa [abs_of_nonneg (sub_nonneg.mpr h)] using lower a b ha hb
  · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub, gromovWassersteinEDist_comm]
    exact lower b a hb ha

/-- At infinity the exact uniform two-point GW distance is the difference of the distances. -/
theorem gromovWassersteinEDist_twoPoint_top {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    gromovWassersteinEDist ∞ (PMF.uniformOfFintype (Fin 2)).toMeasure (twoPointKernel a)
      (PMF.uniformOfFintype (Fin 2)).toMeasure (twoPointKernel b) =
      ENNReal.ofReal |a - b| := by
  simpa using gromovWassersteinEDist_twoPoint ha hb (p := ∞) le_top

/-- The matching coupling attains the infimum defining the uniform two-point GW distance. -/
theorem gromovWassersteinDistortion_twoPoint_diagonal_eq_edist {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    gromovWassersteinDistortion p (twoPointKernel a) (twoPointKernel b)
      (PMF.uniformOfFintype (Fin 2)).toMeasure.diagonalCoupling =
      gromovWassersteinEDist p (PMF.uniformOfFintype (Fin 2)).toMeasure (twoPointKernel a)
        (PMF.uniformOfFintype (Fin 2)).toMeasure (twoPointKernel b) := by
  rw [gromovWassersteinDistortion_twoPoint_diagonal _ _ (ne_of_gt (zero_lt_one.trans_le hp)),
    gromovWassersteinEDist_twoPoint ha hb hp]

/-- The distance kernel of any pair of points is its two-point distance matrix. -/
theorem twoPointKernel_dist {X : Type*} [PseudoMetricSpace X] (x : Fin 2 → X) :
    twoPointKernel (dist (x 0) (x 1)) = fun q ↦ dist (x q.1) (x q.2) := by
  funext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [twoPointKernel, dist_comm]

/-- Exact GW distance between two labelled pairs in arbitrary metric spaces, with uniform laws
on their labels. Distinct points give genuine two-point metric spaces. -/
theorem gromovWassersteinEDist_dist_fin_two {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (x : Fin 2 → X) (y : Fin 2 → Y)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    gromovWassersteinEDist p (PMF.uniformOfFintype (Fin 2)).toMeasure
      (fun q ↦ dist (x q.1) (x q.2)) (PMF.uniformOfFintype (Fin 2)).toMeasure
      (fun q ↦ dist (y q.1) (y q.2)) =
      (2 : ℝ≥0∞) ^ (-1 / p.toReal) * ENNReal.ofReal |dist (x 0) (x 1) - dist (y 0) (y 1)| := by
  rw [← twoPointKernel_dist x, ← twoPointKernel_dist y]
  exact gromovWassersteinEDist_twoPoint dist_nonneg dist_nonneg hp

end TauCeti
