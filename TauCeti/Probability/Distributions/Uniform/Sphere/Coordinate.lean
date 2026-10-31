/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Uniform.Sphere.Basic
public import TauCeti.Probability.Distributions.Beta.Quantile
import TauCeti.Probability.Distributions.Uniform.Sphere.Dirichlet
import TauCeti.Probability.Distributions.Beta.Square
import TauCeti.Probability.Distributions.Beta.Reflection
import TauCeti.Probability.Distributions.Affine
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Signed coordinates of a uniform sphere point

In dimension `d ≥ 2`, each coordinate `Xᵢ` of a uniform unit vector satisfies
`(Xᵢ + 1) / 2 ∼ Beta ((d - 1) / 2) ((d - 1) / 2)`. The measure identity gives its
cdf and quantile through the incomplete Beta function and its inverse.
The law of any real linear observable is obtained by scaling this centered Beta law by the
norm of its representing vector; this includes the constant-zero observable.

The squared-coordinate law `map_sq_eval_uniformSphereMeasure` determines the signed law
because the uniform sphere law is invariant under the antipodal map. The identification
uses `betaMeasure_map_centered_sq` and
`MeasureTheory.Measure.eq_of_map_sq_eq_of_map_neg_eq_self`.

## References

* K.-T. Fang, S. Kotz, K. W. Ng, *Symmetric Multivariate and Related Distributions*,
  Chapman and Hall, 1990, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped Topology RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [Nontrivial ι]

/-- A coordinate of a uniform sphere point in dimension at least two is a symmetric Beta
variable affinely transported from `(0, 1)` to `(-1, 1)`. -/
theorem map_eval_uniformSphereMeasure (i : ι) :
    (uniformSphereMeasure (EuclideanSpace ℝ ι)).map (fun u ↦ u.val i) =
      (betaMeasure (((Fintype.card ι : ℝ) - 1) / 2)
        (((Fintype.card ι : ℝ) - 1) / 2)).map (fun x ↦ -1 + 2 * x) := by
  let a : ℝ := ((Fintype.card ι : ℝ) - 1) / 2
  have ha : 0 < a := by
    have hcard : 1 < Fintype.card ι := Fintype.one_lt_card
    dsimp [a]
    exact div_pos (sub_pos.mpr (by exact_mod_cast hcard)) two_pos
  let _ := isProbabilityMeasureBeta ha ha
  have hneg : (uniformSphereMeasure (EuclideanSpace ℝ ι)).map (fun u ↦ -u) =
      uniformSphereMeasure (EuclideanSpace ℝ ι) :=
    (LinearIsometryEquiv.neg ℝ).map_uniformSphereMeasure
  apply Measure.eq_of_map_sq_eq_of_map_neg_eq_self
  · rw [Measure.map_map (by fun_prop) (by fun_prop)]
    calc
      _ = ((uniformSphereMeasure (EuclideanSpace ℝ ι)).map (fun u ↦ -u)).map
          (fun u ↦ u.val i) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = _ := by rw [hneg]
  · calc
      _ = ((betaMeasure a a).map (fun x ↦ 1 - x)).map (fun x ↦ -1 + 2 * x) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop),
          Measure.map_map (by fun_prop) (by fun_prop)]
        congr 1
        ext x
        dsimp
        ring
      _ = _ := by rw [betaMeasure_map_one_sub]
  · rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    exact (map_sq_eval_uniformSphereMeasure i).trans (betaMeasure_map_centered_sq ha).symm

/-- Rescaling a sphere coordinate from `(-1, 1)` to `(0, 1)` gives the symmetric Beta law
with shape half the dimension minus one half. -/
@[simp]
theorem map_add_one_div_two_eval_uniformSphereMeasure (i : ι) :
    (uniformSphereMeasure (EuclideanSpace ℝ ι)).map (fun u ↦ (u.val i + 1) / 2) =
      betaMeasure (((Fintype.card ι : ℝ) - 1) / 2) (((Fintype.card ι : ℝ) - 1) / 2) := by
  have h := congrArg (Measure.map (fun x : ℝ ↦ (x + 1) / 2))
    (map_eval_uniformSphereMeasure i)
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  have hinv : (fun x : ℝ ↦ ((-1 + 2 * x) + 1) / 2) = id := by ext x; dsimp; ring
  simpa only [Function.comp_def, hinv, Measure.map_id] using h

/-- The cdf of a sphere coordinate is the symmetric incomplete Beta cdf evaluated at
`(x + 1) / 2`, including its zero and one extensions outside `[-1, 1]`. -/
theorem cdf_map_eval_uniformSphereMeasure (i : ι) (x : ℝ) :
    cdf ((uniformSphereMeasure (EuclideanSpace ℝ ι)).map (fun u ↦ u.val i)) x =
      regularizedIncompleteBeta (((Fintype.card ι : ℝ) - 1) / 2)
        (((Fintype.card ι : ℝ) - 1) / 2) ((x + 1) / 2) := by
  have ha : 0 < ((Fintype.card ι : ℝ) - 1) / 2 :=
    div_pos (sub_pos.mpr (by exact_mod_cast Fintype.one_lt_card (α := ι))) two_pos
  let _ := isProbabilityMeasureBeta ha ha
  rw [map_eval_uniformSphereMeasure, cdf_map_affine_of_pos (by norm_num),
    cdf_betaMeasure_eq ha ha, sub_neg_eq_add]

/-- At an interior probability level the quantile of a sphere coordinate is an affine
inverse-Beta quantile. -/
theorem quantile_map_eval_uniformSphereMeasure (i : ι) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((uniformSphereMeasure (EuclideanSpace ℝ ι)).map (fun x ↦ x.val i)).quantile u =
      -1 + 2 * inverseRegularizedIncompleteBeta (((Fintype.card ι : ℝ) - 1) / 2)
        (((Fintype.card ι : ℝ) - 1) / 2) u := by
  have ha : 0 < ((Fintype.card ι : ℝ) - 1) / 2 :=
    div_pos (sub_pos.mpr (by exact_mod_cast Fintype.one_lt_card (α := ι))) two_pos
  let _ := isProbabilityMeasureBeta ha ha
  rw [map_eval_uniformSphereMeasure, quantile_map_affine_pos (by norm_num) hu.1 hu.2,
    quantile_betaMeasure ha ha hu]

/-- Sphere-coordinate quantiles tend to the lower support endpoint `-1`. -/
theorem tendsto_quantile_map_eval_uniformSphereMeasure_nhdsGT_zero (i : ι) :
    Tendsto ((uniformSphereMeasure (EuclideanSpace ℝ ι)).map (fun x ↦ x.val i)).quantile
      (𝓝[>] 0) (𝓝 (-1)) := by
  have ha : 0 < ((Fintype.card ι : ℝ) - 1) / 2 :=
    div_pos (sub_pos.mpr (by exact_mod_cast Fintype.one_lt_card (α := ι))) two_pos
  have h := ((tendsto_inverseRegularizedIncompleteBeta_zero ha ha).const_mul 2).const_add (-1)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact (quantile_map_eval_uniformSphereMeasure i hu).symm

/-- Sphere-coordinate quantiles tend to the upper support endpoint `1`. -/
theorem tendsto_quantile_map_eval_uniformSphereMeasure_nhdsLT_one (i : ι) :
    Tendsto ((uniformSphereMeasure (EuclideanSpace ℝ ι)).map (fun x ↦ x.val i)).quantile
      (𝓝[<] 1) (𝓝 1) := by
  have ha : 0 < ((Fintype.card ι : ℝ) - 1) / 2 :=
    div_pos (sub_pos.mpr (by exact_mod_cast Fintype.one_lt_card (α := ι))) two_pos
  have h := ((tendsto_inverseRegularizedIncompleteBeta_one ha ha).const_mul 2).const_add (-1)
  norm_num only [mul_one, neg_add_cancel_left] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_map_eval_uniformSphereMeasure i hu).symm

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every real linear observable of a uniform sphere point in dimension at least two
is a scaled symmetric Beta variable. The formula includes the zero observable. -/
theorem map_inner_uniformSphereMeasure (hd : 2 ≤ Module.finrank ℝ E) (v : E) :
    (uniformSphereMeasure E).map (fun u : sphere (0 : E) 1 ↦ ⟪v, (u : E)⟫) =
      (betaMeasure (((Module.finrank ℝ E : ℝ) - 1) / 2)
        (((Module.finrank ℝ E : ℝ) - 1) / 2)).map (fun x ↦ ‖v‖ * (-1 + 2 * x)) := by
  let d := Module.finrank ℝ E
  let i : Fin d := ⟨0, lt_of_lt_of_le (by norm_num) hd⟩
  have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  let g := (stdOrthonormalBasis ℝ E).repr
  let w : EuclideanSpace ℝ (Fin d) := ‖v‖ • EuclideanSpace.single i 1
  have hnorm : ‖g v‖ = ‖w‖ := by simp [w, g, norm_smul]
  let f := g.trans (Submodule.reflection (ℝ ∙ (g v - w))ᗮ)
  let fs : sphere (0 : E) 1 → sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    Subtype.map f (fun x hx ↦ by simpa using hx)
  have hfs : Measurable fs := f.continuous.measurable.subtype_map _
  have hmap : (uniformSphereMeasure E).map fs =
      uniformSphereMeasure (EuclideanSpace ℝ (Fin d)) := f.map_uniformSphereMeasure
  have hfv : f v = w := Submodule.reflection_sub hnorm
  have hcoord (x : E) : ⟪v, x⟫ = ‖v‖ * (f x) i := by
    rw [← f.inner_map_map, hfv]
    simp [w, real_inner_smul_left, EuclideanSpace.inner_single_left]
  calc
    _ = (((uniformSphereMeasure E).map fs).map
        (fun u ↦ u.val i)).map (fun x ↦ ‖v‖ * x) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) hfs]
      congr 1
      ext x
      exact hcoord x
    _ = _ := by
      rw [hmap, map_eval_uniformSphereMeasure,
        Measure.map_map (by fun_prop) (by fun_prop)]
      simp only [Fintype.card_fin, Function.comp_def, d]

/-- Quantiles of any real linear observable of a uniform sphere point scale with the
norm of its representing vector, including the zero observable. -/
theorem quantile_map_inner_uniformSphereMeasure (hd : 2 ≤ Module.finrank ℝ E) (v : E)
    {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((uniformSphereMeasure E).map (fun x : sphere (0 : E) 1 ↦ ⟪v, (x : E)⟫)).quantile u =
      ‖v‖ * (-1 + 2 * inverseRegularizedIncompleteBeta
        (((Module.finrank ℝ E : ℝ) - 1) / 2) (((Module.finrank ℝ E : ℝ) - 1) / 2) u) := by
  have ha : 0 < ((Module.finrank ℝ E : ℝ) - 1) / 2 :=
    div_pos (sub_pos.mpr (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hd))) two_pos
  let _ := isProbabilityMeasureBeta ha ha
  rw [map_inner_uniformSphereMeasure hd v]
  by_cases hv : ‖v‖ = 0
  · simp [hv, Measure.map_const, Measure.quantile_dirac _ hu.1 hu.2.le]
  · have hfun : (fun x : ℝ ↦ ‖v‖ * (-1 + 2 * x)) =
        fun x ↦ -‖v‖ + (2 * ‖v‖) * x := by ext x; ring
    have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    rw [hfun, quantile_map_affine_pos (mul_pos two_pos hvpos) hu.1 hu.2,
      quantile_betaMeasure ha ha hu]
    ring

end Projection

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {ι Ω : Type*} [Fintype ι] [Nontrivial ι] [MeasurableSpace Ω]
  {P : Measure Ω} {U : Ω → sphere (0 : EuclideanSpace ℝ ι) 1}

/-- A rescaled coordinate of a uniform random unit vector is a symmetric Beta variable. -/
theorem HasLaw.add_one_div_two_eval_uniformSphereMeasure
    (hU : HasLaw U (uniformSphereMeasure (EuclideanSpace ℝ ι)) P) (i : ι) :
    HasLaw (fun ω ↦ ((U ω).val i + 1) / 2)
      (betaMeasure (((Fintype.card ι : ℝ) - 1) / 2)
        (((Fintype.card ι : ℝ) - 1) / 2)) P :=
  (HasLaw.mk (by fun_prop) (map_add_one_div_two_eval_uniformSphereMeasure i)).fun_comp hU

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {V : Ω → sphere (0 : E) 1}

/-- A real linear observable of a uniform random unit vector is a scaled symmetric Beta
variable. -/
theorem HasLaw.inner_uniformSphereMeasure (hV : HasLaw V (uniformSphereMeasure E) P)
    (hd : 2 ≤ Module.finrank ℝ E) (v : E) :
    HasLaw (fun ω ↦ ⟪v, (V ω : E)⟫)
      ((betaMeasure (((Module.finrank ℝ E : ℝ) - 1) / 2)
        (((Module.finrank ℝ E : ℝ) - 1) / 2)).map (fun x ↦ ‖v‖ * (-1 + 2 * x))) P :=
  (HasLaw.mk (by fun_prop) (map_inner_uniformSphereMeasure hd v)).fun_comp hV

end ProbabilityTheory
