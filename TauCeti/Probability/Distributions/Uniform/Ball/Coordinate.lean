/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Uniform.Ball.Basic
public import TauCeti.Probability.Distributions.Beta.Quantile
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.Uniform.Sphere.Dirichlet
import TauCeti.Probability.Distributions.Beta.Product
import TauCeti.Probability.Distributions.Beta.Square
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates

/-!
# Coordinates and projections of a uniform ball point

In dimension `d ≥ 1`, a coordinate `Xᵢ` of a uniform point of the centered unit ball satisfies
`(Xᵢ + 1) / 2 ∼ Beta ((d + 1) / 2) ((d + 1) / 2)`. Real linear observables of any uniform ball
law are affine images of this symmetric Beta law. For nonconstant projections of positive-radius
balls, their cdfs follow from the incomplete Beta function. Quantiles follow from its inverse,
including constant observables and balls of radius zero.

The squared coordinate is the product of the independent squared radius and squared sphere
coordinate. The Beta product identity identifies its law; antipodal symmetry then determines
the signed coordinate. The one-dimensional case uses that the squared coordinate is the
squared radius.

The proof reuses `map_sphereDirection_prod_uniformBallMeasure`, `map_mul_prod_betaMeasure`, and
`MeasureTheory.Measure.eq_of_map_sq_eq_of_map_neg_eq_self`. The projection argument uses an
orthonormal coordinate system and Mathlib's `Submodule.reflection_sub`.

## References

* K.-T. Fang, S. Kotz, K. W. Ng, *Symmetric Multivariate and Related Distributions*,
  Chapman and Hall, 1990, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped Topology RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- The square of a coordinate of a uniform point in the unit ball has Beta law with
shapes `1 / 2` and `(d + 1) / 2`, including dimension one. -/
@[simp]
theorem map_sq_eval_uniformBallMeasure (i : ι) :
    (uniformBallMeasure (0 : EuclideanSpace ℝ ι) 1).map (fun x ↦ x i ^ 2) =
      betaMeasure (1 / 2) (((Fintype.card ι : ℝ) + 1) / 2) := by
  classical
  have : Nonempty ι := ⟨i⟩
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := by simp
  have := isProbabilityMeasureBeta
    (Nat.cast_pos.2 (Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℝ ι))) one_pos
  have hrad := map_sq_norm_sub_div_uniformBallMeasure (0 : EuclideanSpace ℝ ι)
    (by norm_num : (0 : ℝ) < 1)
  simp only [sub_zero, div_one, hdim] at hrad
  rcases subsingleton_or_nontrivial ι with hι | hι
  -- In dimension one the coordinate square equals the squared radius.
  · let : Unique ι := { default := i, uniq := fun j ↦ Subsingleton.elim j i }
    have hnorm (x : EuclideanSpace ℝ ι) : ‖x‖ ^ 2 = x i ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_subsingleton _ i]
    simpa [hnorm] using hrad
  · let e : sphere (0 : EuclideanSpace ℝ ι) 1 := ⟨EuclideanSpace.single i 1, by simp⟩
    -- Square both components of the independent direction-radius pair.
    have hjoint := congrArg (Measure.map
      (Prod.map (fun u : sphere (0 : EuclideanSpace ℝ ι) 1 ↦ u.val i ^ 2)
        (fun r : ℝ ↦ r ^ 2)))
      (map_sphereDirection_prod_uniformBallMeasure e 0 (by norm_num : (0 : ℝ) < 1))
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      map_sq_eval_uniformSphereMeasure,
      ← map_norm_sub_div_uniformBallMeasure (0 : EuclideanSpace ℝ ι)
        (by norm_num : (0 : ℝ) < 1),
      Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)] at hjoint
    simp only [Function.comp_def, Prod.map_apply, sub_zero, div_one] at hjoint
    rw [hrad] at hjoint
    have hb : 0 < ((Fintype.card ι : ℝ) - 1) / 2 := by
      have hcard : 1 < Fintype.card ι := Fintype.one_lt_card
      exact div_pos (sub_pos.mpr (by exact_mod_cast hcard)) two_pos
    calc
      _ = ((uniformBallMeasure (0 : EuclideanSpace ℝ ι) 1).map
          (fun x ↦ ((sphereDirection e x).val i ^ 2, ‖x‖ ^ 2))).map
            (fun z ↦ z.1 * z.2) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        congr 1
        ext x
        -- Reconstruct the coordinate from its radius and direction, also at the origin.
        have hx := congrArg (fun y : EuclideanSpace ℝ ι ↦ y i)
          (norm_smul_sphereDirection e x)
        simp only [PiLp.smul_apply, smul_eq_mul] at hx
        simp only [Function.comp_apply]
        rw [← hx]
        ring
      _ = _ := by
        rw [hjoint]
        have hshape : (Fintype.card ι : ℝ) / 2 = 1 / 2 + ((Fintype.card ι : ℝ) - 1) / 2 := by ring
        rw [hshape, map_mul_prod_betaMeasure (by norm_num) hb one_pos]
        congr 1
        ring

/-- A coordinate of a uniform unit-ball point is a symmetric Beta variable affinely
transported from `(0, 1)` to `(-1, 1)`. -/
theorem map_eval_uniformBallMeasure (i : ι) :
    (uniformBallMeasure (0 : EuclideanSpace ℝ ι) 1).map (fun x ↦ x i) =
      (betaMeasure (((Fintype.card ι : ℝ) + 1) / 2)
        (((Fintype.card ι : ℝ) + 1) / 2)).map (fun x ↦ -1 + 2 * x) := by
  have ha : 0 < ((Fintype.card ι : ℝ) + 1) / 2 := by positivity
  have := isProbabilityMeasure_uniformBallMeasure (c := (0 : EuclideanSpace ℝ ι))
    (by norm_num : (0 : ℝ) ≤ 1)
  have hneg : (uniformBallMeasure (0 : EuclideanSpace ℝ ι) 1).map (fun x ↦ -x) =
      uniformBallMeasure 0 1 := by
    simp
  apply eq_map_betaMeasure_of_map_sq_of_map_neg ha
  · rw [Measure.map_map (by fun_prop) (by fun_prop)]
    exact map_sq_eval_uniformBallMeasure i
  · rw [Measure.map_map (by fun_prop) (by fun_prop)]
    calc
      _ = ((uniformBallMeasure (0 : EuclideanSpace ℝ ι) 1).map (fun x ↦ -x)).map
          (fun x ↦ x i) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        simp only [Function.comp_def, PiLp.neg_apply]
      _ = _ := by rw [hneg]

/-- Rescaling a unit-ball coordinate to `(0, 1)` gives the symmetric Beta law with
shape `(d + 1) / 2`. -/
@[simp]
theorem map_add_one_div_two_eval_uniformBallMeasure (i : ι) :
    (uniformBallMeasure (0 : EuclideanSpace ℝ ι) 1).map (fun x ↦ (x i + 1) / 2) =
      betaMeasure (((Fintype.card ι : ℝ) + 1) / 2) (((Fintype.card ι : ℝ) + 1) / 2) := by
  have h := congrArg (Measure.map (fun x : ℝ ↦ (x + 1) / 2)) (map_eval_uniformBallMeasure i)
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  have hinv : (fun x : ℝ ↦ ((-1 + 2 * x) + 1) / 2) = id := by ext x; dsimp; ring
  simpa only [Function.comp_def, hinv, Measure.map_id] using h

/-- The cdf of a unit-ball coordinate is the symmetric incomplete Beta cdf at `(x + 1) / 2`,
including the constant extensions outside `[-1, 1]`. -/
theorem cdf_map_eval_uniformBallMeasure (i : ι) (x : ℝ) :
    cdf ((uniformBallMeasure (0 : EuclideanSpace ℝ ι) 1).map (fun x ↦ x i)) x =
      regularizedIncompleteBeta (((Fintype.card ι : ℝ) + 1) / 2)
        (((Fintype.card ι : ℝ) + 1) / 2) ((x + 1) / 2) := by
  have ha : 0 < ((Fintype.card ι : ℝ) + 1) / 2 := by positivity
  have := isProbabilityMeasureBeta ha ha
  rw [map_eval_uniformBallMeasure, cdf_map_affine_of_pos (by norm_num),
    cdf_betaMeasure_eq ha ha, sub_neg_eq_add]

/-- Interior quantiles of a unit-ball coordinate are affine inverse-Beta quantiles. -/
theorem quantile_map_eval_uniformBallMeasure (i : ι) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((uniformBallMeasure (0 : EuclideanSpace ℝ ι) 1).map (fun x ↦ x i)).quantile u =
      -1 + 2 * inverseRegularizedIncompleteBeta (((Fintype.card ι : ℝ) + 1) / 2)
        (((Fintype.card ι : ℝ) + 1) / 2) u := by
  have ha : 0 < ((Fintype.card ι : ℝ) + 1) / 2 := by positivity
  have := isProbabilityMeasureBeta ha ha
  rw [map_eval_uniformBallMeasure, quantile_map_affine_pos (by norm_num) hu.1 hu.2,
    quantile_betaMeasure ha ha hu]

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every real linear observable of a uniform ball point is an affine image of a symmetric
Beta variable. The formula includes zero radius, the zero observable, and dimension zero. -/
theorem map_inner_uniformBallMeasure (c : E) {r : ℝ} (hr : 0 ≤ r) (v : E) :
    (uniformBallMeasure c r).map (fun x ↦ ⟪v, x⟫) =
      (betaMeasure (((Module.finrank ℝ E : ℝ) + 1) / 2)
        (((Module.finrank ℝ E : ℝ) + 1) / 2)).map
          (fun x ↦ ⟪v, c⟫ + r * ‖v‖ * (-1 + 2 * x)) := by
  have ha : 0 < ((Module.finrank ℝ E : ℝ) + 1) / 2 := by positivity
  have := isProbabilityMeasureBeta ha ha
  have := isProbabilityMeasure_uniformBallMeasure (c := c) hr
  by_cases hv : v = 0
  · simp [hv, Measure.map_const]
  have : Nontrivial E := ⟨⟨v, 0, hv⟩⟩
  let d := Module.finrank ℝ E
  let i : Fin d := ⟨0, Module.finrank_pos⟩
  obtain ⟨f, hcoord⟩ := TauCeti.exists_linearIsometryEquiv_inner_eq_norm_mul_eval v i
  have hunit : (uniformBallMeasure (0 : E) 1).map (fun x ↦ ⟪v, x⟫) =
      (betaMeasure (((d : ℝ) + 1) / 2) (((d : ℝ) + 1) / 2)).map
        (fun x ↦ ‖v‖ * (-1 + 2 * x)) := by
    calc
      _ = (((uniformBallMeasure (0 : E) 1).map f).map (fun x ↦ x i)).map
          (fun x ↦ ‖v‖ * x) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop),
          Measure.map_map (by fun_prop) (by fun_prop)]
        congr 1
        exact funext hcoord
      _ = _ := by
        rw [f.map_uniformBallMeasure, map_zero, map_eval_uniformBallMeasure,
          Measure.map_map (by fun_prop) (by fun_prop)]
        simp only [Fintype.card_fin, Function.comp_def, d]
  calc
    _ = ((uniformBallMeasure (0 : E) 1).map (fun x ↦ ⟪v, x⟫)).map
        (fun x ↦ ⟪v, c⟫ + r * x) := by
      rw [uniformBallMeasure_eq_map_unitBall c hr,
        Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      ext x
      simp [inner_add_right, inner_smul_right]
    _ = _ := by
      rw [hunit, Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      ext x
      dsimp
      ring

private theorem map_inner_uniformBallMeasure_affine (c : E) {r : ℝ} (hr : 0 ≤ r) (v : E) :
    (uniformBallMeasure c r).map (fun x ↦ ⟪v, x⟫) =
      (betaMeasure (((Module.finrank ℝ E : ℝ) + 1) / 2)
        (((Module.finrank ℝ E : ℝ) + 1) / 2)).map
          (fun y ↦ (⟪v, c⟫ - r * ‖v‖) + (2 * (r * ‖v‖)) * y) := by
  rw [map_inner_uniformBallMeasure c hr v]
  congr 1
  ext y
  ring

/-- For a nonconstant projection of a positive-radius ball, the cdf is the symmetric
incomplete Beta cdf in its affine coordinate. -/
theorem cdf_map_inner_uniformBallMeasure (c : E) {r : ℝ} (hr : 0 < r) {v : E}
    (hv : v ≠ 0) (x : ℝ) :
    cdf ((uniformBallMeasure c r).map (fun x ↦ ⟪v, x⟫)) x =
      regularizedIncompleteBeta (((Module.finrank ℝ E : ℝ) + 1) / 2)
        (((Module.finrank ℝ E : ℝ) + 1) / 2)
        ((x - (⟪v, c⟫ - r * ‖v‖)) / (2 * (r * ‖v‖))) := by
  have ha : 0 < ((Module.finrank ℝ E : ℝ) + 1) / 2 := by positivity
  have := isProbabilityMeasureBeta ha ha
  rw [map_inner_uniformBallMeasure_affine c hr.le v,
    cdf_map_affine_of_pos (by positivity), cdf_betaMeasure_eq ha ha]

/-- Quantiles of a real linear observable of a uniform ball point, including zero radius
and the zero observable. -/
theorem quantile_map_inner_uniformBallMeasure (c : E) {r : ℝ} (hr : 0 ≤ r) (v : E)
    {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((uniformBallMeasure c r).map (fun x ↦ ⟪v, x⟫)).quantile u =
      ⟪v, c⟫ + r * ‖v‖ * (-1 + 2 * inverseRegularizedIncompleteBeta
        (((Module.finrank ℝ E : ℝ) + 1) / 2) (((Module.finrank ℝ E : ℝ) + 1) / 2) u) := by
  have ha : 0 < ((Module.finrank ℝ E : ℝ) + 1) / 2 := by positivity
  have := isProbabilityMeasureBeta ha ha
  rw [map_inner_uniformBallMeasure_affine c hr v]
  by_cases hrv : r * ‖v‖ = 0
  · simp [hrv, Measure.map_const, Measure.quantile_dirac _ hu.1 hu.2.le]
  have hpos : 0 < r * ‖v‖ := lt_of_le_of_ne (mul_nonneg hr (norm_nonneg _)) (Ne.symm hrv)
  rw [quantile_map_affine_pos (by positivity) hu.1 hu.2,
    quantile_betaMeasure ha ha hu]
  ring

/-- Projection quantiles tend to the lower endpoint of the projected closed ball. -/
theorem tendsto_quantile_map_inner_uniformBallMeasure_nhdsGT_zero (c : E) {r : ℝ}
    (hr : 0 ≤ r) (v : E) :
    Tendsto ((uniformBallMeasure c r).map (fun x ↦ ⟪v, x⟫)).quantile
      (𝓝[>] 0) (𝓝 (⟪v, c⟫ - r * ‖v‖)) := by
  have ha : 0 < ((Module.finrank ℝ E : ℝ) + 1) / 2 := by positivity
  have h := (((tendsto_inverseRegularizedIncompleteBeta_zero ha ha).const_mul 2).const_add (-1)
    |>.const_mul (r * ‖v‖)).const_add ⟪v, c⟫
  simp only [mul_zero, add_zero, mul_neg_one, ← sub_eq_add_neg] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact (quantile_map_inner_uniformBallMeasure c hr v hu).symm

/-- Projection quantiles tend to the upper endpoint of the projected closed ball. -/
theorem tendsto_quantile_map_inner_uniformBallMeasure_nhdsLT_one (c : E) {r : ℝ}
    (hr : 0 ≤ r) (v : E) :
    Tendsto ((uniformBallMeasure c r).map (fun x ↦ ⟪v, x⟫)).quantile
      (𝓝[<] 1) (𝓝 (⟪v, c⟫ + r * ‖v‖)) := by
  have ha : 0 < ((Module.finrank ℝ E : ℝ) + 1) / 2 := by positivity
  have h := (((tendsto_inverseRegularizedIncompleteBeta_one ha ha).const_mul 2).const_add (-1)
    |>.const_mul (r * ‖v‖)).const_add ⟪v, c⟫
  norm_num only [mul_one, neg_add_cancel_left] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_map_inner_uniformBallMeasure c hr v hu).symm

end Projection

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A rescaled coordinate of a uniform random point in the unit ball is symmetric Beta. -/
theorem add_one_div_two_eval_uniformBallMeasure {ι : Type*} [Fintype ι]
    {X : Ω → EuclideanSpace ℝ ι}
    (hX : HasLaw X (uniformBallMeasure 0 1) P) (i : ι) :
    HasLaw (fun ω ↦ (X ω i + 1) / 2)
      (betaMeasure (((Fintype.card ι : ℝ) + 1) / 2) (((Fintype.card ι : ℝ) + 1) / 2)) P :=
  (HasLaw.mk (by fun_prop) (map_add_one_div_two_eval_uniformBallMeasure i)).comp hX

/-- A real linear observable of a uniform random ball point has an affine Beta law. -/
theorem inner_uniformBallMeasure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {X : Ω → E} {c : E} {r : ℝ}
    (hX : HasLaw X (uniformBallMeasure c r) P) (hr : 0 ≤ r) (v : E) :
    HasLaw (fun ω ↦ ⟪v, X ω⟫)
      ((betaMeasure (((Module.finrank ℝ E : ℝ) + 1) / 2)
        (((Module.finrank ℝ E : ℝ) + 1) / 2)).map
          (fun x ↦ ⟪v, c⟫ + r * ‖v‖ * (-1 + 2 * x))) P :=
  (HasLaw.mk (by fun_prop) (map_inner_uniformBallMeasure c hr v)).comp hX

end ProbabilityTheory.HasLaw
