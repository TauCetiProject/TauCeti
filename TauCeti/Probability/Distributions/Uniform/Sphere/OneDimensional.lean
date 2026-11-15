/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Probability.Distributions.Rademacher.Basic
public import TauCeti.Probability.Distributions.Uniform.Sphere.Basic

/-!
# The uniform sphere law in dimension one

In a one-dimensional real inner product space, the unit sphere consists of two antipodal
points. Its uniform law assigns mass one half to each point. Consequently, its coordinate
along any unit vector has the Rademacher law, whose cumulative distribution, quantiles,
moments and transforms are available in `TauCeti.Probability.Distributions.Rademacher.Basic`.
Along an arbitrary representing vector, the law is scaled by that vector's norm.
Its cdf and interior quantile are given explicitly, including the zero observable.

The measure identity is stated both on the sphere and after embedding in the ambient space.
These identities also describe the discrete direction in the Gaussian direction/radius
factorization in dimension one.

The argument uses the existing antipodal invariance of the uniform law,
`TauCeti.eq_or_eq_neg_of_norm_eq_of_finrank_eq_one` for the geometry of the sphere, and
Mathlib's `MeasureTheory.Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac` for two-point measures.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal InnerProductSpace

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The uniform law on a one-dimensional unit sphere assigns equal mass to its two antipodes. -/
theorem uniformSphereMeasure_eq_of_finrank_eq_one (hdim : Module.finrank ℝ E = 1)
    (e : sphere (0 : E) 1) :
    uniformSphereMeasure E =
      (1 / 2 : ℝ≥0∞) • Measure.dirac e + (1 / 2 : ℝ≥0∞) • Measure.dirac (-e) := by
  have : Nontrivial E := ⟨⟨e, 0, ne_zero_of_mem_sphere one_ne_zero e⟩⟩
  have he : e ≠ -e := ne_neg_of_mem_unit_sphere ℝ e
  have hpoints : ∀ x : sphere (0 : E) 1, x = e ∨ x = -e := by
    intro x
    exact (eq_or_eq_neg_of_norm_eq_of_finrank_eq_one hdim
      ((norm_eq_of_mem_sphere x).trans (norm_eq_of_mem_sphere e).symm)).imp
        Subtype.ext Subtype.ext
  have hneg : (uniformSphereMeasure E).map (fun x ↦ -x) = uniformSphereMeasure E :=
    (LinearIsometryEquiv.neg ℝ).map_uniformSphereMeasure
  have hmass : uniformSphereMeasure E {-e} = uniformSphereMeasure E {e} := by
    have h := congrArg (fun ν : Measure (sphere (0 : E) 1) ↦ ν {e}) hneg
    simpa [Measure.map_apply measurable_neg (measurableSet_singleton e)] using h
  have huniv : ({e} ∪ {-e} : Set (sphere (0 : E) 1)) = univ := by
    ext x
    simp only [mem_union, mem_singleton_iff, mem_univ, iff_true]
    exact hpoints x
  have hsum : uniformSphereMeasure E {e} + uniformSphereMeasure E {e} = 1 := by
    calc
      _ = uniformSphereMeasure E {e} + uniformSphereMeasure E {-e} := by rw [hmass]
      _ = uniformSphereMeasure E ({e} ∪ {-e}) :=
        (measure_union (by simpa using he) (measurableSet_singleton _)).symm
      _ = 1 := by rw [huniv, measure_univ]
  have hhalf : uniformSphereMeasure E {e} = (1 / 2 : ℝ≥0∞) := by
    apply (ENNReal.eq_div_iff (by norm_num) (by norm_num)).2
    simpa [two_mul] using hsum
  have hdecomp := (Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac
    (μ := uniformSphereMeasure E) he).mp (Filter.Eventually.of_forall hpoints)
  rwa [hmass, hhalf] at hdecomp

/-- Each point of a one-dimensional unit sphere has probability one half. -/
@[simp]
theorem uniformSphereMeasure_singleton_of_finrank_eq_one (hdim : Module.finrank ℝ E = 1)
    (e : sphere (0 : E) 1) : uniformSphereMeasure E {e} = (1 / 2 : ℝ≥0∞) := by
  rw [uniformSphereMeasure_eq_of_finrank_eq_one hdim e]
  simp [(ne_neg_of_mem_unit_sphere ℝ e).symm]

/-- Embedded in its ambient one-dimensional space, the uniform sphere law is the equally
weighted pair of Dirac masses at any chosen unit vector and its negative. -/
theorem map_coe_uniformSphereMeasure_of_finrank_eq_one (hdim : Module.finrank ℝ E = 1)
    (e : sphere (0 : E) 1) :
    (uniformSphereMeasure E).map ((↑) : sphere (0 : E) 1 → E) =
      (1 / 2 : ℝ≥0∞) • Measure.dirac (e : E) +
        (1 / 2 : ℝ≥0∞) • Measure.dirac (-(e : E)) := by
  rw [uniformSphereMeasure_eq_of_finrank_eq_one hdim e]
  rw [Measure.map_add _ _ measurable_subtype_coe,
    Measure.map_smul _ measurable_subtype_coe.aemeasurable,
    Measure.map_smul _ measurable_subtype_coe.aemeasurable]
  simp

/-- The coordinate of a uniform one-dimensional sphere point along a unit vector is Rademacher.
This identifies its cumulative distribution, interior quantiles, moments and transforms with
the existing two-point law. -/
theorem map_inner_uniformSphereMeasure_of_finrank_eq_one (hdim : Module.finrank ℝ E = 1)
    (e : sphere (0 : E) 1) :
    (uniformSphereMeasure E).map (fun x : sphere (0 : E) 1 ↦ ⟪(e : E), (x : E)⟫_ℝ) =
      rademacherMeasure := by
  rw [uniformSphereMeasure_eq_of_finrank_eq_one hdim e, rademacherMeasure_eq]
  have hm : Measurable fun x : sphere (0 : E) 1 ↦ ⟪(e : E), (x : E)⟫_ℝ := by fun_prop
  rw [Measure.map_add _ _ hm, Measure.map_smul _ hm.aemeasurable,
    Measure.map_smul _ hm.aemeasurable]
  simp [ENNReal.smul_def, add_comm]

/-- In dimension one, any real linear observable of a uniform sphere point has a
Rademacher law scaled by the norm of its representing vector, including the zero vector. -/
theorem map_inner_uniformSphereMeasure_eq_map_rademacher_of_finrank_eq_one
    (hd : Module.finrank ℝ E = 1) (v : E) :
    (uniformSphereMeasure E).map (fun u : sphere (0 : E) 1 ↦ ⟪v, (u : E)⟫_ℝ) =
      rademacherMeasure.map (fun y ↦ ‖v‖ * y) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  by_cases hv : v = 0
  · simp [hv, Measure.map_const]
  let e : sphere (0 : E) 1 :=
    ⟨NormedSpace.normalize v, mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hv)⟩
  have h := congrArg (Measure.map (fun y : ℝ ↦ ‖v‖ * y))
    (map_inner_uniformSphereMeasure_of_finrank_eq_one hd e)
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa only [Function.comp_def, ← real_inner_smul_left, e,
    NormedSpace.norm_smul_normalize] using h

/-- In dimension one, projection cdfs have two equally weighted atoms at the extreme
values. For the zero observable these coincide and give the Dirac cdf at zero. -/
theorem cdf_map_inner_uniformSphereMeasure_of_finrank_eq_one
    (hd : Module.finrank ℝ E = 1) (v : E) (x : ℝ) :
    cdf ((uniformSphereMeasure E).map (fun u : sphere (0 : E) 1 ↦ ⟪v, (u : E)⟫_ℝ)) x =
      if x < -‖v‖ then 0 else if x < ‖v‖ then 1 / 2 else 1 := by
  rw [map_inner_uniformSphereMeasure_eq_map_rademacher_of_finrank_eq_one hd v]
  by_cases hv : v = 0
  · simp [hv, Measure.map_const, cdf_dirac]
    split_ifs <;> grind
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h := cdf_map_affine_of_pos (μ := rademacherMeasure) (a := 0) hn x
  simpa only [zero_add, sub_zero, cdf_rademacherMeasure,
    div_lt_iff₀ hn, neg_one_mul, one_mul] using h

/-- In dimension one, projection quantiles equal the lower extreme through probability
one half and the upper extreme above it, including the constant-zero observable. -/
theorem quantile_map_inner_uniformSphereMeasure_of_finrank_eq_one
    (hd : Module.finrank ℝ E = 1) (v : E) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((uniformSphereMeasure E).map (fun x : sphere (0 : E) 1 ↦ ⟪v, (x : E)⟫_ℝ)).quantile u =
      if u ≤ 1 / 2 then -‖v‖ else ‖v‖ := by
  rw [map_inner_uniformSphereMeasure_eq_map_rademacher_of_finrank_eq_one hd v]
  by_cases hv : v = 0
  · simp [hv, Measure.map_const, Measure.quantile_dirac _ hu.1 hu.2.le]
  have h := quantile_map_affine_pos (μ := rademacherMeasure) (a := 0)
    (norm_pos_iff.mpr hv) hu.1 hu.2
  simpa only [zero_add, quantile_rademacherMeasure hu, mul_ite, mul_neg_one, mul_one] using h

/-- In dimension one the exponential moment is the hyperbolic cosine of the coordinate
along a chosen unit vector. -/
theorem integral_exp_inner_uniformSphereMeasure_of_finrank_eq_one
    (hdim : Module.finrank ℝ E = 1) (η : E) (e : sphere (0 : E) 1) :
    ∫ x : sphere (0 : E) 1, Real.exp ⟪η, (x : E)⟫_ℝ ∂uniformSphereMeasure E =
      Real.cosh ⟪η, (e : E)⟫_ℝ := by
  rw [uniformSphereMeasure_eq_of_finrank_eq_one hdim e,
    integral_add_measure
      ((integrable_dirac (by finiteness)).smul_measure (by finiteness))
      ((integrable_dirac (by finiteness)).smul_measure (by finiteness)), integral_smul_measure,
    integral_smul_measure]
  simp [Real.cosh_eq, inner_neg_right, smul_eq_mul]
  ring

/-- The unit sphere of the real line, embedded in `ℝ`, has the Rademacher law. -/
@[simp]
theorem map_coe_uniformSphereMeasure_real :
    (uniformSphereMeasure ℝ).map ((↑) : sphere (0 : ℝ) 1 → ℝ) = rademacherMeasure := by
  simpa using map_inner_uniformSphereMeasure_of_finrank_eq_one (E := ℝ) (by simp)
    ⟨1, by simp⟩

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → sphere (0 : E) 1}

/-- A uniform point on a one-dimensional unit sphere has a Rademacher coordinate along any
unit vector. -/
theorem HasLaw.inner_uniformSphereMeasure_of_finrank_eq_one
    (hX : HasLaw X (uniformSphereMeasure E) P) (hdim : Module.finrank ℝ E = 1)
    (e : sphere (0 : E) 1) :
    HasLaw (fun ω ↦ ⟪(e : E), (X ω : E)⟫_ℝ) rademacherMeasure P :=
  HasLaw.comp (Y := fun x : sphere (0 : E) 1 ↦ ⟪(e : E), (x : E)⟫_ℝ)
    ⟨(by fun_prop), map_inner_uniformSphereMeasure_of_finrank_eq_one hdim e⟩ hX

/-- Every real linear observable of a uniform random unit vector in dimension one has a
Rademacher law scaled by the norm of its representing vector. -/
theorem HasLaw.inner_uniformSphereMeasure_eq_map_rademacher_of_finrank_eq_one
    (hX : HasLaw X (uniformSphereMeasure E) P) (hd : Module.finrank ℝ E = 1) (v : E) :
    HasLaw (fun ω ↦ ⟪v, (X ω : E)⟫_ℝ) (rademacherMeasure.map (fun y ↦ ‖v‖ * y)) P :=
  (HasLaw.mk (by fun_prop)
    (map_inner_uniformSphereMeasure_eq_map_rademacher_of_finrank_eq_one hd v)).comp hX

end ProbabilityTheory
