/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Uniform.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Affine images of interval-uniform laws

An affine map with positive slope transports both endpoints of a uniform interval in order.
A negative slope reverses their order and exchanges the two half-open endpoint conventions;
the endpoint atoms vanish, so the resulting law is again the named interval-uniform law.
These identities also cover invalid source intervals, whose laws are zero.

For a nondegenerate source interval, the full affine formula sorts the transformed endpoints
at nonzero slope and gives a Dirac measure at zero slope. Its `HasLaw` corollaries transport
uniform random variables without requiring a separate density calculation.

The positive-slope proof uses `map_uniformMeasure_affine`, the construction of an interval
uniform from a unit uniform. Reflection uses Lebesgue measure's invariance under negation
and `MeasureTheory.Measure.restrict_congr_set` to retain the endpoint convention.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- A positive affine image of an interval-uniform law has the transformed endpoints.
This includes the zero laws on empty or reversed source intervals. -/
@[simp]
theorem uniformMeasure_map_affine_pos (a b c : ℝ) {s : ℝ} (hs : 0 < s) :
    (uniformMeasure a b).map (fun x ↦ c + s * x) =
      uniformMeasure (c + s * a) (c + s * b) := by
  by_cases hab : a < b
  · have htarget : c + s * a < c + s * b := by nlinarith
    rw [← map_uniformMeasure_affine hab,
      Measure.map_map (by fun_prop) (by fun_prop), ← map_uniformMeasure_affine htarget]
    congr 1
    ext x
    simp only [Function.comp_apply]
    ring
  · have hba := le_of_not_gt hab
    rw [uniformMeasure_eq_zero_of_le hba, Measure.map_zero,
      uniformMeasure_eq_zero_of_le (by nlinarith)]

/-- A negative affine image of an interval-uniform law has the reversed transformed endpoints.
The two half-open endpoint conventions define the same law, since their endpoint atoms vanish.
The identity includes the zero laws on empty or reversed source intervals. -/
@[simp]
theorem uniformMeasure_map_affine_neg (a b c : ℝ) {s : ℝ} (hs : s < 0) :
    (uniformMeasure a b).map (fun x ↦ c + s * x) =
      uniformMeasure (c + s * b) (c + s * a) := by
  have hpre : (fun x : ℝ ↦ -x) ⁻¹' Ioc (-b) (-a) = Ico a b := by
    ext x
    simp only [mem_preimage, mem_Ioc, mem_Ico, neg_lt_neg_iff, neg_le_neg_iff]
    exact and_comm
  have hreflect : (uniformMeasure a b).map (fun x : ℝ ↦ -x) =
      uniformMeasure (-b) (-a) := by
    rw [uniformMeasure_eq_smul, Measure.map_smul _ measurable_neg.aemeasurable,
      ← Measure.restrict_congr_set (Ico_ae_eq_Ioc (μ := (volume : Measure ℝ)) (a := a) (b := b)),
      ← hpre, ← Measure.restrict_map measurable_neg measurableSet_Ioc,
      Measure.map_neg_eq_self (volume : Measure ℝ), uniformMeasure_eq_smul]
    simp only [neg_sub_neg]
  have h := uniformMeasure_map_affine_pos (-b) (-a) c (neg_pos.mpr hs)
  rw [← hreflect, Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa only [Function.comp_def, neg_mul_neg] using h

/-- An affine image of a genuine interval-uniform law is uniform between the sorted image
endpoints at nonzero slope, and is a Dirac law at zero slope. -/
theorem uniformMeasure_map_affine {a b : ℝ} (hab : a < b) (c s : ℝ) :
    (uniformMeasure a b).map (fun x ↦ c + s * x) =
      if s = 0 then Measure.dirac c else
        uniformMeasure (min (c + s * a) (c + s * b))
          (max (c + s * a) (c + s * b)) := by
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have horder : c + s * b ≤ c + s * a := by nlinarith
    simp [hs.ne, min_eq_right horder, max_eq_left horder,
      uniformMeasure_map_affine_neg a b c hs]
  · let _ := isProbabilityMeasure_uniformMeasure hab
    simp
  · have horder : c + s * a ≤ c + s * b := by nlinarith
    simp [hs.ne', min_eq_left horder, max_eq_right horder,
      uniformMeasure_map_affine_pos a b c hs]

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {a b : ℝ}

/-- A positive affine image of a uniform random variable is uniform on the transformed interval,
including the zero source laws at invalid endpoints. -/
theorem HasLaw.affine_pos_uniformMeasure (hX : HasLaw X (uniformMeasure a b) P)
    (c : ℝ) {s : ℝ} (hs : 0 < s) :
    HasLaw (fun ω ↦ c + s * X ω) (uniformMeasure (c + s * a) (c + s * b)) P :=
  (HasLaw.mk (by fun_prop) (uniformMeasure_map_affine_pos a b c hs)).fun_comp hX

/-- A negative affine image of a uniform random variable is uniform on the interval with reversed
transformed endpoints, including the zero source laws at invalid endpoints. -/
theorem HasLaw.affine_neg_uniformMeasure (hX : HasLaw X (uniformMeasure a b) P)
    (c : ℝ) {s : ℝ} (hs : s < 0) :
    HasLaw (fun ω ↦ c + s * X ω) (uniformMeasure (c + s * b) (c + s * a)) P :=
  (HasLaw.mk (by fun_prop) (uniformMeasure_map_affine_neg a b c hs)).fun_comp hX

/-- An affine image of a uniform random variable has the uniform law on the sorted image interval,
with a Dirac law at zero slope. -/
theorem HasLaw.affine_uniformMeasure (hX : HasLaw X (uniformMeasure a b) P)
    (hab : a < b) (c s : ℝ) :
    HasLaw (fun ω ↦ c + s * X ω)
      (if s = 0 then Measure.dirac c else
        uniformMeasure (min (c + s * a) (c + s * b))
          (max (c + s * a) (c + s * b))) P :=
  (HasLaw.mk (by fun_prop) (uniformMeasure_map_affine hab c s)).fun_comp hX

end ProbabilityTheory
