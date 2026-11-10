/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Differentiating bounded continuous functions in the supremum norm

A uniform bound on the second pointwise time derivative controls the Taylor remainder in
supremum norm. Consequently a compactly supported `C²` function on space-time defines a
differentiable curve of bounded continuous functions, whose derivative is its time partial.
The target need not be complete, and the general lifting theorem permits an empty index space.
-/

public section

open Asymptotics Filter Set
open scoped Topology ContDiff

namespace BoundedContinuousFunction

variable {V F : Type*} [TopologicalSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A bounded second time derivative makes the pointwise derivative a
derivative of the curve in the supremum norm. -/
theorem hasDerivAt_of_bounded_second_derivative
    (u du : ℝ → BoundedContinuousFunction V F) (ddu : ℝ → V → F)
    {K : ℝ} (hK : 0 ≤ K)
    (hu : ∀ t x, HasDerivAt (fun s ↦ u s x) (du t x) t)
    (hdu : ∀ t x, HasDerivAt (fun s ↦ du s x) (ddu t x) t)
    (hb : ∀ t x, ‖ddu t x‖ ≤ K) (t : ℝ) :
    HasDerivAt u (du t) t := by
  have hLip (s r : ℝ) (x : V) : ‖du s x - du r x‖ ≤ K * ‖s - r‖ := by
    exact (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun q _ ↦ (hdu q x).hasDerivWithinAt) (fun q _ ↦ hb q x) (mem_univ r) (mem_univ s)
  apply HasDerivAt.of_isLittleO
  refine (IsBigO.of_bound (g := fun s ↦ ‖s - t‖ ^ 2) K ?_).trans_isLittleO
    (isLittleO_pow_sub_sub t (by norm_num : 1 < (2 : ℕ)))
  filter_upwards with s
  simp only [norm_pow, norm_norm]
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  change ‖u s x - u t x - (s - t) • du t x‖ ≤ _
  -- Mathlib already subtracts the fixed linear part in its mean-value inequality.
  have h := (convex_segment t s).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (φ := ContinuousLinearMap.toSpanSingleton ℝ (du t x))
    (fun r _ ↦ (hu r x).hasFDerivAt.hasFDerivWithinAt)
    (fun r hr ↦ by
      change ‖ContinuousLinearMap.toSpanSingletonLIE ℝ F (du r x) -
        ContinuousLinearMap.toSpanSingletonLIE ℝ F (du t x)‖ ≤ _
      rw [← (ContinuousLinearMap.toSpanSingletonLIE ℝ F).map_sub,
        (ContinuousLinearMap.toSpanSingletonLIE ℝ F).norm_map]
      exact (hLip r t x).trans (mul_le_mul_of_nonneg_left
        (norm_sub_le_of_mem_segment hr) hK))
    (left_mem_segment ℝ t s) (right_mem_segment ℝ t s)
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, pow_two, mul_assoc] using h

/-- A continuous compactly supported function on space-time, viewed as a curve of bounded
continuous spatial functions. -/
@[expose] noncomputable def compactSlice (f : V × ℝ → F) (hf : Continuous f)
    (hc : HasCompactSupport f) (t : ℝ) : V →ᵇ F :=
  ofNormedAddCommGroup (fun x ↦ f (x, t))
    (hf.comp (continuous_id.prodMk continuous_const))
    (hc.exists_bound_of_continuous hf).choose
    (fun x ↦ (hc.exists_bound_of_continuous hf).choose_spec (x, t))

omit [NormedSpace ℝ F] in
/-- Evaluation of a compactly supported time slice. -/
@[simp]
theorem compactSlice_apply (f : V × ℝ → F) (hf : Continuous f)
    (hc : HasCompactSupport f) (t : ℝ) (x : V) :
    compactSlice f hf hc t x = f (x, t) := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The curve of time slices of a compactly supported `C²` function is differentiable in the
supremum norm, with derivative equal to its actual time partial. -/
theorem hasDerivAt_compactSlice {f : E × ℝ → F} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (t : ℝ) :
    HasDerivAt (compactSlice f hf.continuous hc)
      (compactSlice (fun p ↦ fderiv ℝ f p (0, 1))
        ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous
        (hc.fderiv_apply ℝ (0, 1)) t) t := by
  let dt := fun p ↦ fderiv ℝ f p (0, 1)
  have hdt : ContDiff ℝ 1 dt :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdtt : Continuous (fun p ↦ fderiv ℝ dt p (0, 1)) :=
    ((hdt.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
  have hct : HasCompactSupport dt := hc.fderiv_apply ℝ (0, 1)
  obtain ⟨K, hK⟩ := (hct.fderiv_apply ℝ (0, 1)).exists_bound_of_continuous hdtt
  apply hasDerivAt_of_bounded_second_derivative
    (ddu := fun s x ↦ fderiv ℝ dt (x, s) (0, 1))
    (hK := (norm_nonneg _).trans (hK (0, 0)))
  · intro s x
    exact TauCeti.hasDerivAt_slice_right (hf.differentiable (by norm_num) (x, s))
  · intro s x
    exact TauCeti.hasDerivAt_slice_right (hdt.differentiable (by norm_num) (x, s))
  · exact fun s x ↦ hK (x, s)

end BoundedContinuousFunction
