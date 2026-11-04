/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Splitting a set integral along concentric balls

Let `μ` be an additive Haar measure on a nontrivial finite-dimensional real normed space, and let
the closed ball of radius `r` about `c` lie in a set `A`. For `s ≤ r`, the integral of an
integrable function over `A` is the sum of its integrals over `A` minus the open ball of radius
`r`, over the closed annulus `s ≤ ‖w - c‖ ≤ r`, and over the open ball of radius `s`
(`TauCeti.setIntegral_diff_ball_add_annulus_add_ball`). The first two pieces overlap only in the
sphere of radius `r`, which is null. This removes a disc from a region so that an annulus formula
applies to the removed part.
-/

public section

open MeasureTheory Metric Set

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Splitting a set integral along concentric balls.** If the closed ball of radius `r` about
`c` lies in `A` and `s ≤ r`, the integral over `A` of a function integrable on `A` is its integral
over `A` minus the open ball of radius `r`, plus its integral over the closed annulus
`s ≤ ‖w - c‖ ≤ r`, plus its integral over the open ball of radius `s`. -/
theorem setIntegral_diff_ball_add_annulus_add_ball (μ : Measure E) [μ.IsAddHaarMeasure]
    {A : Set E} {c : E} {r s : ℝ} (hsr : s ≤ r) (hA : closedBall c r ⊆ A) {f : E → F}
    (hf : IntegrableOn f A μ) :
    (∫ w in A \ ball c r, f w ∂μ) + (∫ w in {w | s ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r}, f w ∂μ) +
        ∫ w in ball c s, f w ∂μ = ∫ w in A, f w ∂μ := by
  set D : Set E := {w | s ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r}
  have hD : D ⊆ closedBall c r := fun w hw ↦ by
    rw [mem_closedBall, dist_eq_norm]
    exact hw.2
  have hball : ball c s ⊆ closedBall c r :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hsr)
  have hAeq : A = A \ ball c r ∪ (D ∪ ball c s) := by
    refine Subset.antisymm (fun w hw ↦ ?_)
      (union_subset sdiff_subset (union_subset (hD.trans hA) (hball.trans hA)))
    by_cases hr : w ∈ ball c r
    · rw [mem_ball, dist_eq_norm] at hr
      by_cases hs : s ≤ ‖w - c‖
      · exact Or.inr (Or.inl ⟨hs, hr.le⟩)
      · exact Or.inr (Or.inr (by rw [mem_ball, dist_eq_norm]; exact not_le.1 hs))
    · exact Or.inl ⟨hw, hr⟩
  have hc : Continuous fun w : E ↦ ‖w - c‖ := continuous_norm.comp (continuous_sub_right c)
  have hDm : MeasurableSet D :=
    ((isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)).measurableSet
  -- `A` minus the open ball of radius `r` meets the rest only in the sphere of radius `r`.
  have hdisj : AEDisjoint μ (A \ ball c r) (D ∪ ball c s) := by
    refine measure_mono_null (fun w ⟨⟨_, hw⟩, hw'⟩ ↦ ?_) (Measure.addHaar_sphere μ c r)
    rw [mem_ball, not_lt, dist_eq_norm] at hw
    rw [mem_sphere_iff_norm]
    rcases hw' with hw' | hw'
    · exact le_antisymm hw'.2 hw
    · rw [mem_ball, dist_eq_norm] at hw'
      linarith
  rw [hAeq] at hf
  conv_rhs => rw [hAeq]
  rw [setIntegral_union₀ hdisj (hDm.union measurableSet_ball).nullMeasurableSet
      (hf.mono_set subset_union_left) (hf.mono_set subset_union_right),
    setIntegral_union (disjoint_left.2 fun w hw hw' ↦ ?_) measurableSet_ball
      (hf.mono_set fun w hw ↦ Or.inr (Or.inl hw)) (hf.mono_set fun w hw ↦ Or.inr (Or.inr hw)),
    add_assoc]
  rw [mem_ball, dist_eq_norm] at hw'
  linarith [hw.1]

end TauCeti
