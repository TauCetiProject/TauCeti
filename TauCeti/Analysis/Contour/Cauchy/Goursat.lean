/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Cauchy–Goursat for a pole-free meromorphic function

If `A : ℂ → E` (with `E` a complex normed space) is meromorphic on the closed disc
`closedBall c R` (`R ≥ 0`) and has non-negative meromorphic order at every point of the disc, then
the contour integral of `A` around the boundary circle vanishes: `∮ z in C(c, R), A z = 0`.

This is the pole-free base case shared by the argument principle and the classical residue theorem:
integrating a meromorphic function with no poles in the closed disc gives `0`. No pointwise
regularity of `A` itself is required: `A` may take arbitrary values on a discrete subset of the
disc, since it agrees there with its meromorphic normal form, which is analytic throughout the disc.

## Main results

* `TauCeti.Contour.circleIntegral_eq_zero_of_meromorphicOrderAt_nonneg` — the vanishing of the
  circle integral of a pole-free meromorphic function.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project, specialised to a circle.
-/

public section

open Filter Metric Complex

namespace TauCeti.Contour

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Cauchy–Goursat for a pole-free meromorphic function.** If `A` is meromorphic on the closed
disc `closedBall c R` (`R ≥ 0`) and has non-negative meromorphic order at every point of the disc,
then `∮ z in C(c, R), A z = 0`. -/
lemma circleIntegral_eq_zero_of_meromorphicOrderAt_nonneg {A : ℂ → E} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hA : MeromorphicOn A (closedBall c R))
    (hord : ∀ z ∈ closedBall c R, 0 ≤ meromorphicOrderAt A z) :
    circleIntegral A c R = 0 := by
  rcases hR.eq_or_lt with rfl | hR
  · exact circleIntegral.integral_radius_zero A c
  -- The normal form `B` of `A` is analytic on the whole disc, so `∮ B = 0` by Cauchy–Goursat.
  set B := toMeromorphicNFOn A (closedBall c R)
  have hB : AnalyticOnNhd ℂ B (closedBall c R) := fun z hz ↦
    (meromorphicNFOn_toMeromorphicNFOn A _ hz).meromorphicOrderAt_nonneg_iff_analyticAt.1 <| by
      rw [meromorphicOrderAt_toMeromorphicNFOn hA hz]
      exact hord z hz
  rw [← circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le Set.countable_empty
    hB.continuousOn fun z hz ↦ (hB z (ball_subset_closedBall hz.1)).differentiableAt]
  -- `A` and `B` agree off a discrete subset of the circle, hence for almost every angle. (Mathlib's
  -- `circleIntegral.circleIntegral_congr_codiscreteWithin` covers only `ℂ`-valued functions.)
  have hAB : A =ᶠ[codiscreteWithin (sphere c |R|)] B := by
    rw [abs_of_pos hR]
    exact (toMeromorphicNFOn_eqOn_codiscrete hA).filter_mono
      (codiscreteWithin_mono sphere_subset_closedBall)
  refine intervalIntegral.integral_congr_ae_restrict <|
    ae_restrict_le_codiscreteWithin measurableSet_uIoc ?_
  filter_upwards [codiscreteWithin_mono (Set.subset_univ _)
    (circleMap_preimage_codiscrete hR.ne' hAB)] with θ hθ
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hθ
  rw [hθ]

end TauCeti.Contour
