/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Critical points of holomorphic maps

For a nonconstant analytic map on a connected complex domain, the derivative cannot vanish on a
neighborhood of any point. Since the derivative is analytic, the identity principle and the
isolated-zero theorem then show that every critical point is isolated. This local fact is a first
step toward the local theory of holomorphic curves and the analysis of their moduli spaces.
-/

public section

open Filter
open scoped Topology

namespace AnalyticOnNhd

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {f : ℂ → F} {U : Set ℂ}

/-- **Critical points of a nonconstant analytic map are isolated.** Let `f` be analytic on an open,
preconnected set `U`, and suppose it is not constant there. At each `z ∈ U`, its derivative is
nonzero on a punctured neighborhood of `z`. In particular, every critical point of `f` in `U` is
isolated. -/
theorem eventually_deriv_ne_zero_of_not_eqOn_const (hf : AnalyticOnNhd ℂ f U)
    (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hnc : ¬ ∃ c, Set.EqOn f (fun _ : ℂ ↦ c) U) {z : ℂ} (hz : z ∈ U) :
    ∀ᶠ w in 𝓝[≠] z, deriv f w ≠ 0 := by
  have hdf := hf.deriv
  rcases (hf z hz).deriv.eventually_eq_zero_or_eventually_ne_zero with hzero | hnonzero
  · have hdfzero := hdf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz hzero
    exfalso
    apply hnc
    refine ⟨f z, fun w hw ↦ ?_⟩
    exact (hUo.is_const_of_deriv_eq_zero hUc hf.differentiableOn hdfzero hz hw).symm
  · exact hnonzero

end AnalyticOnNhd

end
