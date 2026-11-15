/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Order bounds and cutoff approximations via the continuous functional calculus

This file provides operator inequalities and functional-calculus cutoff approximations for positive
elements in (possibly nonunital) C⋆-algebras:

* `TauCeti.CStarAlgebra.star_mul_mul_self_le`: left-multiplication operator bound
  `star (a * x) * (a * x) ≤ ‖star a * a‖ • (star x * x)`.
* `TauCeti.CStarAlgebra.tendsto_cfcₙ_max_sub_inv`: for `0 ≤ a`, the shifted positive-part cutoffs
  `cfcₙ (fun t ↦ max (t - (n + 1)⁻¹) 0) a` converge in norm to `a` as `n → ∞`.
* `TauCeti.CStarAlgebra.norm_sub_cfcₙ_min_mul_le`: for `0 ≤ x`, the contractive linear-ramp cutoffs
  `u_n = cfcₙ (fun t ↦ min ((n + 1) * max t 0) 1) x` satisfy `‖x - u_n * x‖ ≤ (n + 1)⁻¹`.
-/

public section

open Filter Topology

namespace TauCeti.CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Left-multiplying `x` by `a` scales `star x * x` in the C⋆-algebra order by at most
`‖star a * a‖`. -/
theorem star_mul_mul_self_le (a x : A) :
    star (a * x) * (a * x) ≤ ‖star a * a‖ • (star x * x) := by
  have heq : star (a * x) * (a * x) = star x * (star a * a) * x := by
    simp only [star_mul, mul_assoc]
  rw [heq]
  exact CStarAlgebra.star_left_conjugate_le_norm_smul x (star a * a)
    (IsSelfAdjoint.star_mul_self a)

/-- For a nonnegative element `a` of a C⋆-algebra, the shifted threshold cutoffs
`cfcₙ (fun t ↦ max (t - (n + 1)⁻¹) 0) a` converge in norm to `a`. -/
theorem tendsto_cfcₙ_max_sub_inv {a : A} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ ↦ cfcₙ (fun t : ℝ ↦ max (t - ((n : ℝ) + 1)⁻¹) 0) a) atTop (𝓝 a) := by
  have ha_sa : IsSelfAdjoint a := ha.isSelfAdjoint
  let g : ℕ → ℝ → ℝ := fun n t ↦ max (t - ((n : ℝ) + 1)⁻¹) 0
  have hg_cont : ∀ n : ℕ, Continuous (g n) := fun n ↦ by fun_prop
  have hg_zero : ∀ n : ℕ, g n 0 = 0 := fun n ↦ max_eq_right (sub_nonpos.mpr (by positivity))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' (Eventually.of_forall fun n ↦ ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Real.norm_of_nonneg (norm_nonneg _), one_div]
  set ε : ℝ := ((n : ℝ) + 1)⁻¹
  have hε : 0 < ε := by positivity
  have hsub : cfcₙ (g n) a - a = cfcₙ (fun t : ℝ ↦ g n t - t) a := by
    symm
    rw [cfcₙ_sub (g n) (fun t : ℝ ↦ t) a (hf := (hg_cont n).continuousOn) (hf0 := hg_zero n)
        (hg := continuousOn_id) (hg0 := rfl),
      cfcₙ_id' ℝ a]
  rw [hsub]
  refine norm_cfcₙ_le fun t ht ↦ ?_
  have ht0 : 0 ≤ t := quasispectrum_nonneg_of_nonneg a ha t ht
  rw [Real.norm_eq_abs]
  dsimp only [g]
  rcases le_total t ε with htle | htge
  · rw [max_eq_right (sub_nonpos.mpr htle), zero_sub, abs_neg, abs_of_nonneg ht0]
    exact htle
  · rw [max_eq_left (sub_nonneg.mpr htge), sub_sub_cancel_left, abs_neg, abs_of_nonneg hε.le]

/-- For a nonnegative element `x` of a C⋆-algebra, the contractive ramp cutoff
`u_n = cfcₙ (fun t ↦ min ((n + 1) * max t 0) 1) x` satisfies `‖x - u_n * x‖ ≤ (n + 1)⁻¹`. -/
theorem norm_sub_cfcₙ_min_mul_le {x : A} (hx : 0 ≤ x) (n : ℕ) :
    ‖x - cfcₙ (fun t : ℝ ↦ min (((n : ℝ) + 1) * max t 0) 1) x * x‖ ≤ ((n : ℝ) + 1)⁻¹ := by
  have hx_sa : IsSelfAdjoint x := hx.isSelfAdjoint
  let c : ℝ := (n : ℝ) + 1
  have hc : 0 < c := by positivity
  let g : ℝ → ℝ := fun t ↦ min (c * max t 0) 1
  have hg : Continuous g := by fun_prop
  have hsub : x - cfcₙ g x * x = cfcₙ (fun t : ℝ ↦ t - g t * t) x := by
    symm
    rw [cfcₙ_sub (fun t : ℝ ↦ t) (fun t : ℝ ↦ g t * t) x (hf := continuousOn_id) (hf0 := rfl)
        (hg := Continuous.continuousOn (by fun_prop)) (hg0 := mul_zero _),
      cfcₙ_mul g (fun t : ℝ ↦ t) x (hf := hg.continuousOn) (hf0 := by simp [g])
        (hg := continuousOn_id) (hg0 := rfl),
      cfcₙ_id' ℝ x]
  rw [hsub]
  refine norm_cfcₙ_le fun t ht ↦ ?_
  have ht0 : 0 ≤ t := quasispectrum_nonneg_of_nonneg x hx t ht
  rw [Real.norm_eq_abs]
  dsimp only [g]
  rw [max_eq_left ht0]
  rcases le_total (c * t) 1 with hle | hge
  · rw [min_eq_left hle, abs_of_nonneg (by nlinarith), ← one_div, le_div_iff₀' hc]
    nlinarith
  · rw [min_eq_right hge, one_mul, sub_self, abs_zero]
    positivity

end TauCeti.CStarAlgebra
