/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Liouville
import TauCeti.Analysis.Complex.Sector.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Cauchy's estimate in a sector

Discs whose radii are a fixed multiple of the distance of their centers to the vertex, centered
at the points of a closed sector `|arg z| ≤ θ'`, stay inside every larger open sector
`|arg w| < θ`, and on them the norms are comparable to the norm of the center
(`Complex.exists_pos_forall_closedBall_abs_arg_lt` in `TauCeti.Analysis.Complex.Sector.Bounds`).
Cauchy's estimate for the derivative on these discs turns a power bound `‖f w‖ ≤ B ‖w‖ ^ ν` on
the open sector into the bound `‖f' z‖ ≤ K B ‖z‖ ^ (ν - 1)` on the closed subsector, with `K`
depending only on the sectors and `ν`, both pointwise and eventually as `z → ∞`.

## Main results

* `Complex.exists_pos_norm_deriv_le_of_sector_bound`: a power bound in an open sector gives a
  derivative bound with the next lower power in a closed subsector.
* `Complex.exists_pos_eventually_norm_deriv_le_sector`: the eventual form, along
  `cobounded ℂ` restricted to the sectors.

The statements and proofs are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), files `DLMFMathlib/Analysis/Complex/Sector.lean`, where
the sectors may have any bisector, and `DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean`.
-/

public section

noncomputable section

open Bornology Filter Metric Set
open scoped Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace Complex

/-- **Cauchy's estimate in a sector.** For `θ' < θ` there is `K > 0` such that every `f`
holomorphic on `{A < ‖w‖, |arg w| < θ}` and bounded there by `B ‖w‖ ^ ν` satisfies
`‖f' z‖ ≤ K B ‖z‖ ^ (ν - 1)` for `2 max A 0 < ‖z‖` and `|arg z| ≤ θ'`. The constant does not
depend on `f`, `A` or `B`. -/
theorem exists_pos_norm_deriv_le_of_sector_bound {θ θ' : ℝ} (hθ' : θ' < θ) (ν : ℝ) :
    ∃ K > 0, ∀ (f : ℂ → E) (A B : ℝ),
      DifferentiableOn ℂ f {w | A < ‖w‖ ∧ |w.arg| < θ} →
      (∀ w, A < ‖w‖ → |w.arg| < θ → ‖f w‖ ≤ B * ‖w‖ ^ ν) →
      ∀ z : ℂ, 2 * max A 0 < ‖z‖ → |z.arg| ≤ θ' → ‖deriv f z‖ ≤ K * B * ‖z‖ ^ (ν - 1) := by
  obtain ⟨c, hc, hb⟩ := exists_pos_forall_closedBall_abs_arg_lt hθ'
  refine ⟨2 ^ |ν| / c, by positivity, fun f A B hf hbound z hz harg => ?_⟩
  have hz0 : 0 < ‖z‖ := by linarith [le_max_right A 0]
  have hzne : z ≠ 0 := norm_pos_iff.mp hz0
  have hB : 0 ≤ B := nonneg_of_mul_nonneg_left
    ((norm_nonneg _).trans (hbound z (by linarith [le_max_left A 0]) (harg.trans_lt hθ')))
    (Real.rpow_pos_of_pos hz0 ν)
  have hsub : closedBall z (c * ‖z‖) ⊆ {w | A < ‖w‖ ∧ |w.arg| < θ} := fun w hw => by
    have h := hb z hzne harg w hw
    exact ⟨by linarith [le_max_left A 0, h.2.1], h.1⟩
  have hd := norm_deriv_le_of_forall_mem_sphere_norm_le (mul_pos hc hz0)
    (hf.diffContOnCl_ball hsub) (C := B * 2 ^ |ν| * ‖z‖ ^ ν) fun w hw => by
      have hwc := sphere_subset_closedBall hw
      have h := hb z hzne harg w hwc
      calc ‖f w‖ ≤ B * ‖w‖ ^ ν := hbound w (hsub hwc).1 h.1
        _ ≤ B * (2 ^ |ν| * ‖z‖ ^ ν) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_two_rpow_abs_mul h.2.1 h.2.2) hB
        _ = B * 2 ^ |ν| * ‖z‖ ^ ν := by ring
  refine hd.trans_eq ?_
  rw [Real.rpow_sub hz0, Real.rpow_one]
  field_simp

/-- The eventual form of Cauchy's estimate in a sector: for `θ' < θ` there is `K > 0` such that
an eventual bound `‖f z‖ ≤ B ‖z‖ ^ ν` as `z → ∞` in `|arg z| < θ`, for `f` holomorphic on
`{R < ‖z‖, |arg z| < θ}`, gives `‖f' z‖ ≤ K B ‖z‖ ^ (ν - 1)` as `z → ∞` in `|arg z| ≤ θ'`. The
constant does not depend on `f`, `R` or `B`. -/
theorem exists_pos_eventually_norm_deriv_le_sector {θ θ' : ℝ} (hθ' : θ' < θ) (ν : ℝ) :
    ∃ K > 0, ∀ (f : ℂ → E) (R B : ℝ),
      DifferentiableOn ℂ f {z | R < ‖z‖ ∧ |arg z| < θ} →
      (∀ᶠ z in cobounded ℂ ⊓ 𝓟 {z | |arg z| < θ}, ‖f z‖ ≤ B * ‖z‖ ^ ν) →
      ∀ᶠ z in cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ'}, ‖deriv f z‖ ≤ K * B * ‖z‖ ^ (ν - 1) := by
  obtain ⟨K, hK, hder⟩ := exists_pos_norm_deriv_le_of_sector_bound (E := E) hθ' ν
  refine ⟨K, hK, fun f R B hf hbound => ?_⟩
  obtain ⟨A, -, hA⟩ := (hasBasis_cobounded_norm.inf_principal _).eventually_iff.mp hbound
  refine (hasBasis_cobounded_norm.inf_principal _).eventually_iff.mpr
    ⟨2 * max (max A R) 0 + 1, trivial, fun z ⟨hz, harg⟩ => ?_⟩
  have hfn : DifferentiableOn ℂ f {w | max A R < ‖w‖ ∧ |w.arg| < θ} :=
    hf.mono fun w hw => ⟨(le_max_right A R).trans_lt hw.1, hw.2⟩
  refine hder f (max A R) B hfn (fun w hw hwa => ?_) z ((lt_add_one _).trans_le hz) harg
  exact hA ⟨((le_max_left A R).trans_lt hw).le, hwa⟩

end Complex
