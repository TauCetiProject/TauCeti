/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Asymptotic bounds for homogeneous polynomials

A continuous multilinear map `q` in `k` variables defines the homogeneous polynomial
`y ↦ q (y, …, y)` of degree `k`. Mathlib bounds it pointwise by `‖q‖ * ‖y‖ ^ k`
(`ContinuousMultilinearMap.le_opNorm`); this file records the asymptotic forms of this bound.

## Main results

* `ContinuousMultilinearMap.isBigO_apply_const`: `q (y, …, y) = O(‖y‖ ^ k)` along any filter.
* `ContinuousMultilinearMap.isBigO_apply_const_sub`: for `k ≥ 2` and `w y = y + O(‖y‖ ^ k)` near
  `0`, `q (w y, …, w y) - q (y, …, y) = O(‖y‖ ^ (k + 1))`.
* `ContinuousMultilinearMap.isBigO_of_isBigO_sub_smul_apply_const`: if
  `g y = c • q (y, …, y) + O(‖y‖ ^ (k + 1))` near `0`, then `g y = O(‖y‖ ^ k)`.
-/

public section

open Filter Topology Asymptotics

namespace ContinuousMultilinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {k : ℕ}

/-- A homogeneous polynomial `y ↦ q (y, …, y)` of degree `k` is `O(‖y‖ ^ k)`. -/
theorem isBigO_apply_const (q : ContinuousMultilinearMap 𝕜 (fun _ : Fin k => E) F)
    (l : Filter E) : (fun y : E => q fun _ => y) =O[l] fun y => ‖y‖ ^ k :=
  IsBigO.of_bound ‖q‖ (Eventually.of_forall fun y => by
    simpa [abs_of_nonneg (pow_nonneg (norm_nonneg y) k)] using q.le_opNorm fun _ => y)

/-- For a homogeneous polynomial `P` of degree `k ≥ 2` and `w y = y + O(‖y‖ ^ k)` near `0`,
`P (w y) - P y = O(‖y‖ ^ (k + 1))`. -/
theorem isBigO_apply_const_sub (hk : 2 ≤ k)
    (q : ContinuousMultilinearMap 𝕜 (fun _ : Fin k => E) F) {w : E → E}
    (hw1 : w =O[𝓝 0] fun y => ‖y‖) (hwy : (fun y => w y - y) =O[𝓝 0] fun y => ‖y‖ ^ k) :
    (fun y => (q fun _ => w y) - q fun _ => y) =O[𝓝 0] fun y => ‖y‖ ^ (k + 1) := by
  have h1 : (fun y => (q fun _ => w y) - q fun _ => y) =O[𝓝 0]
      fun y => (‖w y‖ + ‖y‖) ^ (k - 1) * ‖w y - y‖ := by
    refine IsBigO.of_bound (‖q‖ * k) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    refine (q.norm_image_sub_le _ _).trans ?_
    simp only [Fintype.card_fin, mul_assoc]
    gcongr
    · exact (max_le_max (pi_norm_const_le _) (pi_norm_const_le _)).trans
        (max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _)))
    · exact pi_norm_const_le (w y - y)
  have h2 : (fun y => (‖w y‖ + ‖y‖) ^ (k - 1) * ‖w y - y‖) =O[𝓝 0]
      fun y => ‖y‖ ^ (k - 1) * ‖y‖ ^ k :=
    ((hw1.norm_left.add (isBigO_refl _ _)).pow (k - 1)).mul hwy.norm_left
  have h3 : (fun y : E => ‖y‖ ^ (k - 1) * ‖y‖ ^ k) =O[𝓝 0] fun y => ‖y‖ ^ (k + 1) := by
    simp only [← pow_add]
    rcases (show k + 1 ≤ k - 1 + k by omega).eq_or_lt with h | h
    · rw [h]
    · exact (isLittleO_norm_pow_norm_pow h).isBigO
  exact h1.trans (h2.trans h3)

/-- If `g y = c • P y + O(‖y‖ ^ (k + 1))` near `0` for a homogeneous polynomial `P` of degree `k`,
then `g y = O(‖y‖ ^ k)`. -/
theorem isBigO_of_isBigO_sub_smul_apply_const
    (q : ContinuousMultilinearMap 𝕜 (fun _ : Fin k => E) F) {g : E → F} {c : 𝕜}
    (hg : (fun y => g y - c • q fun _ => y) =O[𝓝 0] fun y => ‖y‖ ^ (k + 1)) :
    g =O[𝓝 0] fun y => ‖y‖ ^ k := by
  have : g = fun y => (g y - c • q fun _ => y) + c • q fun _ => y := by
    ext y
    abel
  rw [this]
  exact (hg.trans (isLittleO_norm_pow_norm_pow (lt_add_one k)).isBigO).add
    ((q.isBigO_apply_const _).const_smul_left _)

end ContinuousMultilinearMap
