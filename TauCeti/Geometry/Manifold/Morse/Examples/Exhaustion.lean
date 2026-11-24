/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import TauCeti.Geometry.Manifold.Exhaustion
import TauCeti.Topology.Maps.Proper.Metric
import TauCeti.Topology.MetricSpace.ProperSpace

/-!
# Examples of proper exhaustions of the real line

A proper Morse function bounded below is produced by approximating a smooth proper exhaustion
within distance `1` (`ContMDiffMap.exists_isMorse_isProperMap_mem_ball`,
`TauCeti.exists_isMorse_isProperMap_bddBelow`), and the exhaustion itself can be controlled by a
prescribed compact exhaustion (`CompactExhaustion.exists_contMDiffMap_isProperMap`). This file
tests these statements on `ℝ`.

* **A controlled exhaustion.** For the compact exhaustion of `ℝ` by the intervals `[-n, n]`, the
  closed balls of natural radius about `0` (`CompactExhaustion.closedBall`), a point `x` first
  enters at the index `⌈|x|⌉₊` (`CompactExhaustion.find_closedBall`). So there is a smooth proper
  function `g` with `g x ≥ ⌈|x|⌉₊ ≥ 0` whose sublevel `{g ≤ n}` lies in `[-n, n]`
  (`TauCeti.exists_contMDiffMap_isProperMap_natCeil_abs_le`).
* **A bounded function is no exhaustion.** The sublevel `{arctan ≤ 2}` is all of `ℝ`
  (`TauCeti.setOf_arctan_le_two`), so `arctan` is not proper (`TauCeti.not_isProperMap_arctan`).
  In general a proper map into a proper metric space with bounded range has a compact source
  (`IsProperMap.compactSpace_of_isBounded_range`).

The remaining tests need no new statement. The function `x ↦ x²` is Morse
(`TauCeti.isMorse_sq_real`), proper (`TauCeti.isProperMap_pow`) and bounded below by `0`; every
continuous function within distance `1` of it is again proper (`IsProperMap.of_dist_le`) and bounded
below by `-1`, while the unbounded perturbation `-x²` gives the constant `0`, which is not proper on
the noncompact space `ℝ` (`isProperMap_const_iff`). On an empty manifold every function is Morse
(`TauCeti.isMorse_of_isEmpty`) and proper (`Continuous.isProperMap`). On the discrete manifold
`ℕ`, modelled on a zero-dimensional space, every function is Morse with every point critical of
index `0` (`TauCeti.isMorse_of_subsingleton`, `TauCeti.criticalPoints_eq_univ_of_subsingleton`,
`TauCeti.manifoldMorseIndex_eq_zero_of_subsingleton`); the function `n ↦ n` is proper, being a
closed embedding (`Nat.isClosedEmbedding_coe_real`), while a constant function is not, since `ℕ` is
not compact (`isProperMap_const_iff`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer, 2013, Proposition 2.28
  (smooth exhaustion functions).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §6, Corollary 6.8, for the existence of a Morse function with compact sublevels.
-/

public section

open Set Real
open scoped ContDiff Manifold

namespace TauCeti

/-! ### A controlled exhaustion of the real line -/

/-- **A controlled exhaustion of the real line.** There is a smooth proper function `g` on `ℝ`
with `g x ≥ ⌈|x|⌉₊` for every `x`, so that its sublevel `{g ≤ n}` at a natural height `n` lies in
`[-n, n]`. It is the exhaustion controlled by the compact exhaustion of `ℝ` by the intervals
`[-n, n]`, which `x` first enters at the index `⌈|x|⌉₊`. -/
theorem exists_contMDiffMap_isProperMap_natCeil_abs_le :
    ∃ g : C^∞⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯, IsProperMap g ∧ (∀ x, (⌈|x|⌉₊ : ℝ) ≤ g x) ∧
      ∀ n : ℕ, {x | g x ≤ n} ⊆ Icc (-n : ℝ) n := by
  let K := CompactExhaustion.closedBall (0 : ℝ)
  obtain ⟨g, hg, hgK⟩ := K.exists_contMDiffMap_isProperMap 𝓘(ℝ)
  have hfind (x : ℝ) : K.find x = ⌈|x|⌉₊ := by simp [K]
  refine ⟨g, hg, fun x ↦ hfind x ▸ hgK x, fun n x hx ↦ ?_⟩
  rw [← Real.closedBall_zero_eq_Icc, ← CompactExhaustion.closedBall_apply, K.mem_iff_find_le]
  exact_mod_cast (hgK x).trans hx

/-! ### A bounded function is no exhaustion -/

/-- The sublevel `{arctan ≤ 2}` is all of `ℝ`, since `arctan < π / 2 < 2`. -/
theorem setOf_arctan_le_two : {x : ℝ | arctan x ≤ 2} = univ :=
  eq_univ_of_forall fun x ↦ (arctan_lt_pi_div_two x).le.trans (by linarith [pi_le_four])

/-- The bounded function `arctan` is not proper on `ℝ`. -/
theorem not_isProperMap_arctan : ¬ IsProperMap arctan := fun h ↦
  not_compactSpace_iff.2 inferInstance
    (h.compactSpace_of_isBounded_range (range_arctan ▸ Metric.isBounded_Ioo _ _))

end TauCeti
