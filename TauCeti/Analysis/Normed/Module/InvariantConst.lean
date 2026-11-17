/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Maps invariant under a translation or a contraction

Let `u : V → X` be a map from a normed space to a Hausdorff space. Two kinds of invariance force
`u` to be constant.

* **Translations** (`Function.Periodic.apply_eq_of_tendsto`). If `u (z + t) = u z` for a nonzero `t`
  and `u` has a limit `y` at infinity, then `u` is constantly `y`: the points
  `z + n t` tend to infinity, and `u` is constant along them.
* **Contractions** (`TauCeti.apply_eq_of_forall_apply_add_smul_sub_eq`). If
  `u (c + a • (z - c)) = u z` for a scalar `a` with `‖a‖ < 1` and `u` is continuous at the fixed
  point `c`, then `u` is constantly `u c`: the iterates `c + aⁿ • (z - c)` tend to `c`.

For maps of the Riemann sphere `OnePoint ℂ` fixing `∞` these exclude translations and scalings of
modulus other than `1` from the reparametrizations that fix a nonconstant map.
-/

public section

open Filter Topology

variable {V X : Type*} [NormedAddCommGroup V] [TopologicalSpace X] [T2Space X] {u : V → X}

namespace Function.Periodic

/-- **A periodic map with a limit at infinity is constant.** If `u` is periodic with a nonzero
period `t`, that is `u (z + t) = u z`, and `u` tends to `y` along the filter of complements of
bounded sets, then `u` is constantly `y`. -/
theorem apply_eq_of_tendsto [NormedSpace ℝ V] {t : V} (hu : Function.Periodic u t) (ht : t ≠ 0)
    {y : X} (hy : Tendsto u (Bornology.cobounded V) (𝓝 y)) (z : V) : u z = y := by
  have hn : ∀ n : ℕ, u (z + (n : ℝ) • t) = u z := fun n ↦ by
    rw [Nat.cast_smul_eq_nsmul]
    exact hu.nsmul n z
  have hlim : Tendsto (fun n : ℕ ↦ z + (n : ℝ) • t) atTop (Bornology.cobounded V) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine tendsto_atTop_mono (fun n : ℕ ↦ ?_)
      ((tendsto_natCast_atTop_atTop.atTop_mul_const (norm_pos_iff.2 ht)).atTop_add
        (tendsto_const_nhds (x := -‖z‖)))
    have h := norm_sub_le (z + (n : ℝ) • t) z
    rw [add_sub_cancel_left, norm_smul, Real.norm_natCast] at h
    linarith
  have := hy.comp hlim
  simp only [Function.comp_def, hn] at this
  exact tendsto_nhds_unique tendsto_const_nhds this

end Function.Periodic

namespace TauCeti

/-- **A self-similar map is constant.** If `u (c + a • (z - c)) = u z` for all `z`, with
`‖a‖ < 1`, and `u` is continuous at the fixed point `c`, then `u` is constantly `u c`. -/
theorem apply_eq_of_forall_apply_add_smul_sub_eq {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V]
    {c : V} {a : 𝕜} (ha : ‖a‖ < 1) (hu : ∀ z, u (c + a • (z - c)) = u z)
    (huc : ContinuousAt u c) (z : V) : u z = u c := by
  have hn : ∀ n : ℕ, u (c + a ^ n • (z - c)) = u z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih, ← hu (c + a ^ n • (z - c)), add_sub_cancel_left, smul_smul, pow_succ']
  have hlim : Tendsto (fun n : ℕ ↦ c + a ^ n • (z - c)) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one ha).smul_const (z - c))
  have := huc.tendsto.comp hlim
  simp only [Function.comp_def, hn] at this
  exact tendsto_nhds_unique tendsto_const_nhds this

end TauCeti
