/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Group.Units

/-!
# The units of a real normed division algebra have no small subgroups

Let `𝕜` be a normed division ring that is a normed algebra over `ℝ`, such as `ℝ` or `ℂ`. An element
`z ≠ 1` of `𝕜` has a power at distance more than `1 / 2` from `1`: as long as `w` stays within
`1 / 2` of `1`, squaring multiplies the distance by `‖w + 1‖ ≥ 3 / 2`. Hence the only subgroup of
`𝕜ˣ` inside the closed ball of radius `1 / 2` around `1` is trivial. For the unit circle alone,
Mathlib's `Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two` is the analogous statement; the
version here applies to characters with values in `ℂˣ` that need not be unitary.

For a continuous homomorphism `f` from a topological group `G` to `𝕜ˣ`, the preimage of that ball
is a neighbourhood of `1`, and every subgroup of `G` inside it lies in the kernel of `f`. This is
how a continuous character of a group with arbitrarily small open subgroups, such as the units of
a nonarchimedean local field, is seen to be trivial on one of them.

## Main results

* `TauCeti.three_div_two_mul_norm_sub_one_le_norm_sq_sub_one`: if `‖w - 1‖ ≤ 1 / 2`, then squaring
  multiplies the distance to `1` by at least `3 / 2`.
* `TauCeti.eq_one_of_forall_norm_pow_sub_one_le`: an element all of whose powers lie within
  `1 / 2` of `1` is `1`.
* `ContinuousMonoidHom.exists_mem_nhds_one_forall_le_ker`: a continuous homomorphism into `𝕜ˣ` is
  trivial on every subgroup contained in a suitable neighbourhood of `1`.
-/

public section

open Topology

namespace TauCeti

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [NormedAlgebra ℝ 𝕜]

/-- **Squaring pushes an element near `1` away from `1`.** If `‖w - 1‖ ≤ 1 / 2`, then
`‖w ^ 2 - 1‖ ≥ 3 / 2 * ‖w - 1‖`, because `w ^ 2 - 1 = (w - 1) * (w + 1)` and
`‖w + 1‖ ≥ ‖2‖ - ‖w - 1‖ ≥ 3 / 2`. -/
theorem three_div_two_mul_norm_sub_one_le_norm_sq_sub_one {w : 𝕜} (hw : ‖w - 1‖ ≤ 1 / 2) :
    3 / 2 * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have htwo : ‖(2 : 𝕜)‖ = 2 := by
    rw [← map_ofNat (algebraMap ℝ 𝕜) 2, norm_algebraMap', Real.norm_ofNat]
  have hadd : 3 / 2 ≤ ‖w + 1‖ := by
    have h := norm_sub_norm_le (2 : 𝕜) (-(w - 1))
    rw [norm_neg, sub_neg_eq_add, htwo] at h
    have heq : (2 : 𝕜) + (w - 1) = w + 1 := by rw [← one_add_one_eq_two]; abel
    rw [heq] at h
    linarith
  have hsq : w ^ 2 - 1 = (w - 1) * (w + 1) := by noncomm_ring
  rw [hsq, norm_mul]
  nlinarith [norm_nonneg (w - 1)]

/-- **No small subgroups.** An element of a real normed division algebra all of whose powers lie
within `1 / 2` of `1` is `1` itself. -/
theorem eq_one_of_forall_norm_pow_sub_one_le {z : 𝕜} (h : ∀ n : ℕ, ‖z ^ n - 1‖ ≤ 1 / 2) :
    z = 1 := by
  by_contra hz
  have hr : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  -- Along the powers `z ^ (2 ^ k)` the distance to `1` grows at least like `(3 / 2) ^ k`.
  have hgrow (k : ℕ) : (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ 2 ^ k - 1‖ := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc (3 / 2 : ℝ) ^ (k + 1) * ‖z - 1‖ = 3 / 2 * ((3 / 2) ^ k * ‖z - 1‖) := by ring
        _ ≤ 3 / 2 * ‖z ^ 2 ^ k - 1‖ := by gcongr
        _ ≤ ‖(z ^ 2 ^ k) ^ 2 - 1‖ :=
          three_div_two_mul_norm_sub_one_le_norm_sq_sub_one (h _)
        _ = ‖z ^ 2 ^ (k + 1) - 1‖ := by rw [← pow_mul, ← pow_succ]
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 : 1 / 2 < (3 / 2 : ℝ) ^ k * ‖z - 1‖ := (div_lt_iff₀ hr).mp hk
  exact (h1.trans_le (hgrow k)).not_ge (h _)

end TauCeti

namespace ContinuousMonoidHom

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [NormedDivisionRing 𝕜] [NormedAlgebra ℝ 𝕜]

/-- **A continuous homomorphism into `𝕜ˣ` kills every small subgroup.** For a continuous
homomorphism `f` from a topological group to the units of a real normed division algebra, there is
a neighbourhood `N` of `1` such that every subgroup contained in `N` lies in the kernel of `f`. -/
theorem exists_mem_nhds_one_forall_le_ker (f : G →ₜ* 𝕜ˣ) :
    ∃ N ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ N → H ≤ f.ker := by
  -- Take for `N` the preimage of the open ball of radius `1 / 2` around `1`.
  refine ⟨(fun g ↦ ‖((f g : 𝕜ˣ) : 𝕜) - 1‖) ⁻¹' Set.Iio (1 / 2), ?_, fun H hH g hg ↦ ?_⟩
  · refine (isOpen_Iio.preimage ?_).mem_nhds (by simp)
    fun_prop
  · rw [MonoidHom.mem_ker]
    refine Units.ext (TauCeti.eq_one_of_forall_norm_pow_sub_one_le fun n ↦ ?_)
    have hn : ‖((f (g ^ n) : 𝕜ˣ) : 𝕜) - 1‖ < 1 / 2 := hH (H.pow_mem hg n)
    rw [map_pow, Units.val_pow_eq_pow_val] at hn
    exact hn.le

end ContinuousMonoidHom
