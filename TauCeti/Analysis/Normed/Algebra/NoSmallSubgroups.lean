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
# The units of a real normed algebra have no small subgroups

Let `A` be a real normed algebra, such as `ℝ`, `ℂ`, or an algebra of bounded operators. An element
`z ≠ 1` of `A` has a power at distance more than `1 / 2` from `1`: as long as `w` stays within
`1 / 2` of `1`, the identity `w² - 1 = 2 • (w - 1) + (w - 1)²` shows that squaring multiplies
the distance to `1` by at least `3 / 2`. Hence the only subgroup of `Aˣ` inside the closed ball
of radius `1 / 2` around `1` is trivial. For the unit circle alone,
Mathlib's `Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two` is the analogous statement; the
version here applies to characters with values in `ℂˣ` that need not be unitary.

For a continuous homomorphism `f` from a topological group `G` to `Aˣ`, the preimage of that ball
is a neighbourhood of `1`, and every subgroup of `G` inside it lies in the kernel of `f`. This is
how a continuous character of a group with arbitrarily small open subgroups, such as the units of
a nonarchimedean local field, is seen to be trivial on one of them.

## Main results

* `TauCeti.three_div_two_mul_norm_sub_one_le_norm_sq_sub_one`: if `‖w - 1‖ ≤ 1 / 2`, then squaring
  multiplies the distance to `1` by at least `3 / 2`.
* `TauCeti.eq_one_of_forall_norm_pow_sub_one_le`: an element all of whose powers lie within
  `1 / 2` of `1` is `1`.
* `ContinuousMonoidHom.exists_mem_nhds_one_forall_le_ker`: a continuous homomorphism into `Aˣ` is
  trivial on every subgroup contained in a suitable neighbourhood of `1`.
-/

public section

open Topology

namespace TauCeti

section

variable {A : Type*} [SeminormedRing A] [NormedAlgebra ℝ A]

/-- **Squaring pushes an element near `1` away from `1`.** If `‖w - 1‖ ≤ 1 / 2`, then
`‖w ^ 2 - 1‖ ≥ 3 / 2 * ‖w - 1‖`. This holds even in a real seminormed algebra. -/
theorem three_div_two_mul_norm_sub_one_le_norm_sq_sub_one {w : A} (hw : ‖w - 1‖ ≤ 1 / 2) :
    3 / 2 * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have hsq : w ^ 2 - 1 = (2 : ℝ) • (w - 1) + (w - 1) * (w - 1) := by
    rw [two_smul]
    noncomm_ring
  have h := norm_sub_norm_le ((2 : ℝ) • (w - 1)) (-((w - 1) * (w - 1)))
  simp only [norm_smul, Real.norm_ofNat, norm_neg, sub_neg_eq_add, ← hsq] at h
  nlinarith [norm_mul_le (w - 1) (w - 1), norm_nonneg (w - 1)]

end

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- **No small subgroups.** An element of a real normed algebra all of whose powers lie
within `1 / 2` of `1` is `1` itself. -/
theorem eq_one_of_forall_norm_pow_sub_one_le {z : A} (h : ∀ n : ℕ, ‖z ^ n - 1‖ ≤ 1 / 2) :
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

variable {G A : Type*} [Group G] [TopologicalSpace G] [NormedRing A] [NormedAlgebra ℝ A]

/-- **A continuous homomorphism into `Aˣ` kills every small subgroup.** For a continuous
homomorphism `f` from a topological group to the units of a real normed algebra, there is
a neighbourhood `N` of `1` such that every subgroup contained in `N` lies in the kernel of `f`. -/
theorem exists_mem_nhds_one_forall_le_ker (f : G →ₜ* Aˣ) :
    ∃ N ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ N → H ≤ f.ker := by
  -- Take for `N` the preimage of the open ball of radius `1 / 2` around `1`.
  refine ⟨(fun g ↦ ‖((f g : Aˣ) : A) - 1‖) ⁻¹' Set.Iio (1 / 2), ?_, fun H hH g hg ↦ ?_⟩
  · refine (isOpen_Iio.preimage ?_).mem_nhds (by simp)
    fun_prop
  · rw [MonoidHom.mem_ker]
    refine Units.ext (TauCeti.eq_one_of_forall_norm_pow_sub_one_le fun n ↦ ?_)
    have hn : ‖((f (g ^ n) : Aˣ) : A) - 1‖ < 1 / 2 := hH (H.pow_mem hg n)
    rw [map_pow, Units.val_pow_eq_pow_val] at hn
    exact hn.le

end ContinuousMonoidHom
