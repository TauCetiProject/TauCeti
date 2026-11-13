/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Separation.Connected

/-!
# No small subgroups in the units of a normed ring

Let `A` be a normed ring with `‖n • a‖ = ‖n‖ * ‖a‖` for integers `n`, such as `ℤ`, `ℝ`, `ℂ`,
or an algebra of bounded operators, and let `r < 1`. An element `z ≠ 1` of `A` has a power at
distance more than `r` from `1`: the identity `w² - 1 = 2 • (w - 1) + (w - 1)²` shows that squaring
multiplies the distance `‖w - 1‖` to `1` by at least `2 - ‖w - 1‖`, which is at least `2 - r > 1`
as long as `w` stays within `r` of `1`. Hence the only subgroup of `Aˣ` inside the closed ball
of radius `r` around `1` is trivial. For the unit circle alone,
Mathlib's `Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two` is the analogous statement; the
version here applies to characters with values in `ℂˣ` that need not be unitary.

Integer norm homogeneity is expressed by `NormSMulClass ℤ A`. It holds in every real normed
space, but also permits rings without a real scalar action. For a generic real normed space,
the instance can be supplied locally using `norm_zsmul` from
`Mathlib.Analysis.Normed.Module.Basic`:

```lean
have : NormSMulClass ℤ A :=
  ⟨fun n a ↦ by simpa only [Int.norm_cast_real] using norm_zsmul ℝ n a⟩
```

For a continuous homomorphism `f` from a topological group `G` to `Aˣ`, the preimage of such a
ball is a neighbourhood of `1`, and every subgroup of `G` inside it lies in the kernel of `f`.
This is how a continuous character of a group with arbitrarily small open subgroups, such as the
units of a nonarchimedean local field, is seen to be trivial on one of them.

## Main results

* `TauCeti.two_sub_norm_sub_one_mul_norm_sub_one_le_norm_sq_sub_one`: squaring multiplies the
  distance `‖w - 1‖` to `1` by at least `2 - ‖w - 1‖`.
* `TauCeti.eq_one_of_forall_norm_pow_sub_one_le`: an element all of whose powers lie within
  a fixed distance `r < 1` of `1` is `1`.
* `ContinuousMonoidHom.exists_mem_nhds_one_forall_le_ker`: a continuous homomorphism into `Aˣ` is
  trivial on every subgroup contained in a suitable neighbourhood of `1`.
* `ContinuousMonoidHom.isOpen_ker_of_compactSpace_of_totallyDisconnectedSpace`: a continuous
  homomorphism from a profinite group into `Aˣ` has open kernel.
-/

public section

open Topology

namespace TauCeti

section

variable {A : Type*} [SeminormedRing A] [NormSMulClass ℤ A]

/-- **Squaring pushes an element near `1` away from `1`.** Squaring multiplies the distance
`‖w - 1‖` to `1` by at least `2 - ‖w - 1‖`, a factor greater than `1` when `‖w - 1‖ < 1`. The
ring may be seminormed; its norm is homogeneous under integer scalar multiplication. -/
theorem two_sub_norm_sub_one_mul_norm_sub_one_le_norm_sq_sub_one (w : A) :
    (2 - ‖w - 1‖) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have hsq : w ^ 2 - 1 = (2 : ℤ) • (w - 1) + (w - 1) * (w - 1) := by
    rw [two_smul]
    noncomm_ring
  have h := norm_sub_norm_le ((2 : ℤ) • (w - 1)) (-((w - 1) * (w - 1)))
  norm_num only [norm_smul, Int.norm_eq_abs, norm_neg, sub_neg_eq_add, ← hsq] at h
  linarith [norm_mul_le (w - 1) (w - 1)]

end

variable {A : Type*} [NormedRing A] [NormSMulClass ℤ A]

/-- **No small subgroups.** In a normed ring whose norm is homogeneous under integer scalar
multiplication, an element all of whose powers lie within a fixed distance `r < 1` of `1` is
`1` itself. The bound `r < 1` cannot be relaxed to `r = 1`: in `ℝ`, all powers of `0` lie
within `1` of `1`. -/
theorem eq_one_of_forall_norm_pow_sub_one_le {z : A} {r : ℝ} (hr : r < 1)
    (h : ∀ n : ℕ, ‖z ^ n - 1‖ ≤ r) : z = 1 := by
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  -- Along the powers `z ^ (2 ^ k)` the distance to `1` grows at least like `(2 - r) ^ k`.
  have hgrow (k : ℕ) : (2 - r) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc (2 - r) ^ (k + 1) * ‖z - 1‖ = (2 - r) * ((2 - r) ^ k * ‖z - 1‖) := by ring
        _ ≤ (2 - r) * ‖z ^ (2 ^ k) - 1‖ := by gcongr; linarith
        _ ≤ (2 - ‖z ^ (2 ^ k) - 1‖) * ‖z ^ (2 ^ k) - 1‖ := by gcongr; exact h _
        _ ≤ ‖(z ^ (2 ^ k)) ^ 2 - 1‖ :=
          two_sub_norm_sub_one_mul_norm_sub_one_le_norm_sq_sub_one _
        _ = ‖z ^ (2 ^ (k + 1)) - 1‖ := by rw [← pow_mul, ← pow_succ]
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (r / ‖z - 1‖) (by linarith : 1 < 2 - r)
  exact ((div_lt_iff₀ hpos).mp hk |>.trans_le (hgrow k)).not_ge (h _)

end TauCeti

namespace ContinuousMonoidHom

variable {G A : Type*} [Group G] [TopologicalSpace G] [NormedRing A] [NormSMulClass ℤ A]

/-- **A continuous homomorphism into `Aˣ` kills every small subgroup.** For a continuous
homomorphism `f` from a group with a topology to the units of a normed ring whose norm is
homogeneous under integer scalar multiplication, there is a neighbourhood `N` of `1` such
that every subgroup contained in `N` lies in the kernel of `f`. -/
theorem exists_mem_nhds_one_forall_le_ker (f : G →ₜ* Aˣ) :
    ∃ N ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ N → H ≤ f.ker := by
  -- Take for `N` the preimage of the open ball of radius `1 / 2` around `1`.
  refine ⟨(fun g ↦ ‖(f g : A) - 1‖) ⁻¹' Set.Iio (1 / 2), ?_, fun H hH g hg ↦ ?_⟩
  · refine (isOpen_Iio.preimage ?_).mem_nhds (by simp)
    fun_prop
  · rw [MonoidHom.mem_ker]
    refine Units.ext (TauCeti.eq_one_of_forall_norm_pow_sub_one_le one_half_lt_one fun n ↦ ?_)
    have hn : ‖(f (g ^ n) : A) - 1‖ < 1 / 2 := hH (H.pow_mem hg n)
    rw [map_pow, Units.val_pow_eq_pow_val] at hn
    exact hn.le

/-- A continuous homomorphism from a profinite group to the units of a normed ring whose norm
is homogeneous under integer scalar multiplication has open kernel. -/
theorem isOpen_ker_of_compactSpace_of_totallyDisconnectedSpace
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (f : G →ₜ* Aˣ) :
    IsOpen (f.ker : Set G) := by
  obtain ⟨N, hN, hNker⟩ := f.exists_mem_nhds_one_forall_le_ker
  obtain ⟨U, hUN, hU, h1U⟩ := mem_nhds_iff.mp hN
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1U
  exact Subgroup.isOpen_mono (hNker H.toSubgroup (hH.trans hUN)) H.isOpen

end ContinuousMonoidHom
