/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.LocalInverse
public import TauCeti.Topology.Algebra.Group.NoSmallSubgroups

import TauCeti.Geometry.Lie.Basic
import TauCeti.Geometry.Lie.Interior

/-!
# Finite-dimensional real Lie groups have no small subgroups

Every finite-dimensional real Lie group `G` satisfies `TauCeti.HasNoSmallSubgroups G`.

Near `0` in the Lie algebra `LeftInvariantDerivation I G`, the local logarithm `lieLog` satisfies
`lieLog (lieExp X) = X` on some open ball `Metric.ball 0 R` (`eventually_lieLog_lieExp`), and near
`1` in `G` it satisfies `lieExp (lieLog g) = g` (`eventually_lieExp_lieLog`). Setting `r = R / 2`
and taking the identity neighbourhood `U` where `lieExp (lieLog g) = g` and `‖lieLog g‖ < r`, any
element `g` all of whose natural-number powers stay in `U` has `X = lieLog g` satisfying
`‖k • X‖ < r` for every `k : ℕ` by induction: `‖k • X‖ < r` and `‖X‖ < r` force
`‖(k + 1) • X‖ < 2 * r = R`, where `lieLog` inverts `lieExp ((k + 1) • X) = g ^ (k + 1) ∈ U`.
Archimedean unboundedness of `k • ‖X‖` then forces `X = 0` and `g = 1`.

As an immediate corollary, every continuous homomorphism from a profinite group into a
finite-dimensional real Lie group has open kernel (`TauCeti.Lie.isOpen_ker_of_lieGroup`).

## Main results

* `TauCeti.Lie.exists_mem_nhds_one_forall_pow_mem_imp_eq_one`: in a finite-dimensional real Lie
  group, some identity neighbourhood `U ∈ 𝓝 1` has `1` as the only element all of whose
  natural-number powers lie in `U`.
* `TauCeti.Lie.hasNoSmallSubgroups_of_lieGroup`: every finite-dimensional real Lie group has no
  small subgroups.
* `TauCeti.Lie.isOpen_ker_of_lieGroup`: every continuous homomorphism from a profinite group into
  a finite-dimensional real Lie group has open kernel.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Problem 20-8.
* T. Tao, *Hilbert's Fifth Problem and Related Topics*, AMS GSM 153 (2014), Proposition 1.2.2.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- In a finite-dimensional real Lie group, there is an identity neighbourhood `U ∈ 𝓝 1` such that
`1` is the only element all of whose natural-number powers lie in `U`. -/
theorem exists_mem_nhds_one_forall_pow_mem_imp_eq_one
    (I : ModelWithCorners ℝ E H) [LieGroup I ∞ G] :
    ∃ U ∈ 𝓝 (1 : G), ∀ g : G, (∀ n : ℕ, g ^ n ∈ U) → g = 1 := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  obtain ⟨R, hR, hlog_exp⟩ :=
    Metric.eventually_nhds_iff_ball.mp (eventually_lieLog_lieExp (I := I) (G := G))
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hlog_cont : ContinuousAt (lieLog (I := I) (G := G)) (1 : G) :=
    (contMDiffAt_lieLog_one (I := I) (G := G)).continuousAt
  have hball_nhds : ∀ᶠ g in 𝓝 (1 : G), ‖lieLog (I := I) (G := G) g‖ < r := by
    have hmem : Metric.ball (0 : LeftInvariantDerivation I G) r ∈ 𝓝 (lieLog (I := I) (1 : G)) := by
      simpa only [lieLog_one] using Metric.ball_mem_nhds (0 : LeftInvariantDerivation I G) hr
    exact Filter.mem_of_superset (hlog_cont.preimage_mem_nhds hmem) fun g hg ↦ by
      simpa [Metric.mem_ball, dist_zero_right] using hg
  let U : Set G :=
    {g : G | lieExp (lieLog (I := I) (G := G) g) = g ∧ ‖lieLog (I := I) (G := G) g‖ < r}
  have hU : U ∈ 𝓝 (1 : G) := (eventually_lieExp_lieLog (I := I) (G := G)).and hball_nhds
  refine ⟨U, hU, fun g hg ↦ ?_⟩
  let X : LeftInvariantDerivation I G := lieLog (I := I) (G := G) g
  have hg1 : lieExp X = g ∧ ‖X‖ < r := by simpa [U, X] using hg 1
  -- By induction on `k`, every natural multiple `k • X` stays inside the half-radius ball.
  have hnsmul_lt : ∀ k : ℕ, ‖k • X‖ < r := by
    intro k
    induction k with
    | zero => simpa using hr
    | succ k ih =>
      have hlt_R : ‖(k + 1) • X‖ < R := by
        calc ‖(k + 1) • X‖ = ‖k • X + X‖ := by rw [succ_nsmul]
          _ ≤ ‖k • X‖ + ‖X‖ := norm_add_le _ _
          _ < r + r := add_lt_add ih hg1.2
          _ = R := add_halves R
      have hmem_R : (k + 1) • X ∈ Metric.ball (0 : LeftInvariantDerivation I G) R := by
        simpa [Metric.mem_ball, dist_zero_right] using hlt_R
      have hexp_pow : lieExp ((k + 1) • X) = g ^ (k + 1) := by
        rw [lieExp_nsmul, hg1.1]
      have hlog_pow : lieLog (I := I) (G := G) (g ^ (k + 1)) = (k + 1) • X := by
        rw [← hexp_pow]
        exact hlog_exp ((k + 1) • X) hmem_R
      simpa only [hlog_pow] using (hg (k + 1)).2
  have hX0 : X = 0 := by
    by_contra hne
    have hpos : 0 < ‖X‖ := norm_pos_iff.mpr hne
    obtain ⟨k, hk⟩ := exists_nat_gt (r / ‖X‖)
    have hle : r < ‖k • X‖ := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]
      exact (div_lt_iff₀ hpos).mp hk
    exact (hnsmul_lt k).not_gt hle
  rw [← hg1.1, hX0, lieExp_zero]

/-- **Every finite-dimensional real Lie group has no small subgroups.** -/
theorem hasNoSmallSubgroups_of_lieGroup (I : ModelWithCorners ℝ E H) [LieGroup I ∞ G] :
    HasNoSmallSubgroups G :=
  HasNoSmallSubgroups.of_forall_pow_mem (exists_mem_nhds_one_forall_pow_mem_imp_eq_one I)

/-- Every continuous group homomorphism from a profinite group into a finite-dimensional real Lie
group has open kernel. -/
theorem isOpen_ker_of_lieGroup (I : ModelWithCorners ℝ E H) [LieGroup I ∞ G]
    {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [TotallyDisconnectedSpace P] (f : P →ₜ* G) :
    IsOpen (f.ker : Set P) :=
  f.isOpen_ker_of_hasNoSmallSubgroups (hasNoSmallSubgroups_of_lieGroup I)

end TauCeti.Lie
