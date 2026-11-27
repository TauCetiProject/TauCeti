/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Topology.PartitionOfUnity.Basic
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Smooth partitions of unity: pointwise sums and pullback regularity

This file collects facts about smooth partitions of unity `ρ : SmoothPartitionOfUnity ι I M s`.

First, two pointwise facts about the finite support `ρ.finsupport x` (derived from their
counterparts for `PartitionOfUnity` in `TauCeti.Topology.PartitionOfUnity.Basic`): every index
`i ∈ ρ.finsupport x` satisfies `x ∈ U i` for any cover `U` to which `ρ` is subordinate
(`SmoothPartitionOfUnity.IsSubordinate.mem_of_mem_finsupport`), and a weighted sum
`∑ i ∈ ρ.finsupport x, ρ i x • w i` whose summands `w i` all equal `v` is `v`
(`SmoothPartitionOfUnity.sum_finsupport_smul_eq_of_forall_eq`).

Second, gluing local smooth maps `g i : N → F` on another manifold `N` along a smooth map
`π : N → M` (for example, a product projection `(P × E) × ℂ → P`) produces the locally finite sum
`y ↦ ∑ᶠ i, ρ i (π y) • g i y`. `SmoothPartitionOfUnity.contMDiffAt_finsum_comp` proves that this
pulled-back sum is `C^n` at `y₀ : N` whenever `π` is `C^n` at `y₀` and every `g i` with
`π y₀ ∈ tsupport (ρ i)` is `C^n` at `y₀`. Unlike Mathlib's global `_root_.contMDiffAt_finsum`,
this requires only local regularity of `π` at `y₀` rather than global continuity of `π`.

## Main results

* `SmoothPartitionOfUnity.IsSubordinate.mem_of_mem_finsupport`: membership in a subordinate cover
  on `ρ.finsupport x`.
* `SmoothPartitionOfUnity.sum_finsupport_smul_eq_of_forall_eq`: collapsing a weighted sum over
  `ρ.finsupport x` when the summands agree.
* `SmoothPartitionOfUnity.contMDiffAt_finsum_comp`: local `C^n` regularity of a partition-of-unity
  sum pulled back along a `C^n` map `π : N → M`.
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace SmoothPartitionOfUnity

section Pointwise

variable {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {s : Set M}
  {ρ : SmoothPartitionOfUnity ι I M s} {x : M}

/-- If `ρ` is subordinate to `U` and the bump `ρ i` does not vanish at `x`, then `x ∈ U i`. -/
theorem IsSubordinate.mem_of_mem_finsupport {U : ι → Set M} (hρ : ρ.IsSubordinate U) {i : ι}
    (hi : i ∈ ρ.finsupport x) : x ∈ U i :=
  hρ.toPartitionOfUnity.mem_of_mem_finsupport hi

/-- At a point `x ∈ s`, a weighted sum `∑ i ∈ ρ.finsupport x, ρ i x • w i` whose summands with
`ρ i x ≠ 0` all equal `v` is `v`. -/
theorem sum_finsupport_smul_eq_of_forall_eq {A : Type*} [AddCommMonoid A] [Module ℝ A]
    (hx : x ∈ s) {w : ι → A} {v : A} (hw : ∀ i ∈ ρ.finsupport x, w i = v) :
    ∑ i ∈ ρ.finsupport x, ρ i x • w i = v :=
  ρ.toPartitionOfUnity.sum_finsupport_smul_eq_of_forall_eq hx hw

end Pointwise

/-- Local `C^n` regularity of a smooth partition-of-unity sum pulled back along a map `π : N → M`
that is `C^n` at `y₀`. Only the terms `g i` with `π y₀ ∈ tsupport (ρ i)` need be `C^n` at `y₀`. -/
theorem contMDiffAt_finsum_comp {ι E H M E' H' N F : Type*} {n : ℕ∞}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s)
    {π : N → M} {y₀ : N} {g : ι → N → F}
    (hπ : ContMDiffAt J I n π y₀)
    (hg : ∀ i, π y₀ ∈ tsupport (ρ i) → ContMDiffAt J 𝓘(ℝ, F) n (g i) y₀) :
    ContMDiffAt J 𝓘(ℝ, F) n (fun y ↦ ∑ᶠ i, ρ i (π y) • g i y) y₀ := by
  -- `_root_.contMDiffAt_finsum` requires global `LocallyFinite` on `N` (hence global continuity
  -- of `π`), whereas `hπ.continuousAt` with `eventually_finsupport_subset` is purely local.
  have hloc : (fun y ↦ ∑ᶠ i, ρ i (π y) • g i y) =ᶠ[𝓝 y₀]
      fun y ↦ ∑ i ∈ ρ.fintsupport (π y₀), ρ i (π y) • g i y := by
    filter_upwards [hπ.continuousAt.eventually (ρ.eventually_finsupport_subset (π y₀))] with y hy
    refine finsum_eq_sum_of_support_subset _ fun i hi ↦ hy ?_
    rw [ρ.mem_finsupport]
    exact fun h0 ↦ hi (by simp [h0])
  refine (ContMDiffAt.sum fun i hi ↦ ?_).congr_of_eventuallyEq hloc
  exact ((((ρ i).contMDiff.of_le (mod_cast le_top)).contMDiffAt).comp y₀ hπ).smul
    (hg i ((ρ.mem_fintsupport_iff (π y₀) i).1 hi))

end SmoothPartitionOfUnity

namespace BumpCovering

variable {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {s : Set M}

/-- A `BumpCovering` whose functions are `C^k` generates a `C^k` partition of unity. -/
theorem contMDiff_toPartitionOfUnity_of_contMDiff {k : ℕ∞ω} (f : BumpCovering ι M s)
    (hf : ∀ i, ContMDiff I 𝓘(ℝ) k (f i)) (i : ι) :
    ContMDiff I 𝓘(ℝ) k (f.toPartitionOfUnity i) :=
  (hf i).mul <| (contMDiff_finprod_cond fun j _ ↦ contMDiff_const.sub (hf j)) <| by
    simp only [Function.mulSupport_one_sub]
    exact f.locallyFinite

end BumpCovering
