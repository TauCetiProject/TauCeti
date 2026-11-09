/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact
import TauCeti.Analysis.Calculus.Deriv.LocallyFinite
import TauCeti.Topology.MetricSpace.Thickening

/-!
# Smooth partitions of unity of the real line

The real line has a smooth partition of unity indexed by `ℤ` whose `k`-th function is supported
in `(k - 1, k + 1)` (`TauCeti.exists_smoothPartitionOfUnity_isSubordinate_Ioo_int`). Gluing
small constant multiples of its functions puts a positive `C¹` function with derivative bounded
by `1` below any positive continuous function
(`Continuous.exists_contDiff_pos_le_abs_deriv_le_one`). Above any continuous function there is
a smooth function which is constant near each member of a locally finite family of pairwise
disjoint compact sets, with values there above prescribed constants
(`Continuous.exists_contDiff_lt_eventuallyEq_const`).
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

/-- A smooth partition of unity of `ℝ` by functions supported in `(k - 1, k + 1)`, `k ∈ ℤ`. -/
theorem exists_smoothPartitionOfUnity_isSubordinate_Ioo_int :
    ∃ ρ : SmoothPartitionOfUnity ℤ 𝓘(ℝ, ℝ) ℝ,
      ρ.IsSubordinate fun k : ℤ ↦ Ioo ((k : ℝ) - 1) (k + 1) :=
  SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℝ) isClosed_univ _ (fun _ ↦ isOpen_Ioo) fun x _ ↦
    mem_iUnion.2 ⟨⌊x⌋, by linarith [Int.floor_le x], by linarith [Int.lt_floor_add_one x]⟩

end TauCeti

open TauCeti in
/-- Below a positive continuous function `δ` on `ℝ` there is a positive `C¹` function `Ψ` with
`|Ψ'| ≤ 1`. -/
theorem Continuous.exists_contDiff_pos_le_abs_deriv_le_one {δ : ℝ → ℝ} (hδ : Continuous δ)
    (hδ0 : ∀ x, 0 < δ x) :
    ∃ Ψ : ℝ → ℝ, ContDiff ℝ 1 Ψ ∧ ∀ x, 0 < Ψ x ∧ Ψ x ≤ δ x ∧ |deriv Ψ x| ≤ 1 := by
  have hval {φ : ℤ → ℝ → ℝ} (hlf : LocallyFinite fun k ↦ Function.support (φ k)) (x : ℝ) :
      HasSum (fun k ↦ φ k x) (∑ᶠ k, φ k x) := by
    have hfin : Function.HasFiniteSupport fun k ↦ φ k x := hlf.point_finite x
    simpa [tsum_eq_finsum hfin] using
      (summable_of_hasFiniteSupport (L := SummationFilter.unconditional ℤ) hfin).hasSum
  obtain ⟨ρ, hρ⟩ := exists_smoothPartitionOfUnity_isSubordinate_Ioo_int
  have hρd (k : ℤ) : ContDiff ℝ 1 (ρ k) := (ρ k).contMDiff.contDiff.of_le (by exact_mod_cast le_top)
  have hρs (k : ℤ) : HasCompactSupport (ρ k) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) ((hρ k).trans Ioo_subset_Icc_self)
  -- On `[k - 1, k + 1]`, `δ ≥ m k > 0` and `|ρ' k| ≤ B k`.
  have hm (k : ℤ) : ∃ m > 0, ∀ y ∈ Icc ((k : ℝ) - 1) (k + 1), m ≤ δ y := by
    obtain ⟨y₀, -, hy₀⟩ := (isCompact_Icc (a := (k : ℝ) - 1) (b := k + 1)).exists_isMinOn
      (nonempty_Icc.2 (by linarith)) hδ.continuousOn
    exact ⟨δ y₀, hδ0 y₀, hy₀⟩
  choose m hm0 hm using hm
  have hB (k : ℤ) := ((hρd k).continuous_deriv le_rfl).bounded_above_of_compact_support
    (hρs k).deriv
  choose B hB using hB
  obtain ⟨w, hw0, s, hws, hs1⟩ := NNReal.exists_pos_sum_of_countable one_ne_zero ℤ
  have hw : HasSum (fun k ↦ (w k : ℝ)) s := NNReal.hasSum_coe.2 hws
  have hw0' (k : ℤ) : (0 : ℝ) < w k := NNReal.coe_pos.2 (hw0 k)
  have hs1' : (s : ℝ) ≤ 1 := by exact_mod_cast hs1.le
  -- The coefficients `c k ≤ m k` are small enough that `|c k * ρ' k| ≤ w k`.
  set c : ℤ → ℝ := fun k ↦ min (m k) (w k / (|B k| + 1)) with hc
  have hc0 (k : ℤ) : 0 < c k := lt_min (hm0 k) (div_pos (hw0' k) (by positivity))
  have hcB (k : ℤ) (y : ℝ) : |c k * deriv (ρ k) y| ≤ w k := by
    rw [abs_mul, abs_of_pos (hc0 k)]
    calc c k * |deriv (ρ k) y| ≤ w k / (|B k| + 1) * (|B k| + 1) :=
          mul_le_mul (min_le_right _ _) (((hB k) y).trans ((le_abs_self _).trans
            (le_add_of_nonneg_right zero_le_one))) (abs_nonneg _)
            (div_pos (hw0' k) (by positivity)).le
      _ = w k := div_mul_cancel₀ _ (by positivity)
  have hlf : LocallyFinite fun k ↦ Function.support fun y ↦ c k * ρ k y :=
    ρ.locallyFinite.subset fun k ↦ Function.support_mul_subset_right _ _
  have hd (k : ℤ) : Differentiable ℝ fun y ↦ c k * ρ k y :=
    ((hρd k).differentiable one_ne_zero).const_mul _
  refine ⟨fun y ↦ ∑ᶠ k, c k * ρ k y, ?_, fun x ↦ ⟨?_, ?_, ?_⟩⟩
  · have := ρ.contMDiff_finsum_smul (n := 1) (g := fun k _ ↦ c k) fun k x _ ↦ contMDiffAt_const
    simp only [smul_eq_mul] at this
    simp_rw [mul_comm (c _)]
    exact this.contDiff
  · obtain ⟨k, hk⟩ := ρ.exists_pos_of_mem (mem_univ x)
    exact lt_of_lt_of_le (mul_pos (hc0 k) hk) (le_hasSum (hval hlf x) k
      fun j _ ↦ mul_nonneg (hc0 j).le (ρ.nonneg j x))
  · have hρx : HasSum (fun k ↦ δ x * ρ k x) (δ x) := by
      have := (hval ρ.locallyFinite x).mul_left (δ x)
      rwa [ρ.sum_eq_one (mem_univ x), mul_one] at this
    refine hasSum_le (fun k ↦ ?_) (hval hlf x) hρx
    by_cases hk : ρ k x = 0
    · simp [hk]
    · exact mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (hm k x
        (Ioo_subset_Icc_self ((hρ k) (subset_tsupport _ hk))))) (ρ.nonneg k x)
  · have := (hlf.hasSum_deriv_finsum fun k ↦ hd k x).norm_le_of_bounded hw fun k ↦ by
      rw [deriv_const_mul _ ((hρd k).differentiable one_ne_zero).differentiableAt]
      exact hcB k x
    exact this.trans hs1'

open Filter Function Metric Topology in
/-- Let `K i` be pairwise disjoint compact subsets of `ℝ` forming a locally finite family. Above a
continuous function `G` there is a smooth function `F` which is constant on a neighbourhood of
each `K i`, with a value there above a prescribed constant `M i`. -/
theorem Continuous.exists_contDiff_lt_eventuallyEq_const {G : ℝ → ℝ} (hG : Continuous G)
    {ι : Type*} {K : ι → Set ℝ} (hK : ∀ i, IsCompact (K i)) (hdisj : Pairwise (Disjoint on K))
    (hlf : LocallyFinite K) (M : ι → ℝ) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ (∀ x, G x < F x) ∧
      ∀ i, ∃ c, M i < c ∧ ∀ᶠ x in 𝓝ˢ (K i), F x = c := by
  -- Neighbourhoods `V i ⊆ D i ⊆ W i ⊆ C i` of `K i`, the thickenings by `r i / 2` (open and
  -- closed) and by `r i` (open and closed). The `D i` form a locally finite family and the
  -- compact sets `C i` are pairwise disjoint.
  obtain ⟨δ, hδ, hδd⟩ := hlf.exists_cthickenings_pairwiseDisjoint hK hdisj
  set r : ι → ℝ := fun i ↦ min (δ i) 1
  have hr0 (i : ι) : 0 < r i := lt_min (hδ i) one_pos
  have hCd : Pairwise (Disjoint on fun i ↦ cthickening (r i) (K i)) := fun i j hij ↦
    (hδd hij).mono (cthickening_mono (min_le_left _ _) _) (cthickening_mono (min_le_left _ _) _)
  have hD : LocallyFinite fun i ↦ cthickening (r i / 2) (K i) :=
    hlf.cthickening (R := 1) fun i ↦ by linarith [min_le_right (δ i) 1]
  have hDW (i : ι) : cthickening (r i / 2) (K i) ⊆ thickening (r i) (K i) :=
    cthickening_subset_thickening' (hr0 i) (half_lt_self (hr0 i)) _
  -- The value `c i` near `K i` lies above `G` on `C i` and above `M i`.
  have hB (i : ι) : ∃ B, ∀ y ∈ cthickening (r i) (K i), G y ≤ B :=
    (hK i).cthickening.bddAbove_image hG.continuousOn |>.imp fun _ hB y hy ↦
      hB (mem_image_of_mem _ hy)
  choose B hB using hB
  set c : ι → ℝ := fun i ↦ max (M i + 1) (B i + 1)
  -- Glue the constraints `G < F`, and `F = c i` on `V i`, by a smooth partition of unity.
  obtain ⟨F, hF⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const 𝓘(ℝ, ℝ) (n := ⊤)
    (t := fun x ↦ Ioi (G x) ∩ ⋂ i, ⋂ (_ : x ∈ thickening (r i / 2) (K i)), {c i})
    (fun x ↦ (convex_Ioi _).inter <| convex_iInter fun i ↦ convex_iInter fun _ ↦
      convex_singleton _) fun x ↦ by
      by_cases hx : ∃ i, x ∈ cthickening (r i / 2) (K i)
      · -- Near a point of `D i`, only the constraint `F = c i` is active.
        obtain ⟨i, hi⟩ := hx
        refine ⟨c i, ?_⟩
        filter_upwards [isOpen_thickening.mem_nhds (hDW i hi)] with y hy
        have hyC := thickening_subset_cthickening _ _ hy
        refine ⟨mem_Ioi.2 ((hB i y hyC).trans_lt ((lt_add_one _).trans_le (le_max_right _ _))),
          mem_iInter₂.2 fun j hj ↦ ?_⟩
        obtain rfl : j = i := by
          by_contra hji
          exact (hCd hji).ne_of_mem
            (thickening_subset_cthickening_of_le (half_le_self (hr0 j).le) _ hj) hyC rfl
        rfl
      · -- Away from the closed union of the `D i`, only the constraint `G < F` is active.
        push Not at hx
        refine ⟨G x + 1, ?_⟩
        have hcl : IsClosed (⋃ i, cthickening (r i / 2) (K i)) :=
          hD.isClosed_iUnion fun _ ↦ isClosed_cthickening
        filter_upwards [hcl.isOpen_compl.mem_nhds (by simpa using hx),
          hG.continuousAt.eventually_lt continuousAt_const (lt_add_one (G x))] with y hy hyG
        refine ⟨hyG, mem_iInter₂.2 fun j hj ↦ ?_⟩
        exact absurd (mem_iUnion.2 ⟨j, thickening_subset_cthickening _ _ hj⟩) hy
  refine ⟨F, F.contMDiff.contDiff, fun x ↦ (hF x).1, fun i ↦
    ⟨c i, (lt_add_one _).trans_le (le_max_left _ _), ?_⟩⟩
  filter_upwards [isOpen_thickening.mem_nhdsSet.2 (self_subset_thickening (half_pos (hr0 i)) _)]
    with y hy
  exact mem_singleton_iff.1 (mem_iInter₂.1 (hF y).2 i hy)
