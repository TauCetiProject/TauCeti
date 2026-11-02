/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Calculus.Deriv.LocallyFinite

/-!
# Smooth partitions of unity of the real line

The real line has a smooth partition of unity indexed by `ℤ` whose `k`-th function is supported
in `(k - 1, k + 1)` (`TauCeti.exists_smoothPartitionOfUnity_isSubordinate_Ioo_int`). Gluing
small constant multiples of its functions puts a positive `C¹` function with derivative bounded
by `1` below any positive continuous function
(`Continuous.exists_contDiff_pos_le_abs_deriv_le_one`).
-/

public section

open Set
open scoped Manifold

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
