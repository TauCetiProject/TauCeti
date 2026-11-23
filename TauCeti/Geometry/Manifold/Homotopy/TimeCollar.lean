/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Topology.Homotopy.Basic

/-!
# Collaring the time parameter of a homotopy

`ContinuousMap.Homotopy.exists_timeCollar` reparametrizes a continuous homotopy between `C^n`
maps to a map on `N × ℝ` that is `C^n` near `N × {0, 1}` and agrees with the endpoint maps there.
Its image stays in that of the original homotopy. This supplies endpoint collars for relative
smooth approximation without requiring finite-dimensional models or `IsManifold` instances.

The reparametrization clamps `3 * t - 1` to the unit interval, so the map is constant in time
for `t < 1 / 3` and `t > 2 / 3`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013,
  proof of Theorem 6.29.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace ContinuousMap.Homotopy

variable {E F H G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace H N] [TopologicalSpace M] [ChartedSpace G M]

/-- Reparametrizing time so that a homotopy `H` between `C^n` maps is `f₀` for `t < 1 / 3` and
`f₁` for `t > 2 / 3` gives a map `N × ℝ → M` with image in that of `H`, which is `C^n` on a
neighbourhood of `N × {0, 1}` and equal to `f₀` and `f₁` there. Smoothing it relative to
`N × {0, 1}` gives a `C^n` homotopy from `f₀` to `f₁`. -/
theorem exists_timeCollar {f₀ f₁ : C(N, M)} (H : f₀.Homotopy f₁) (n : ℕ∞)
    (hf₀ : ContMDiff I J n f₀) (hf₁ : ContMDiff I J n f₁) :
    ∃ H' : C(N × ℝ, M), range H' ⊆ range H ∧
      ∃ U ∈ 𝓝ˢ (univ ×ˢ {0, 1} : Set (N × ℝ)), ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) J n H' U ∧
      ∀ x, H' (x, 0) = f₀ x ∧ H' (x, 1) = f₁ x := by
  let c : ℝ → unitInterval := fun t ↦ projIcc 0 1 zero_le_one (3 * t - 1)
  have hc₀ {t : ℝ} (ht : t < 1 / 3) : c t = 0 := by
    simp only [c]
    rw [projIcc_of_le_left _ (by linarith), Set.Icc.mk_zero]
  have hc₁ {t : ℝ} (ht : 2 / 3 < t) : c t = 1 := by
    simp only [c]
    rw [projIcc_of_right_le _ (by linarith), Set.Icc.mk_one]
  let H' : C(N × ℝ, M) := ⟨fun p ↦ H (c p.2, p.1), by fun_prop⟩
  let U : Set (N × ℝ) := univ ×ˢ (Iio (1 / 3) ∪ Ioi (2 / 3))
  have hU : IsOpen U := isOpen_univ.prod (isOpen_Iio.union isOpen_Ioi)
  have hSU : (univ ×ˢ {0, 1} : Set (N × ℝ)) ⊆ U := prod_mono subset_rfl (by
    rintro t (rfl | rfl)
    · exact Or.inl (by norm_num)
    · exact Or.inr (by norm_num))
  refine ⟨H', range_subset_iff.2 fun p ↦ mem_range_self _, U, hU.mem_nhdsSet.2 hSU, ?_,
    fun x ↦ ⟨by simp [H', hc₀ (by norm_num : (0 : ℝ) < 1 / 3)],
      by simp [H', hc₁ (by norm_num : (2 / 3 : ℝ) < 1)]⟩⟩
  rintro ⟨x, t⟩ ⟨-, ht | ht⟩
  · have hev : (f₀ ∘ Prod.fst : N × ℝ → M) =ᶠ[𝓝 (x, t)] H' := by
      filter_upwards [(isOpen_univ.prod isOpen_Iio).mem_nhds (mem_prod.2 ⟨mem_univ x, ht⟩)]
        with p hp
      simp [H', hc₀ hp.2]
    exact ((hf₀.comp contMDiff_fst).contMDiffAt.congr_of_eventuallyEq hev.symm).contMDiffWithinAt
  · have hev : (f₁ ∘ Prod.fst : N × ℝ → M) =ᶠ[𝓝 (x, t)] H' := by
      filter_upwards [(isOpen_univ.prod isOpen_Ioi).mem_nhds (mem_prod.2 ⟨mem_univ x, ht⟩)]
        with p hp
      simp [H', hc₁ hp.2]
    exact ((hf₁.comp contMDiff_fst).contMDiffAt.congr_of_eventuallyEq hev.symm).contMDiffWithinAt

end ContinuousMap.Homotopy
