/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Lipschitz bounds for interval limits

An eventual common time-Lipschitz bound passes from an interior pointwise limit to its
continuous extension at both endpoints. The convergence filter is arbitrary and nontrivial,
and the target can be a pseudometric space.
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

variable {ι Y : Type*} {l : Filter ι} [l.NeBot] [PseudoMetricSpace Y]

/-- An eventual common time-Lipschitz bound passes from an interior pointwise
limit to its continuous values at both endpoints. -/
theorem time_lipschitz_of_interior_tendsto
    {f : ι → ℝ → Y} {g : ℝ → Y} {a b L : ℝ} (hab : a < b)
    (hg : ContinuousOn g (Icc a b))
    (hconv : ∀ t ∈ Ioo a b, Tendsto (fun k ↦ f k t) l (𝓝 (g t)))
    (hL : ∀ᶠ k in l, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      dist (f k s) (f k t) ≤ L * |s - t|) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (g s) (g t) ≤ L * |s - t| := by
  have hdist : ContinuousOn (fun p : ℝ × ℝ ↦ dist (g p.1) (g p.2))
      (Icc a b ×ˢ Icc a b) := by
    have hfst : ContinuousOn (fun p : ℝ × ℝ ↦ g p.1) (Icc a b ×ˢ Icc a b) :=
      hg.comp continuousOn_fst (fun _ hp ↦ hp.1)
    have hsnd : ContinuousOn (fun p : ℝ × ℝ ↦ g p.2) (Icc a b ×ˢ Icc a b) :=
      hg.comp continuousOn_snd (fun _ hp ↦ hp.2)
    exact fun p hp ↦ Filter.Tendsto.dist (hfst p hp) (hsnd p hp)
  intro s hs t ht
  have hclosure : (s, t) ∈ closure (Ioo a b ×ˢ Ioo a b) := by
    rw [closure_prod_eq, closure_Ioo hab.ne]
    exact ⟨hs, ht⟩
  have hbound : ContinuousWithinAt (fun p : ℝ × ℝ ↦ L * |p.1 - p.2|)
      (Ioo a b ×ˢ Ioo a b) (s, t) := by fun_prop
  apply ContinuousWithinAt.closure_le hclosure
    ((hdist (s, t) ⟨hs, ht⟩).mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
    hbound
  intro p hp
  apply le_of_tendsto ((hconv p.1 hp.1).dist (hconv p.2 hp.2))
  exact hL.mono (fun k hk ↦ hk p.1 ⟨hp.1.1.le, hp.1.2.le⟩
    p.2 ⟨hp.2.1.le, hp.2.2.le⟩)

/-- A time-Lipschitz bound controls displacement under a backward clamp near `b`. -/
theorem dist_apply_min_sub_le {q : ℝ → Y} {a b L δ t : ℝ}
    (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hδlength : δ ≤ b - a) (ht : t ≤ b)
    (hq : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (q s) (q t) ≤ L * |s - t|) :
    dist (q t) (q (min t (b - δ))) ≤ L * δ := by
  by_cases hfar : t ≤ b - δ
  · simp only [min_eq_left hfar, dist_self]
    exact mul_nonneg hL hδ
  · have ht' : t ∈ Icc a b := ⟨by linarith, ht⟩
    have hs : b - δ ∈ Icc a b := ⟨by linarith, by linarith⟩
    have hdiff : |t - (b - δ)| ≤ δ := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    simpa only [min_eq_right (le_of_not_ge hfar)] using
      (hq t ht' (b - δ) hs).trans (mul_le_mul_of_nonneg_left hdiff hL)

end TauCeti
