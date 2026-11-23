/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Riccardo Brasca
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Local constant-speed metric curves

A real-parameter curve satisfying `dist (γ s) (γ t) = |s - t| * c` locally can be
normalized by its speed. At zero speed it is locally constant; at positive speed an affine
change of parameter makes it distance preserving. These metric facts let regularity and
speed arguments reduce to the unit-speed case without additional geometric assumptions.
-/

public section

open Set
open scoped Topology

namespace TauCeti

/-- A curve realizing the zero-speed distance identity on a neighbourhood of `t₀` agrees
locally with its value at `t₀`. -/
theorem eventuallyEq_const_of_dist_eq_mul_zero {M : Type*} [MetricSpace M] {γ : ℝ → M} {ε t₀ : ℝ}
    (hε : 0 < ε)
    (hdist : ∀ s ∈ Icc (t₀ - ε) (t₀ + ε), ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
      dist (γ s) (γ t) = |s - t| * 0) : γ =ᶠ[𝓝 t₀] fun _ ↦ γ t₀ := by
  have ht₀ : t₀ ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  filter_upwards [Icc_mem_nhds (by linarith : t₀ - ε < t₀)
    (by linarith : t₀ < t₀ + ε)] with t ht
  rw [← dist_eq_zero, hdist t ht t₀ ht₀, mul_zero]

/-- Rescaling time by a positive speed `c` and translating the centre `t₀` to zero turns
the local constant-speed distance identity into distance preservation on `[-ε * c, ε * c]`. -/
theorem dist_reparam_eq_abs_of_dist_eq_mul_abs {M : Type*} [PseudoMetricSpace M]
    {γ : ℝ → M} {ε c t₀ : ℝ}
    (hc : 0 < c)
    (hdist : ∀ s ∈ Icc (t₀ - ε) (t₀ + ε), ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
      dist (γ s) (γ t) = |s - t| * c) :
    ∀ s ∈ Icc (-(ε * c)) (ε * c), ∀ t ∈ Icc (-(ε * c)) (ε * c),
      dist (γ (s / c + t₀)) (γ (t / c + t₀)) = |s - t| := by
  have hmaps : ∀ s ∈ Icc (-(ε * c)) (ε * c), s / c + t₀ ∈ Icc (t₀ - ε) (t₀ + ε) := by
    intro s hs
    have hleft : -ε ≤ s / c := (le_div_iff₀ hc).mpr (by nlinarith [hs.1])
    have hright : s / c ≤ ε := (div_le_iff₀ hc).mpr hs.2
    exact ⟨by linarith, by linarith⟩
  intro s hs t ht
  have hsub : s / c + t₀ - (t / c + t₀) = (s - t) / c := by ring
  rw [hdist _ (hmaps s hs) _ (hmaps t ht), hsub, abs_div, abs_of_pos hc,
    div_mul_cancel₀ _ hc.ne']

end TauCeti
