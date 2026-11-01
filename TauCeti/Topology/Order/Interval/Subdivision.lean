/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Order.ProjIcc

/-!
# Continuous variation of clipped interval subdivisions

Mathlib's `Set.Icc.addNSMul` subdivides a closed interval into equally spaced steps, clipped
at the right endpoint. The subdivision depends continuously on its step size. If a positive
step size varies continuously, the sequence reaches the right endpoint locally uniformly
in the parameter. This stronger, neighbourhood-wise termination permits locally finite
compositions of transport maps; pointwise termination alone would not ensure continuity.
-/

public section

open Filter Set Topology

namespace Set.Icc

/-- Each point of the clipped subdivision varies continuously with its step size. -/
@[fun_prop]
theorem continuous_addNSMul {α : Type*} [AddCommGroup α] [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [ContinuousAdd α]
    {a b : α} (h : a ≤ b) (n : ℕ) :
    Continuous fun δ : α ↦ addNSMul h δ n :=
  continuous_projIcc.comp (continuous_const.add (continuous_id.nsmul n))

/-- Positive step sizes continuous at a parameter reach the right endpoint after a single
number of steps valid on a neighbourhood of that parameter. -/
theorem eventually_addNSMul_eq_right {X : Type*} [TopologicalSpace X]
    {a b : ℝ} (h : a ≤ b) {δ : X → ℝ} {x : X}
    (hδ : ContinuousAt δ x) (hpos : 0 < δ x) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ n ≥ N, addNSMul h (δ y) n = b := by
  obtain ⟨N, hN⟩ := Archimedean.arch (b - a) (half_pos hpos)
  refine ⟨N, ?_⟩
  filter_upwards [hδ.eventually (Ioi_mem_nhds (half_lt_self hpos))] with y hy n hn
  have hbound : b - a ≤ n • δ y :=
    hN.trans ((nsmul_le_nsmul_left (half_pos hpos).le hn).trans
      (nsmul_le_nsmul_right hy.le n))
  exact congrArg Subtype.val (projIcc_of_right_le h (sub_le_iff_le_add'.mp hbound))

end Set.Icc
