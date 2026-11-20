/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Uniform convergence through the supremum of the extended norm

A family of maps into a seminormed group converges uniformly on `s` exactly when the supremum
over `s` of the extended norm of the difference tends to zero. This file records the forward
direction, the form in which uniform convergence enters bounds on lower Lebesgue integrals.
-/

public section

open Filter
open scoped ENNReal Topology

variable {ι α X : Type*} [SeminormedAddCommGroup X] {l : Filter ι} {f : ι → α → X} {f₀ : α → X}
  {s : Set α}

/-- Uniform convergence on `s` makes the supremum over `s` of the extended norm of the difference
tend to zero. -/
theorem TendstoUniformlyOn.tendsto_iSup_enorm_sub (h : TendstoUniformlyOn f f₀ l s) :
    Tendsto (fun i => ⨆ x ∈ s, ‖f i x - f₀ x‖ₑ) l (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  filter_upwards [EMetric.tendstoUniformlyOn_iff.1 h ε hε] with i hi
  refine iSup₂_le fun x hx => ?_
  rw [← eDist_eq_eNorm_sub, edist_comm]
  exact (hi x hx).le
