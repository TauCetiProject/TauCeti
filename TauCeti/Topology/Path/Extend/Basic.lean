/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path

/-!
# Properties along extended paths

Pointwise properties can be transferred between a path on `unitInterval` and its constant
endpoint extension on all of `ℝ`. This lets statements about the extended curve use properties
established on the original path. For the corresponding range equality, see `Path.extend_range`.
Away from the joining parameter, a concatenation locally agrees with its rescaled component.
-/

public section

open Set
open scoped Topology

/-- A property holds everywhere along an extended path exactly when it holds along the path. -/
theorem Path.forall_extend_iff {E : Type*} [TopologicalSpace E] {p q : E} (γ : Path p q)
    {P : E → Prop} : (∀ t : ℝ, P (γ.extend t)) ↔ ∀ t, P (γ t) := by
  rw [← Set.forall_mem_range, γ.extend_range, Set.forall_mem_range]

/-- Below the joining parameter, an extended concatenation locally equals its first piece. -/
theorem Path.eventuallyEq_extend_trans_of_lt_half {E : Type*} [TopologicalSpace E] {p q r : E}
    (γ : Path p q) (δ : Path q r) {t : ℝ} (ht : t < 1 / 2) :
    (γ.trans δ).extend =ᶠ[𝓝 t] fun x ↦ γ.extend (2 * x) := by
  filter_upwards [Iic_mem_nhds ht] with x hx
  exact γ.extend_trans_of_le_half δ hx

/-- Above the joining parameter, an extended concatenation locally equals its second piece. -/
theorem Path.eventuallyEq_extend_trans_of_half_lt {E : Type*} [TopologicalSpace E] {p q r : E}
    (γ : Path p q) (δ : Path q r) {t : ℝ} (ht : 1 / 2 < t) :
    (γ.trans δ).extend =ᶠ[𝓝 t] fun x ↦ δ.extend (2 * x - 1) := by
  filter_upwards [Ioi_mem_nhds ht] with x hx
  exact γ.extend_trans_of_half_le δ hx.le
