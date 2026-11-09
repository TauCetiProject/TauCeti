/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Convergence and squares near one

In a group with zero whose units form an open subspace, convergence to a nonzero element
ensures that the quotient by that element is eventually a square, provided the squares in the
unit group form a neighbourhood of one. Only separate continuity of multiplication is needed.

For commutative groups with zero, this preserves nonzero square classes under approximation.
-/

public section

open Filter
open scoped Topology

/-- If the squares in the unit group of a group with zero form a neighbourhood of one,
convergence to a nonzero element eventually gives nonzero values whose quotient by the limit is
a square. -/
theorem Filter.Tendsto.eventually_isSquare_div
    {X G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀]
    [SeparatelyContinuousMul G₀] [IsOpenUnits G₀]
    {f : X → G₀} {l : Filter X} {a : G₀} (hf : Tendsto f l (𝓝 a))
    (hsq : {u : G₀ˣ | IsSquare u} ∈ 𝓝 1) (ha : a ≠ 0) :
    ∀ᶠ z in l, f z ≠ 0 ∧ IsSquare (f z / a) := by
  have hmem : Units.val '' {u : G₀ˣ | IsSquare u} ∈ 𝓝 (a / a) := by
    rw [div_self ha]
    exact IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap.image_mem_nhds hsq
  filter_upwards [hf.div_const a hmem] with z ⟨u, hu, (heq : (u : G₀) = f z / a)⟩
  exact ⟨(div_ne_zero_iff.mp (heq ▸ u.ne_zero)).1, heq ▸ hu.map (Units.coeHom G₀)⟩
