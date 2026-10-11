/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Convergence and open sets of squares

In a group with zero whose units form an open subspace, convergence to a nonzero element
ensures that the quotient by that element is eventually a square, provided the set of squares
in the unit group is open. Only separate continuity of multiplication is needed.

For commutative groups with zero, this preserves nonzero square classes under approximation.
-/

public section

open Filter
open scoped Topology

/-- If the squares in the unit group of a group with zero form an open set, convergence to a
nonzero element eventually gives nonzero values whose quotient by the limit is a square. -/
theorem Filter.Tendsto.eventually_isSquare_div_of_isOpen_squares
    {X G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀]
    [SeparatelyContinuousMul G₀] [IsOpenUnits G₀]
    {f : X → G₀} {l : Filter X} {a : G₀} (hf : Tendsto f l (𝓝 a))
    (hsq : IsOpen {u : G₀ˣ | IsSquare u}) (ha : a ≠ 0) :
    ∀ᶠ z in l, f z ≠ 0 ∧ IsSquare (f z / a) := by
  let squareValues : Set G₀ := Units.val '' {u : G₀ˣ | IsSquare u}
  have hsquareValues : IsOpen squareValues :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _ hsq
  have hone : (1 : G₀) ∈ squareValues := ⟨1, IsSquare.one, rfl⟩
  have heventually : ∀ᶠ z in l, f z / a ∈ squareValues :=
    (hf.div_const a).eventually
      (hsquareValues.mem_nhds (by simpa [ha] using hone))
  refine heventually.mono ?_
  rintro z ⟨u, hu, heq⟩
  exact ⟨(div_ne_zero_iff.mp (heq ▸ u.ne_zero)).1, heq ▸ hu.map (Units.coeHom G₀)⟩
