/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Field

import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Continuous functions and open square classes

If the square subgroup of a topological field's unit group is open, a continuous function
that is nonzero at a point has locally constant square class near that point. This packages
the topological argument used to preserve nonzero represented values under approximation.
-/

public section

namespace TauCeti

open scoped Topology

/-- If the squares in the unit group of a topological field are open, then near a point where
a continuous function is nonzero, its value remains nonzero and in the same square class. -/
theorem _root_.ContinuousAt.eventually_isSquare_div_of_isOpen_squares
    {X K : Type*} [TopologicalSpace X]
    [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K]
    {f : X → K} {x : X} (hf : ContinuousAt f x)
    (hsq : IsOpen ((powMonoidHom 2 : Kˣ →* Kˣ).range : Set Kˣ))
    (hx : f x ≠ 0) :
    ∀ᶠ z in 𝓝 x, f z ≠ 0 ∧ IsSquare (f z / f x) := by
  let squareValues : Set K := Units.val '' (powMonoidHom 2 : Kˣ →* Kˣ).range
  have hsquareValues : IsOpen squareValues :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _ hsq
  have hone : (1 : K) ∈ squareValues := ⟨1, ⟨1, by simp⟩, rfl⟩
  have heventually : ∀ᶠ z in 𝓝 x, f z / f x ∈ squareValues :=
    (hf.div_const (f x)).eventually
      (hsquareValues.mem_nhds (by simpa [hx] using hone))
  filter_upwards [heventually] with z hz
  obtain ⟨u, ⟨y, hy⟩, hu⟩ := hz
  refine ⟨(div_ne_zero_iff.mp (hu ▸ u.ne_zero)).1, ⟨(y : K), ?_⟩⟩
  rw [← hu]
  simpa [pow_two] using congrArg Units.val hy.symm

end TauCeti
