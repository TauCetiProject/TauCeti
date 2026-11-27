/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Region.Height.Lattice

/-!
# Checks: the lattice of height functions and flips of heights

On the unit hexagon, the six faces round `0`, with its tilings `T_a = highFlipEdges 0` and
`T_b = lowFlipEdges 0`:

* a height function with free tiling `T_a` has `H(e_k) = H(0) = H(−e_k) + 1`;
* lowering it at `0` by one gives a height function with free tiling `T_b`, and raising a height
  function with free tiling `T_b` at `0` by one gives one with free tiling `T_a`;
* the pointwise minimum of the two height functions related by the flip at `0` is the one of
  `T_b`, the maximum is the one of `T_a`, and they differ at `0` by one.
-/

public section

namespace TauCeti.Examples.LozengeHeightLatticeChecks

open TauCeti

/-- The unit hexagon: the six faces round `0`. -/
abbrev hexagon : Set TriFace := vertexFaces (0, 0)

/-- A height function on the hexagon with free tiling `T_a` has `H(e_k) = H(0)` and
`H(−e_k) = H(0) − 1`. -/
example {H : ℤ × ℤ → ℤ} (hH : IsHeightFunctionOn hexagon H)
    (hT : tilingOfHeightOn hexagon H = highFlipEdges (0, 0)) :
    H (1, 0) = H (0, 0) ∧ H (0, 1) = H (0, 0) ∧ H (1, 1) = H (0, 0) ∧
      H (-1, 0) = H (0, 0) - 1 ∧ H (0, -1) = H (0, 0) - 1 ∧ H (-1, -1) = H (0, 0) - 1 := by
  simpa using (hH.highFlipEdges_subset_tilingOfHeightOn_iff subset_rfl).1 hT.symm.subset

/-- Lowering at `0` a height function with free tiling `T_a` gives a height function with free
tiling `T_b`. -/
theorem update_sub_one_hexagon {H : ℤ × ℤ → ℤ} (hH : IsHeightFunctionOn hexagon H)
    (hT : tilingOfHeightOn hexagon H = highFlipEdges (0, 0)) :
    IsHeightFunctionOn hexagon (Function.update H (0, 0) (H (0, 0) - 1)) ∧
      tilingOfHeightOn hexagon (Function.update H (0, 0) (H (0, 0) - 1)) = lowFlipEdges (0, 0) := by
  obtain ⟨h₁, h₂⟩ := hH.update_sub_one subset_rfl hT.symm.subset
  refine ⟨h₁, ?_⟩
  rw [h₂, hT, Set.sdiff_self, Set.empty_union]

/-- Raising at `0` a height function with free tiling `T_b` gives a height function with free
tiling `T_a`. -/
example {H : ℤ × ℤ → ℤ} (hH : IsHeightFunctionOn hexagon H)
    (hT : tilingOfHeightOn hexagon H = lowFlipEdges (0, 0)) :
    IsHeightFunctionOn hexagon (Function.update H (0, 0) (H (0, 0) + 1)) ∧
      tilingOfHeightOn hexagon (Function.update H (0, 0) (H (0, 0) + 1)) =
        highFlipEdges (0, 0) := by
  obtain ⟨h₁, h₂⟩ := hH.update_add_one subset_rfl hT.symm.subset
  refine ⟨h₁, ?_⟩
  rw [h₂, hT, Set.sdiff_self, Set.empty_union]

/-- The minimum of the heights of `T_a` and of its flip is the height of `T_b`, the maximum is the
height of `T_a`, and the two differ at `0` by one. -/
example {H : ℤ × ℤ → ℤ} (hH : IsHeightFunctionOn hexagon H)
    (hT : tilingOfHeightOn hexagon H = highFlipEdges (0, 0)) :
    tilingOfHeightOn hexagon (H ⊓ Function.update H (0, 0) (H (0, 0) - 1)) = lowFlipEdges (0, 0) ∧
      tilingOfHeightOn hexagon (H ⊔ Function.update H (0, 0) (H (0, 0) - 1)) =
        highFlipEdges (0, 0) ∧
      H (0, 0) - Function.update H (0, 0) (H (0, 0) - 1) (0, 0) = 1 := by
  have hle : Function.update H (0, 0) (H (0, 0) - 1) ≤ H := fun u => by
    by_cases hu : u = (0, 0)
    · subst hu; simp
    · simp [Function.update_of_ne hu]
  refine ⟨?_, ?_, by simp⟩
  · rw [inf_eq_right.2 hle]
    exact (update_sub_one_hexagon hH hT).2
  · rw [sup_eq_left.2 hle, hT]

end TauCeti.Examples.LozengeHeightLatticeChecks
