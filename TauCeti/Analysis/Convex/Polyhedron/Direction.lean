/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Face
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Directions of finite intersections of affine halfspaces

The direction of a nonempty polyhedron is the common kernel of the linear
parts of the inequalities that vanish on the whole polyhedron. This identifies
the tangent space without choosing an irredundant presentation, and allows
arbitrary offsets, unboundedness and lineality. At a point with exactly one
active inequality, the direction of the active face is the kernel of that
row restricted to the ambient affine subspace.

The argument uses `Convex.exists_mem_zero_iff_forall` to choose a point with
exactly the universally active constraints, and
`TauCeti.exists_pos_lineMap_neg_forall_le` to move a short distance in any
vector annihilated by those constraints.

## Attribution

Adapted from `Mei/Geometry/Convex/Polyhedron/Direction.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0).
Original author: Codex; original copyright: Mei contributors.

-/

public section

namespace AffineMap

open Set AffineSubspace

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Finite ι]

/-- The direction of a nonempty finite intersection of affine halfspaces is
the common kernel of the universally active linear parts. -/
theorem direction_affineSpan_setOf_forall_le (g : ι → (V →ᵃ[ℝ] ℝ))
    (hne : ({x | ∀ j, g j x ≤ 0} : Set V).Nonempty) :
    (affineSpan ℝ {x | ∀ j, g j x ≤ 0}).direction =
      ⨅ (j) (_ : ∀ x, (∀ k, g k x ≤ 0) → g j x = 0), (g j).linear.ker := by
  let P : Set V := {x | ∀ j, g j x ≤ 0}
  have hconv : Convex ℝ P := by
    simpa only [P, Set.ofPred_forall, Set.preimage, Set.mem_Iic] using
      convex_iInter (fun j => (convex_Iic (0 : ℝ)).affine_preimage (g j))
  obtain ⟨p, hp, hactive⟩ := hconv.exists_mem_zero_iff_forall hne g
    (fun j x hx => hx j)
  apply le_antisymm
  · refine le_iInf fun j => le_iInf fun hj => ?_
    rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro v ⟨x, hx, y, hy, rfl⟩
    exact LinearMap.mem_ker.mpr (by
      rw [(g j).linear_apply_vsub, hj x hx, hj y hy, vsub_self])
  · intro v hv
    have hvzero : ∀ j, g j p = 0 → (g j).linear v = 0 := by
      intro j hj
      have hvall : ∀ j, (∀ x, (∀ k, g k x ≤ 0) → g j x = 0) →
          (g j).linear v = 0 := by simpa only [Submodule.mem_iInf, LinearMap.mem_ker] using hv
      exact hvall j ((hactive j).mp hj)
    obtain ⟨ε, hε, hmove⟩ := TauCeti.exists_pos_lineMap_neg_forall_le g hp (x := v + p) (by
      intro j hj
      rw [← vadd_eq_add, (g j).map_vadd, hvzero j hj, hj]
      simp)
    have hdir := AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ P hmove) (subset_affineSpan ℝ P hp)
    have heq : lineMap p (v + p) (-ε) -ᵥ p = (-ε) • v := by
      simpa only [vsub_eq_sub, add_sub_cancel_right] using lineMap_vsub_left p (v + p) (-ε)
    rw [heq] at hdir
    exact (Submodule.smul_mem_iff _ (neg_ne_zero.mpr hε.ne')).mp hdir

/-- At a point where precisely one row is active, the direction of the active
face is the kernel of that row inside the ambient affine subspace. -/
theorem vectorSpan_active_eq (g : ι → (V →ᵃ[ℝ] ℝ)) (A : AffineSubspace ℝ V)
    (j : ι) {p : V} (hp : p ∈ A) (hpj : g j p = 0)
    (hstrict : ∀ l, l ≠ j → g l p < 0) :
    vectorSpan ℝ {x | x ∈ A ∧ (∀ l, g l x ≤ 0) ∧ g j x = 0} =
      A.direction ⊓ (g j).linear.ker := by
  let F : Set V := {x | x ∈ A ∧ (∀ l, g l x ≤ 0) ∧ g j x = 0}
  have hpF : p ∈ F := ⟨hp, fun l => by
    by_cases he : l = j
    · simp [he, hpj]
    · exact (hstrict l he).le, hpj⟩
  apply le_antisymm
  · rw [vectorSpan_def, Submodule.span_le]
    rintro v ⟨x, hx, y, hy, rfl⟩
    exact ⟨A.vsub_mem_direction hx.1 hy.1, LinearMap.mem_ker.mpr (by
      rw [(g j).linear_apply_vsub, hx.2.2, hy.2.2, vsub_self])⟩
  · rintro v ⟨hvA, hvj⟩
    have hpv : v + p ∈ A := A.vadd_mem_of_mem_direction hvA hp
    obtain ⟨ε, hε, he⟩ := TauCeti.exists_pos_lineMap_neg_forall_le g hpF.2.1
      (x := v + p) (by
        intro l hl
        have hlj : l = j := by
          by_contra hn
          exact (hstrict l hn).ne hl
        subst l
        rw [← vadd_eq_add, (g j).map_vadd, LinearMap.mem_ker.mp hvj, hpj]
        simp)
    have hm : lineMap p (v + p) (-ε) ∈ F := ⟨lineMap_mem _ hp hpv, he, by
      rw [(g j).apply_lineMap, ← vadd_eq_add v p, (g j).map_vadd,
        LinearMap.mem_ker.mp hvj, hpj]
      simp⟩
    have hv := vsub_mem_vectorSpan ℝ hm hpF
    have heq : lineMap p (v + p) (-ε) -ᵥ p = (-ε) • v := by
      simpa only [vsub_eq_sub, add_sub_cancel_right] using lineMap_vsub_left p (v + p) (-ε)
    rw [heq] at hv
    exact (Submodule.smul_mem_iff _ (neg_ne_zero.mpr hε.ne')).mp hv

end AffineMap
