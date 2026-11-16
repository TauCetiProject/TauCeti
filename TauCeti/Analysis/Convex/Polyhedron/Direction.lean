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
arbitrary offsets, unboundedness and lineality. At a point with a prescribed set of
active inequalities, the direction of the active face is the common kernel of
those rows restricted to the ambient affine subspace.

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

namespace TauCeti

open Set AffineSubspace AffineMap

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Finite ι]

/-- At a point where precisely the rows in `I` are active, the direction of the
active face is their common kernel inside the ambient affine subspace. -/
theorem vectorSpan_setOf_active_eq (g : ι → (V →ᵃ[ℝ] ℝ)) (A : AffineSubspace ℝ V)
    (I : Set ι) {p : V} (hp : p ∈ A) (hpI : ∀ l ∈ I, g l p = 0)
    (hstrict : ∀ l, l ∉ I → g l p < 0) :
    vectorSpan ℝ {x | x ∈ A ∧ (∀ l, g l x ≤ 0) ∧ ∀ l ∈ I, g l x = 0} =
      A.direction ⊓ ⨅ l ∈ I, (g l).linear.ker := by
  let F : Set V := {x | x ∈ A ∧ (∀ l, g l x ≤ 0) ∧ ∀ l ∈ I, g l x = 0}
  have hpF : p ∈ F := ⟨hp, fun l => by
    by_cases hl : l ∈ I
    · exact (hpI l hl).le
    · exact (hstrict l hl).le, hpI⟩
  apply le_antisymm
  · rw [vectorSpan_def, Submodule.span_le]
    rintro v ⟨x, hx, y, hy, rfl⟩
    refine ⟨A.vsub_mem_direction hx.1 hy.1, ?_⟩
    refine (Submodule.mem_iInf _).mpr fun l => (Submodule.mem_iInf _).mpr fun hl =>
      LinearMap.mem_ker.mpr ?_
    rw [(g l).linear_apply_vsub, hx.2.2 l hl, hy.2.2 l hl, vsub_self]
  · rintro v ⟨hvA, hvI⟩
    have hvzero : ∀ l ∈ I, (g l).linear v = 0 := fun l hl =>
      LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hvI l) hl)
    have hpv : v + p ∈ A := A.vadd_mem_of_mem_direction hvA hp
    obtain ⟨ε, hε, he⟩ := TauCeti.exists_pos_lineMap_neg_forall_le g hpF.2.1
      (x := v + p) (by
        intro l hl
        have hlI : l ∈ I := by
          by_contra hn
          exact (hstrict l hn).ne hl
        rw [← vadd_eq_add, (g l).map_vadd, hvzero l hlI, hpI l hlI]
        simp)
    have hm : lineMap p (v + p) (-ε) ∈ F := ⟨lineMap_mem _ hp hpv, he, by
      intro l hl
      rw [(g l).apply_lineMap, ← vadd_eq_add v p, (g l).map_vadd,
        hvzero l hl, hpI l hl]
      simp⟩
    have hv := vsub_mem_vectorSpan ℝ hm hpF
    have heq : lineMap p (v + p) (-ε) -ᵥ p = (-ε) • v := by
      simpa only [vsub_eq_sub, add_sub_cancel_right] using lineMap_vsub_left p (v + p) (-ε)
    rw [heq] at hv
    exact (Submodule.smul_mem_iff _ (neg_ne_zero.mpr hε.ne')).mp hv

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
  let I : Set ι := {j | ∀ x, (∀ k, g k x ≤ 0) → g j x = 0}
  have hface : {x | x ∈ (⊤ : AffineSubspace ℝ V) ∧
      (∀ l, g l x ≤ 0) ∧ ∀ l ∈ I, g l x = 0} = P := by
    ext x
    exact ⟨fun hx => hx.2.1, fun hx => ⟨by simp, hx, fun j hj => hj x hx⟩⟩
  have heq := vectorSpan_setOf_active_eq g ⊤ I (by simp)
    (fun j hj => hj p hp) (fun j hj =>
      lt_of_le_of_ne (hp j) (fun he => hj ((hactive j).mp he)))
  rw [hface] at heq
  simpa only [direction_top, top_inf_eq, I, mem_ofPred_eq, direction_affineSpan] using heq

/-- At a point where precisely one row is active, the direction of the active
face is the kernel of that row inside the ambient affine subspace. -/
theorem vectorSpan_active_eq (g : ι → (V →ᵃ[ℝ] ℝ)) (A : AffineSubspace ℝ V)
    (j : ι) {p : V} (hp : p ∈ A) (hpj : g j p = 0)
    (hstrict : ∀ l, l ≠ j → g l p < 0) :
    vectorSpan ℝ {x | x ∈ A ∧ (∀ l, g l x ≤ 0) ∧ g j x = 0} =
      A.direction ⊓ (g j).linear.ker := by
  simpa using vectorSpan_setOf_active_eq g A {j} hp (by simpa using hpj)
    (by simpa using hstrict)

end TauCeti
