/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.Cone.Alternative
public import Mathlib.Geometry.Convex.Cone.DualFinite
public import Mathlib.Data.Fintype.Option

/-!
# Algebraic separation and bipolarity for finitely generated cones

Tucker's theorem supplies a separating functional for a point outside a finitely
generated pointed cone. Applying it to the generators and the negative of the
point avoids any assumption that the cone is already known to be closed.

Consequently every finitely generated cone equals its algebraic bipolar for the
evaluation pairing. The statements hold over an arbitrary linearly ordered field
and in arbitrary dimension; no topology or salience is required.

## Provenance

Adapted from `Mei/Geometry/Convex/Cone/FiniteDuality.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`68536122a97fed8e87bc6870b9427151971b9ab2`, licensed under Apache 2.0.
-/

public section

namespace PointedCone

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] {C : PointedCone K V} {x : V}

/-- A point outside a finitely generated cone is strictly separated from it by
an algebraic linear functional that is nonnegative on the cone. -/
theorem _root_.Submodule.FG.exists_cone_dual_nonneg_and_lt_zero (hC : C.FG) (hx : x ∉ C) :
    ∃ f : Module.Dual K V, (∀ y ∈ C, 0 ≤ f y) ∧ f x < 0 := by
  classical
  obtain ⟨s, hs⟩ := hC
  let a : Option s → V := fun j => j.elim (-x) Subtype.val
  obtain ⟨c, f, hc, hsum, hf, hpos⟩ :=
    TauCeti.exists_nonneg_sum_smul_eq_zero_and_coeff_add_dual_pos_at (K := K) a none
  have hsC : (s : Set V) ⊆ C := by
    rw [← hs]
    exact Submodule.subset_span
  have hc0 : c none = 0 := by
    by_contra hne
    have hp : 0 < c none := lt_of_le_of_ne (hc none) (Ne.symm hne)
    have hbase : (∑ j : s, c (some j) • (j : V)) ∈ C :=
      C.sum_mem fun j _ => PointedCone.smul_mem C (hc (some j)) (hsC j.property)
    have heq : (∑ j : s, c (some j) • (j : V)) = c none • x := by
      have h := hsum
      simp only [Fintype.sum_option, a, Option.elim_none, Option.elim_some, smul_neg] at h
      exact (neg_add_eq_zero.mp h).symm
    apply hx
    apply (PointedCone.smul_mem_iff C hp).mp
    rw [← heq]
    exact hbase
  have hfC : ∀ y ∈ C, 0 ≤ f y := by
    have hfmem : f ∈ dual (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V).flip
        (s : Set V) := fun y hy => hf (some ⟨y, hy⟩)
    rw [← dual_hull, hull, hs] at hfmem
    exact fun _ hy => hfmem hy
  refine ⟨f, hfC, ?_⟩
  have h : 0 < -f x := by simpa only [hc0, zero_add, a, Option.elim_none, map_neg] using hpos
  exact neg_pos.mp h

/-- A finitely generated cone equals its algebraic bipolar under evaluation.
This statement does not require finite dimensionality or topological closedness. -/
@[simp]
theorem _root_.Submodule.FG.cone_dual_dual_flip_id (hC : C.FG) :
    dual (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V)
      (dual (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V).flip C) = C := by
  apply le_antisymm
  · intro x hx
    by_contra hxC
    obtain ⟨f, hf, hfx⟩ := hC.exists_cone_dual_nonneg_and_lt_zero hxC
    have hfmem : f ∈ dual (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V).flip C :=
      fun _ hy => hf _ hy
    exact (not_le_of_gt hfx) (hx hfmem)
  · exact subset_dual_dual

end PointedCone
