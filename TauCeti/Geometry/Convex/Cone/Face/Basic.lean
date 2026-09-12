/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.LinearAlgebra.Prod

/-!
# The zero face of a salient cone, and faces of a product

Mathlib's `ConvexCone.Salient` records that a convex cone contains no line. This file records the
consequence of salience for the face lattice of a pointed cone: the zero cone is a face. It also
records that a face of a product of two cones is the product of its two projections.

## Main declarations

* `ConvexCone.Salient.bot_isFaceOf`: the zero cone is a face of a salient pointed cone.
* `PointedCone.IsFaceOf.eq_prod_map`: a face of a product of two pointed cones is the product of
  its images under the two coordinate projections.
-/

public section

namespace ConvexCone.Salient

variable {R V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup V]
  [Module R V] [NoZeroSMulDivisors R V] {C : PointedCone R V}

/-- The zero cone is a face of a salient pointed cone. -/
theorem bot_isFaceOf (hC : (C : ConvexCone R V).Salient) :
    (⊥ : PointedCone R V).IsFaceOf C := by
  refine ⟨bot_le, fun {x y a} hx hy ha hxy ↦ ?_⟩
  rw [Submodule.mem_bot] at hxy ⊢
  rw [eq_neg_of_add_eq_zero_right hxy] at hy
  -- A nonzero positive multiple of `x` whose negative is `y ∈ C` would be a line in `C`.
  have hzero : a • x = 0 := by
    by_contra h
    exact hC _ (C.smul_mem ha.le hx) h hy
  exact (eq_zero_or_eq_zero_of_smul_eq_zero hzero).resolve_left ha.ne'

end ConvexCone.Salient

namespace PointedCone.IsFaceOf

variable {R M M' : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [Module R M] [AddCommGroup M'] [Module R M'] {C : PointedCone R M} {C' : PointedCone R M'}
  {F : PointedCone R (M × M')}

/-- A face of a product of two pointed cones is the product of its images under the two coordinate
projections: a point of the product of the images already lies on the face, because it is a
summand of a point of the face. -/
-- Adapted from Mathlib's `PointedCone.Face.fst_prod_snd`, the same fact for the bundled face
-- lattice, whose defining equations are sealed outside Mathlib.
theorem eq_prod_map (hF : F.IsFaceOf (C.prod C')) :
    F = (F.map (LinearMap.fst R M M')).prod (F.map (LinearMap.snd R M M')) := by
  refine le_antisymm (fun x hx ↦ Submodule.mem_prod.2
    ⟨Submodule.mem_map.2 ⟨x, hx, rfl⟩, Submodule.mem_map.2 ⟨x, hx, rfl⟩⟩) fun x hx ↦ ?_
  obtain ⟨h1, h2⟩ := Submodule.mem_prod.1 hx
  obtain ⟨a, ha, ha1⟩ := Submodule.mem_map.1 h1
  obtain ⟨c, hc, hc2⟩ := Submodule.mem_map.1 h2
  -- The face contains `(x.1, a.2)` and `(c.1, x.2)`, whose sum is `x + (c.1, a.2)`.
  have hxa : (x.1, a.2) = a := Prod.ext ha1.symm rfl
  have hcx : (c.1, x.2) = c := Prod.ext rfl hc2.symm
  have hswap : (x.1, a.2) + (c.1, x.2) = x + (c.1, a.2) := by simp [Prod.ext_iff, add_comm]
  have hy : (x.1, a.2) ∈ F := by rw [hxa]; exact ha
  have hz : (c.1, x.2) ∈ F := by rw [hcx]; exact hc
  have hsum : x + (c.1, a.2) ∈ F := by rw [← hswap]; exact Submodule.add_mem _ hy hz
  refine hF.mem_of_add_mem_left ?_ ?_ hsum
  · exact Submodule.mem_prod.2 ⟨(Submodule.mem_prod.1 (hF.le hy)).1,
      (Submodule.mem_prod.1 (hF.le hz)).2⟩
  · exact Submodule.mem_prod.2 ⟨(Submodule.mem_prod.1 (hF.le hz)).1,
      (Submodule.mem_prod.1 (hF.le hy)).2⟩

end PointedCone.IsFaceOf
