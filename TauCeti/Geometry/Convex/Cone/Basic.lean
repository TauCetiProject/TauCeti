/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.LinearAlgebra.Prod

/-!
# Salience of images and products of cones, and the zero face

Mathlib's `ConvexCone.Salient` records that a convex cone contains no line. This file proves the
two closure properties of salience that concern standard cone constructions: the image under an
injective linear map, and the product of two pointed cones. It also records the one consequence of
salience for the face lattice: the zero cone is a face. None of these statements involves a
lattice, so all belong to the generic convex-cone API rather than to any consumer of it.

## Main declarations

* `ConvexCone.Salient.map`: the image of a salient convex cone under an injective linear map is
  salient.
* `ConvexCone.Salient.prod`: a product of salient pointed cones is salient.
* `PointedCone.bot_isFaceOf`: the zero cone is a face of a salient pointed cone.
-/

public section

namespace ConvexCone.Salient

variable {R V V' : Type*} [Semiring R] [PartialOrder R] [AddCommGroup V] [AddCommGroup V']
  [Module R V] [Module R V']

/-- The image of a salient convex cone under an injective linear map is salient. -/
theorem map {C : ConvexCone R V} {g : V →ₗ[R] V'} (hC : C.Salient)
    (hg : Function.Injective g) : (C.map g).Salient := by
  rintro _ ⟨x, hx, rfl⟩ hne hneg
  obtain ⟨y, hy, hgy⟩ := hneg
  have hyx : y = -x := hg (by rw [map_neg]; exact hgy)
  exact hC x hx (fun h ↦ hne (by simp [h])) (hyx ▸ hy)

/-- A product of salient pointed cones is salient. -/
theorem prod [IsOrderedRing R] {σ : PointedCone R V} {τ : PointedCone R V'}
    (hσ : (σ : ConvexCone R V).Salient) (hτ : (τ : ConvexCone R V').Salient) :
    ((σ.prod τ : PointedCone R (V × V')) : ConvexCone R (V × V')).Salient := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩ hne ⟨hnx, hny⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · exact hτ y hy (fun h ↦ hne (by simp [h])) hny
  · exact hσ x hx hx0 hnx

end ConvexCone.Salient

namespace PointedCone

variable {R V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup V]
  [Module R V] [NoZeroSMulDivisors R V] {C : PointedCone R V}

/-- The zero cone is a face of a salient pointed cone. A positive multiple of a point of the cone
can only be cancelled inside the cone when that point is zero, which is exactly salience. -/
theorem bot_isFaceOf (hC : (C : ConvexCone R V).Salient) :
    (⊥ : PointedCone R V).IsFaceOf C := by
  refine ⟨bot_le, fun {x y a} hx hy ha hxy ↦ ?_⟩
  rw [Submodule.mem_bot] at hxy ⊢
  rw [eq_neg_of_add_eq_zero_right hxy] at hy
  have hzero : a • x = 0 := by
    by_contra h
    exact hC _ (C.smul_mem ha.le hx) h hy
  exact (eq_zero_or_eq_zero_of_smul_eq_zero hzero).resolve_left ha.ne'

end PointedCone
