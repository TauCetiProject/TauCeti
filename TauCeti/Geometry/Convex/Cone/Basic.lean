/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Prod

/-!
# Salience of images and products of cones, and the line spanned by a ray

Mathlib's `ConvexCone.Salient` records that a convex cone contains no line. This file proves the
two closure properties of salience that concern standard cone constructions: the image under an
injective linear map, and the product of two pointed cones. It also computes the dimension of the
linear span of the cone hull of a single nonzero vector, which is the one-dimensionality making
such a cone a ray, and the invariance of that dimension under multiplying a cone by the zero cone.
None of these statements involves a lattice, so they belong to the generic convex-cone API rather
than to any consumer of it.

## Main declarations

* `ConvexCone.Salient.map`: the image of a salient convex cone under an injective linear map is
  salient.
* `ConvexCone.Salient.prod`: a product of salient pointed cones is salient.
* `PointedCone.finrank_span_coe_hull_singleton`: the cone hull of a nonzero vector spans a line.
* `PointedCone.finrank_span_coe_prod_bot` and `PointedCone.finrank_span_coe_bot_prod`:
  multiplying a pointed cone by the zero cone leaves the dimension of the span of the cone
  unchanged.
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

variable {V V' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']

/-- The linear span of the cone hull of a nonzero vector is the line it spans, of dimension one.
Passing from the cone hull to the linear span is the scalar extension from the nonnegative reals
to the reals. -/
theorem finrank_span_coe_hull_singleton {x : V} (hx : x ≠ 0) :
    Module.finrank ℝ (Submodule.span ℝ ((hull ℝ {x} : PointedCone ℝ V) : Set V)) = 1 := by
  rw [Submodule.span_span_of_tower (Nonneg ℝ) ℝ, finrank_span_singleton hx]

/-- Multiplying a pointed cone by the zero cone leaves the dimension of its span unchanged: the
product is the image of the cone under the inclusion of the first factor. -/
theorem finrank_span_coe_prod_bot (p : PointedCone ℝ V) :
    Module.finrank ℝ (Submodule.span ℝ
        ((p.prod (⊥ : PointedCone ℝ V') : PointedCone ℝ (V × V')) : Set (V × V')))
      = Module.finrank ℝ (Submodule.span ℝ (p : Set V)) := by
  rw [Submodule.prod_coe, Submodule.span_prod_eq ℝ p.zero_mem (Submodule.zero_mem _),
    Submodule.bot_coe, Submodule.span_zero_singleton, ← Submodule.map_inl]
  exact (Submodule.equivMapOfInjective _ LinearMap.inl_injective
    (Submodule.span ℝ (p : Set V))).finrank_eq.symm

/-- Multiplying a pointed cone by the zero cone leaves the dimension of its span unchanged: the
product is the image of the cone under the inclusion of the second factor. -/
theorem finrank_span_coe_bot_prod (q : PointedCone ℝ V') :
    Module.finrank ℝ (Submodule.span ℝ
        (((⊥ : PointedCone ℝ V).prod q : PointedCone ℝ (V × V')) : Set (V × V')))
      = Module.finrank ℝ (Submodule.span ℝ (q : Set V')) := by
  rw [Submodule.prod_coe, Submodule.span_prod_eq ℝ (Submodule.zero_mem _) q.zero_mem,
    Submodule.bot_coe, Submodule.span_zero_singleton, ← Submodule.map_inr]
  exact (Submodule.equivMapOfInjective _ LinearMap.inr_injective
    (Submodule.span ℝ (q : Set V'))).finrank_eq.symm

end PointedCone
