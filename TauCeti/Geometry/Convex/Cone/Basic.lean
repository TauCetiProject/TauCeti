/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Prod
import Mathlib.Geometry.Convex.Cone.Dual

/-!
# Salience and functional-sign bounds for cones, and the line spanned by a ray

Mathlib's `ConvexCone.Salient` records that a convex cone contains no line. This file proves the
two closure properties of salience that concern standard cone constructions, the image under an
injective linear map and the product of two pointed cones, together with the salience of the cone
hull of a single vector and of the cone hull of a set on which some linear functional is positive.
It records the sign bounds behind that salience: a linear functional nonnegative (respectively
positive) on a set is nonnegative on its cone hull (respectively positive on the nonzero vectors
of it), and it gives a cone-hull inclusion for the image of a set under an indexing map, splitting
off one index. It also computes the dimension of the linear span of the cone hull of a single
nonzero vector, which is the one-dimensionality making such a cone a ray, and the invariance of
that dimension under multiplying a cone by the zero cone. None of these statements involves a
lattice, so they belong to the generic convex-cone API rather than to any consumer of it.

## Main declarations

* `ConvexCone.Salient.map`: the image of a salient convex cone under an injective linear map is
  salient.
* `ConvexCone.Salient.prod`: a product of salient pointed cones is salient.
* `PointedCone.salient_hull_singleton`: the cone hull of a single vector is salient.
* `PointedCone.apply_nonneg_of_mem_hull`: a linear functional nonnegative on a set is nonnegative
  on its cone hull.
* `PointedCone.apply_pos_of_mem_hull` and `PointedCone.salient_hull_of_forall_pos`: a linear
  functional positive on a set is positive on the nonzero vectors of its cone hull, which is
  therefore salient; `PointedCone.eq_zero_of_add_eq_zero_of_mem_hull` is the additive form.
* `PointedCone.hull_image_le_hull_insert`: the cone hull of the image of a set lies in the cone hull
  of the image of one index together with the image of the other members of the set.
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
  rintro _ ⟨x, hx, rfl⟩ hne ⟨y, hy, hgy⟩
  exact hC x hx (by rintro rfl; simp at hne) (hg (hgy.trans (map_neg g x).symm) ▸ hy)

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

section HullSalient

variable {R V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommGroup V] [Module R V] [NoZeroSMulDivisors R V]

/-- The cone hull of a single vector is salient. -/
theorem salient_hull_singleton (x : V) : (hull R {x} : ConvexCone R V).Salient := by
  rintro y hy hy0 hny
  obtain ⟨r, hr0, rfl⟩ := mem_hull_singleton.1 hy
  obtain ⟨t, ht0, ht⟩ := mem_hull_singleton.1 hny
  have hrt : (r + t) • x = 0 := by rw [add_smul, ht, add_neg_cancel]
  rcases eq_zero_or_eq_zero_of_smul_eq_zero hrt with h | rfl
  · simp [((add_eq_zero_iff_of_nonneg hr0 ht0).1 h).1] at hy0
  · simp at hy0

end HullSalient

section HullPos

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V] {s : Set V}
  {f : Module.Dual R V} {x : V}

section PartialOrder

variable [PartialOrder R] [IsOrderedRing R]

/-- A linear functional that is nonnegative on a set is nonnegative on its cone hull. -/
theorem apply_nonneg_of_mem_hull (hs : ∀ y ∈ s, 0 ≤ f y) (hx : x ∈ hull R s) : 0 ≤ f x := by
  have hf : f ∈ dual (Module.Dual.eval R V) (hull R s) := by
    rw [dual_hull]
    exact fun y hy => hs y hy
  exact hf hx

end PartialOrder

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- If a linear functional is positive on a set, then the only vector of its cone hull on which
the functional vanishes is zero. -/
theorem eq_zero_of_mem_hull_of_apply_eq_zero (hs : ∀ y ∈ s, 0 < f y) (hx : x ∈ hull R s)
    (h : f x = 0) : x = 0 := by
  have hs' : ∀ y ∈ s, 0 ≤ f y := fun y hy => (hs y hy).le
  induction hx using Submodule.span_induction with
  | mem x hx => exact ((hs x hx).ne' h).elim
  | zero => rfl
  | add x y hxs hys hx hy =>
    rw [map_add] at h
    have := (add_eq_zero_iff_of_nonneg (apply_nonneg_of_mem_hull hs' hxs)
      (apply_nonneg_of_mem_hull hs' hys)).mp h
    rw [hx this.1, hy this.2, add_zero]
  | smul c x hxs hx =>
    obtain ⟨c, hc⟩ := c
    simp only [Nonneg.mk_smul, map_smul, smul_eq_mul] at h ⊢
    rcases hc.eq_or_lt with rfl | hc
    · simp
    · rw [hx ?_, smul_zero]
      by_contra hne
      exact (mul_pos hc ((apply_nonneg_of_mem_hull hs' hxs).lt_of_ne' hne)).ne' h

/-- If a linear functional is positive on a set, then it is positive on every nonzero vector of
the cone hull of the set. -/
theorem apply_pos_of_mem_hull (hs : ∀ y ∈ s, 0 < f y) (hx : x ∈ hull R s) (hx₀ : x ≠ 0) :
    0 < f x :=
  (apply_nonneg_of_mem_hull (fun y hy => (hs y hy).le) hx).lt_of_ne
    fun h => hx₀ (eq_zero_of_mem_hull_of_apply_eq_zero hs hx h.symm)

end HullPos

section HullPosSalient

variable {R V : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] {s : Set V} {f : Module.Dual R V} {x y : V}

/-- If a linear functional is positive on a set, then the cone hull of the set is salient. -/
theorem salient_hull_of_forall_pos (hs : ∀ y ∈ s, 0 < f y) :
    (hull R s : ConvexCone R V).Salient := fun x hx hx₀ hnx => by
  have h₁ := apply_pos_of_mem_hull hs hx hx₀
  have h₂ := apply_pos_of_mem_hull hs hnx (neg_ne_zero.mpr hx₀)
  rw [map_neg] at h₂
  exact (neg_pos.mp h₂).not_gt h₁

/-- If a linear functional is positive on a set, then two vectors of the cone hull of the set that
add up to zero vanish. This is the salience of the hull in additive form. -/
theorem eq_zero_of_add_eq_zero_of_mem_hull (hs : ∀ y ∈ s, 0 < f y) (hx : x ∈ hull R s)
    (hy : y ∈ hull R s) (h : x + y = 0) : x = 0 := by
  by_contra hx₀
  exact salient_hull_of_forall_pos hs x hx hx₀ (neg_eq_of_add_eq_zero_right h ▸ hy)

end HullPosSalient

section HullInsert

variable {ι R V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommMonoid V] [Module R V]

/-- The cone hull of the image of a set under a family lies in the cone hull of the image of
one index together with the image of the other members of the set. -/
theorem hull_image_le_hull_insert (v : ι → V) (T : Set ι) (i : ι) :
    hull R (v '' T) ≤ hull R (insert (v i) (v '' (T \ {i}))) :=
  Submodule.span_mono (Set.image_insert_eq ▸ Set.image_mono (Set.subset_insert_sdiff_singleton i T))

end HullInsert

section HullSpan

variable {R V : Type*} [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
  [AddCommGroup V] [Module R V]

/-- The linear span of the cone hull of a nonzero vector is the line it spans, of dimension one.
Passing from the cone hull to the linear span extends scalars from the nonnegative elements of the
ordered division ring to the ring itself. -/
theorem finrank_span_coe_hull_singleton {x : V} (hx : x ≠ 0) :
    Module.finrank R (Submodule.span R ((hull R {x} : PointedCone R V) : Set V)) = 1 := by
  rw [Submodule.span_span_of_tower (Nonneg R) R, finrank_span_singleton hx]

end HullSpan

section Prod

variable {R V V' : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommMonoid V] [Module R V] [AddCommMonoid V'] [Module R V']

/-- Multiplying a pointed cone by the zero cone in the second factor leaves the dimension of its
span unchanged. In particular, a ray of the first factor remains one-dimensional in the product. -/
theorem finrank_span_coe_prod_bot (p : PointedCone R V) :
    Module.finrank R (Submodule.span R
        ((p.prod (⊥ : PointedCone R V') : PointedCone R (V × V')) : Set (V × V')))
      = Module.finrank R (Submodule.span R (p : Set V)) := by
  rw [Submodule.prod_coe, Submodule.span_prod_eq R p.zero_mem (Submodule.zero_mem _),
    Submodule.bot_coe, Submodule.span_zero_singleton, ← Submodule.map_inl]
  exact (Submodule.equivMapOfInjective _ LinearMap.inl_injective
    (Submodule.span R (p : Set V))).finrank_eq.symm

/-- Multiplying a pointed cone by the zero cone in the first factor leaves the dimension of its
span unchanged. In particular, a ray of the second factor remains one-dimensional in the product. -/
theorem finrank_span_coe_bot_prod (q : PointedCone R V') :
    Module.finrank R (Submodule.span R
        (((⊥ : PointedCone R V).prod q : PointedCone R (V × V')) : Set (V × V')))
      = Module.finrank R (Submodule.span R (q : Set V')) := by
  rw [Submodule.prod_coe, Submodule.span_prod_eq R (Submodule.zero_mem _) q.zero_mem,
    Submodule.bot_coe, Submodule.span_zero_singleton, ← Submodule.map_inr]
  exact (Submodule.equivMapOfInjective _ LinearMap.inr_injective
    (Submodule.span R (q : Set V'))).finrank_eq.symm

end Prod

end PointedCone

namespace LinearMap

variable {R V V' : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommMonoid V] [Module R V] [AddCommMonoid V'] [Module R V']

/-- A linear map sends the zero cone to the zero cone. -/
theorem mapsTo_bot_pointedCone (g : V →ₗ[R] V') :
    Set.MapsTo g (⊥ : PointedCone R V) (⊥ : PointedCone R V') := by
  simp [Set.MapsTo]

end LinearMap
