/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed immersions over a base

Mathlib's `IsClosedImmersion.lift` factors a scheme morphism through a closed immersion
when the defining ideal vanishes on the source. The factor remains over the same base.
This file packages that lift in `Over S`, for use with structure maps of group schemes.
Sections over a base with at most one point are also closed immersions.

A closed immersion also preserves the height of every point for the specialization order
(`AlgebraicGeometry.Scheme.Hom.height_apply_eq_height`): the closure of a point of the source is
carried homeomorphically onto the closure of its image. So the dimension of the closure of a point
can be computed in a closed subscheme or in the ambient scheme alike.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

variable {S : Scheme.{u}} {X Y Z : Over S}

/-- A section over a base with at most one point is a closed immersion. -/
instance isClosedImmersion_section [Subsingleton S] (x : Over.mk (𝟙 S) ⟶ X) :
    IsClosedImmersion x.left :=
  isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)

/-- Factor a morphism over `S` through a closed immersion over `S`, when the defining ideal
of the immersion vanishes on the morphism. -/
noncomputable def closedImmersionOverLift (i : X ⟶ Y) (f : Z ⟶ Y)
    [IsClosedImmersion i.left] (h : i.left.ker ≤ f.left.ker) : Z ⟶ X :=
  Over.homMk (IsClosedImmersion.lift i.left f.left h) (by
    rw [← i.w, ← Category.assoc, IsClosedImmersion.lift_fac, f.w])

/-- The underlying scheme morphism of the lift is Mathlib's closed-immersion lift. -/
@[simp]
theorem closedImmersionOverLift_left (i : X ⟶ Y) (f : Z ⟶ Y)
    [IsClosedImmersion i.left] (h : i.left.ker ≤ f.left.ker) :
    (closedImmersionOverLift i f h).left = IsClosedImmersion.lift i.left f.left h := (rfl)

/-- The lift factors the original morphism over the base. -/
@[reassoc (attr := simp)]
theorem closedImmersionOverLift_comp (i : X ⟶ Y) (f : Z ⟶ Y)
    [IsClosedImmersion i.left] (h : i.left.ker ≤ f.left.ker) :
    closedImmersionOverLift i f h ≫ i = f := by
  ext
  simp

end TauCeti

namespace AlgebraicGeometry.Scheme.Hom

/-- A closed immersion preserves the height of points for the specialization order, that is, the
dimension of the closure of a point: the specializations of `f x` all lie in the closed image of
`f`, and `f` is an embedding. -/
@[simp]
theorem height_apply_eq_height {X Y : Scheme} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    Order.height (f x) = Order.height x := by
  have hemb := f.isClosedEmbedding
  have hle : ∀ a b : X, f a ≤ f b ↔ a ≤ b := fun a b ↦ hemb.isInducing.specializes_iff
  have hmono : StrictMono f := fun a b hab ↦ by
    simpa only [lt_iff_le_not_ge, hle] using hab
  refine (Order.height_eq_of_strictMono f hmono (fun a b hb ↦ ?_) x).symm
  obtain ⟨a', rfl⟩ : b ∈ Set.range f := hemb.isClosed_range.closure_subset
    (closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self a))
      (specializes_iff_mem_closure.mp hb.le))
  exact ⟨a', by simpa only [lt_iff_le_not_ge, hle] using hb, rfl⟩

end AlgebraicGeometry.Scheme.Hom
