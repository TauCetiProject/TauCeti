/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import TauCeti.Geometry.Convex.ConvexSpace.Defs

/-!
# Barycenters of faces under maps of vertices

Mathlib's `Convexity.StdSimplex.subBarycenter S hS` is the barycenter of the face of a standard
simplex spanned by a nonempty finite set `S` of vertices. This file records that a map of
vertices that is injective on `S`, acting on the standard simplex by `Convexity.StdSimplex.map`,
sends the barycenter of the face spanned by `S` to the barycenter of the face spanned by the image
of `S`, both for `Finset.image` and, in the case of an embedding, for `Finset.map`. For instance,
the inclusion of a facet of the standard simplex sends barycenters of faces of the facet to
barycenters of the corresponding faces of the simplex, which is how barycentric subdivision
restricts to faces. Moreover, monotone maps out of a finite nonempty linear order are determined by
their action on `Convexity.StdSimplex.barycenter`
(`Convexity.StdSimplex.eq_of_monotone_barycenter_map_eq`).
-/

public section

namespace Convexity.StdSimplex

variable {K M N : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A map of vertices that is injective on `S` sends the barycenter of the face spanned by `S`
to the barycenter of the face spanned by the image of `S`. -/
lemma map_subBarycenter_of_injOn [DecidableEq N] {f : M → N} {S : Finset M}
    (hf : Set.InjOn f S) (hS : S.Nonempty) :
    (subBarycenter (K := K) S hS).map f = subBarycenter (S.image f) (hS.image f) := by
  ext n
  simp [weights_subBarycenter, Finsupp.mapDomain_finsetSum, Finset.sum_image hf,
    Finset.card_image_of_injOn hf]

/-- An injective map of vertices sends the barycenter of the face spanned by `S` to the
barycenter of the face spanned by the image of `S`. -/
@[simp]
lemma map_subBarycenter (f : M ↪ N) (S : Finset M) (hS : S.Nonempty) :
    (subBarycenter (K := K) S hS).map f = subBarycenter (S.map f) hS.map := by
  classical
  simp_rw [Finset.map_eq_image]
  exact map_subBarycenter_of_injOn f.injective.injOn hS

/-- Two monotone maps out of a finite nonempty linear order into a partial order are equal whenever
they push `StdSimplex.barycenter` forward to the same point. -/
lemma eq_of_monotone_barycenter_map_eq [Fintype M] [Nonempty M] [LinearOrder M]
    [PartialOrder N] {f₁ f₂ : M → N} (hf₁ : Monotone f₁) (hf₂ : Monotone f₂)
    (h : (barycenter (K := K) (M := M)).map f₁ = (barycenter (K := K) (M := M)).map f₂) :
    f₁ = f₂ :=
  eq_of_monotone_map_eq_of_weights_ne_zero hf₁ hf₂
    (fun _ ↦ by
      rw [weights_barycenter_apply]
      exact inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero))
    h

end Convexity.StdSimplex
