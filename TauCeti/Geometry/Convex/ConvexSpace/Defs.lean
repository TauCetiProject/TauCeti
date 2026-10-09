/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Faces of the standard simplex

Complements to Mathlib's `Convexity.StdSimplex` about the maps `StdSimplex.map f` along injective
maps `f`, which embed a standard simplex as a face of a larger one.  Such a map keeps the weights
of a point, so it is injective.  For `f = j.succAbove` its image is the facet on which the `j`-th
weight vanishes.  Two facets, opposite `j < k`, meet in the codimension-two face opposite both:
a common point of the two facets comes from that face through both composites of face maps, the
two sides of the simplicial identity `SimplexCategory.δ_comp_δ`.
-/

public section

namespace Convexity.StdSimplex

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {X Y : Type*}

/-- Along an injective map, the weight at the image of a point is the weight at that point. -/
theorem weights_map_apply_of_injective {f : X → Y} (hf : f.Injective) (x : StdSimplex R X)
    (a : X) : (x.map f).weights (f a) = x.weights a :=
  Finsupp.mapDomain_apply_of_injective hf _ _

/-- The map of standard simplices along an injective map is injective. -/
theorem map_injective {f : X → Y} (hf : f.Injective) : (map (R := R) f).Injective := by
  intro x y h
  ext a
  rw [← weights_map_apply_of_injective hf, h, weights_map_apply_of_injective hf]

/-- A point of a standard simplex lies on the facet opposite `j` exactly when its `j`-th weight
vanishes. -/
theorem mem_range_map_succAbove_iff {n : ℕ} (j : Fin (n + 1)) (x : StdSimplex R (Fin (n + 1))) :
    x ∈ Set.range (map (R := R) j.succAbove) ↔ x.weights j = 0 := by
  rw [mem_range_map_iff, Fin.range_succAbove]
  simp

/-- The `j`-th weight vanishes on the facet opposite `j`. -/
theorem weights_map_succAbove_self {n : ℕ} (j : Fin (n + 1)) (x : StdSimplex R (Fin n)) :
    (x.map j.succAbove).weights j = 0 :=
  (mem_range_map_succAbove_iff j _).1 ⟨x, rfl⟩

/-- The facets of a standard simplex opposite `j < k` meet in the codimension-two face opposite
both: a common point is the image of a point `w` of that face, and the corresponding points of
the two facets are the images of `w` under the face maps given by the simplicial identity. -/
theorem exists_map_succAbove_of_map_succAbove_eq {n : ℕ} {j k : Fin (n + 2)} (hjk : j < k)
    {y z : StdSimplex R (Fin (n + 1))} (h : y.map j.succAbove = z.map k.succAbove) :
    ∃ w : StdSimplex R (Fin n),
      y = w.map (k.pred (Fin.ne_zero_of_lt hjk)).succAbove ∧
        z = w.map (j.castPred (Fin.ne_last_of_lt hjk)).succAbove := by
  have hy : y.weights (k.pred (Fin.ne_zero_of_lt hjk)) = 0 := by
    rw [← weights_map_apply_of_injective Fin.succAbove_right_injective (f := j.succAbove),
      Fin.succAbove_pred_of_lt _ _ hjk, h, weights_map_succAbove_self]
  obtain ⟨w, rfl⟩ := (mem_range_map_succAbove_iff _ y).2 hy
  refine ⟨w, rfl, map_injective (R := R) Fin.succAbove_right_injective (f := k.succAbove) ?_⟩
  have hcomp : k.succAbove ∘ (j.castPred (Fin.ne_last_of_lt hjk)).succAbove =
      j.succAbove ∘ (k.pred (Fin.ne_zero_of_lt hjk)).succAbove := by
    funext m
    ext
    have := Fin.lt_def.1 hjk
    simp only [Function.comp_apply, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
      apply_ite Fin.val, Fin.val_succ, Fin.coe_castPred, Fin.val_pred]
    split_ifs <;> omega
  rw [← h, ← map_comp, ← hcomp, map_comp]

end Convexity.StdSimplex
