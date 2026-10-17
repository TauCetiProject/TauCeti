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
weight vanishes, so a function taking a constant value on every facet takes that value wherever
some weight vanishes.  Two facets, opposite `j < k`, meet in the codimension-two face opposite both:
a common point of the two facets comes from that face through both composites of face maps, the
two sides of the simplicial identity `SimplexCategory.δ_comp_δ`.
-/

public section

namespace Convexity.StdSimplex

/-- A point of the triangle `StdSimplex R (Fin 3)` is determined by its three weights. -/
theorem ext_fin_three {R : Type*} [PartialOrder R] [Semiring R]
    {x y : StdSimplex R (Fin 3)} (h0 : x.weights 0 = y.weights 0)
    (h1 : x.weights 1 = y.weights 1) (h2 : x.weights 2 = y.weights 2) : x = y :=
  ext <| Finsupp.ext fun
    | ⟨0, _⟩ => h0
    | ⟨1, _⟩ => h1
    | ⟨2, _⟩ => h2

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {X Y : Type*}

/-- Along an injective map, the weight at the image of a point is the weight at that point. -/
theorem weights_map_apply_of_injective {f : X → Y} (hf : f.Injective) (x : StdSimplex R X)
    (a : X) : (x.map f).weights (f a) = x.weights a :=
  Finsupp.mapDomain_apply_of_injective hf _ _

omit [IsStrictOrderedRing R] in
/-- The three weights of a point of the standard `2`-simplex add up to `1`. -/
theorem total_fin_three (x : StdSimplex R (Fin 3)) :
    x.weights 0 + x.weights 1 + x.weights 2 = 1 := by
  rw [← x.total_of_fintype, Fin.sum_univ_three]

/-- The weights of the last two vertices of a point of the standard `2`-simplex add up to at
most `1`. -/
theorem weights_one_add_weights_two_le_one (x : StdSimplex R (Fin 3)) :
    x.weights 1 + x.weights 2 ≤ 1 := by
  rw [← x.total_fin_three, add_assoc]
  exact le_add_of_nonneg_left (x.weights_nonneg 0)

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

/-- On the facet opposite `j`, the weight at `j.succAbove i` is the `i`-th weight of the facet. -/
theorem weights_map_succAbove_of_eq {n : ℕ} {j k : Fin (n + 1)} {i : Fin n}
    (h : j.succAbove i = k) (x : StdSimplex R (Fin n)) :
    (x.map j.succAbove).weights k = x.weights i :=
  h ▸ weights_map_apply_of_injective Fin.succAbove_right_injective x i

/-- A function on a standard simplex which takes the value `z` on every facet takes the value `z`
at every point with a vanishing weight. -/
theorem apply_eq_of_weights_eq_zero {n : ℕ} {Z : Type*} {φ : StdSimplex R (Fin (n + 1)) → Z}
    {z : Z} (hφ : ∀ (i : Fin (n + 1)) (w : StdSimplex R (Fin n)), φ (w.map i.succAbove) = z)
    {b : StdSimplex R (Fin (n + 1))} {k : Fin (n + 1)} (hb : b.weights k = 0) : φ b = z := by
  obtain ⟨w, rfl⟩ := (mem_range_map_succAbove_iff k b).2 hb
  exact hφ k w

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
  -- The simplicial identity `SimplexCategory.δ_comp_δ`, in Mathlib's `Fin.succAbove` form.
  have hcomp : k.succAbove ∘ (j.castPred (Fin.ne_last_of_lt hjk)).succAbove =
      j.succAbove ∘ (k.pred (Fin.ne_zero_of_lt hjk)).succAbove := by
    funext m
    have hle : j ≤ (k.pred (Fin.ne_zero_of_lt hjk)).castSucc := by
      rwa [Fin.le_castSucc_iff, Fin.succ_pred]
    have := Fin.succAbove_succAbove_succAbove_predAbove j (k.pred (Fin.ne_zero_of_lt hjk)) m
    rwa [Fin.succAbove_pred_of_lt _ _ hjk, Fin.predAbove_of_le_castSucc _ _ hle] at this
  rw [← h, ← map_comp, ← hcomp, map_comp]

end Convexity.StdSimplex
