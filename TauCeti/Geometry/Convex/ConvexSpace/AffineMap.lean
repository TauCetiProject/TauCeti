/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.AffineMap
public import Mathlib.Geometry.Convex.ConvexSpace.Prod
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Coordinate maps between convex spaces

`Convexity.ConvexSpace.AffineMap.piPrecomp` reindexes a family of convex-space coordinates.
`Convexity.ConvexSpace.AffineMap.finInsertNth` inserts a fixed coordinate. Neither construction
requires vector-space or topological structure.
-/

public section

namespace Convexity.ConvexSpace.AffineMap

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

/-- Precomposition of a family of convex-space coordinates, as a bundled affine map. -/
def piPrecomp {ι κ : Type*} {X : κ → Type*} [∀ k, ConvexSpace R (X k)] (f : ι → κ) :
    ConvexSpace.AffineMap R (∀ k, X k) (∀ i, X (f i)) where
  toFun x i := x (f i)

/-- Coordinate evaluation of affine precomposition. -/
@[simp]
lemma piPrecomp_apply {ι κ : Type*} {X : κ → Type*} [∀ k, ConvexSpace R (X k)]
    (f : ι → κ) (x : ∀ k, X k) : piPrecomp (R := R) f x = fun i ↦ x (f i) := by
  rfl

/-- Insert a fixed coordinate into a finite family of convex spaces. -/
def finInsertNth {n : ℕ} {X : Fin (n + 1) → Type*} [∀ j, ConvexSpace R (X j)]
    (j : Fin (n + 1)) (a : X j) :
    ConvexSpace.AffineMap R (∀ i, X (j.succAbove i)) (∀ k, X k) where
  toFun := j.insertNth a
  isAffineMap_toFun := by
    rw [isAffineMap_pi_iff]
    intro k
    refine Fin.succAboveCases j ?_ ?_ k
    · simpa using (IsAffineMap.const (R := R) (X := ∀ i, X (j.succAbove i)) a)
    · intro i
      simpa using (Pi.isAffineMap_eval (R := R) (i := i) :
        IsAffineMap R (fun x : ∀ i, X (j.succAbove i) ↦ x i))

/-- Evaluation of affine coordinate insertion. -/
@[simp]
lemma finInsertNth_apply {n : ℕ} {X : Fin (n + 1) → Type*} [∀ j, ConvexSpace R (X j)]
    (j : Fin (n + 1)) (a : X j) (x : ∀ i, X (j.succAbove i)) :
    finInsertNth (R := R) j a x = j.insertNth a x := by
  rfl

end Convexity.ConvexSpace.AffineMap
