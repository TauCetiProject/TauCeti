/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.CAD.Basic

/-!
# Projections of cylindrical algebraic decompositions to every lower dimension

Dropping the first `k` coordinates of a cylindrical algebraic decomposition of `ℝ ^ (n + k)`
gives a cylindrical algebraic decomposition of `ℝ ^ n`. The projection is precomposition with
`fun i : Fin n ↦ i.addNat k`, so it agrees with `Fin.tail` when `k = 1` and with the identity
when `k = 0`.

The projected cells are equal or disjoint at every lower dimension. In particular, whenever
two cells have a point in common after projection, both cover the same entire lower cell.
This is the cylindricity property used when eliminating successive blocks of variables.

## References

S. Basu, R. Pollack, and M.-F. Roy,
*Algorithms in Real Algebraic Geometry*, second edition, Section 5.1.
-/

public section

open Function Set

namespace TauCeti.IsCAD

variable {n k : ℕ} {𝒞 : Set (Set (Fin (n + k) → ℝ))}

/-- Dropping any initial block of coordinates from a CAD gives a CAD of the remaining
coordinates. This includes projection to dimension zero and the identity projection. -/
theorem image_comp_addNat (h : IsCAD (n + k) 𝒞) :
    IsCAD n ((image fun x ↦ x ∘ fun i : Fin n ↦ i.addNat k) '' 𝒞) := by
  induction k with
  | zero => simpa [comp_def] using h
  | succ k ih =>
    have hi (i : Fin n) : i.addNat (k + 1) = (i.addNat k).succ := by
      ext
      simp [Nat.add_assoc]
    have hp : (fun x : Fin (n + (k + 1)) → ℝ ↦ x ∘ fun i : Fin n ↦ i.addNat (k + 1)) =
        (fun x ↦ Fin.tail x ∘ fun i : Fin n ↦ i.addNat k) := by
      funext x i
      exact congrArg x (hi i)
    rw [hp]
    have ih' := ih h.image_tail
    rw [← image_comp, ← image_comp_eq] at ih'
    exact ih'

/-- At every lower dimension, the projections of two CAD cells are equal or disjoint.
Equality is equality of the whole projected cells, rather than merely an intersection at
a sample point. -/
theorem image_comp_addNat_eq_or_disjoint (h : IsCAD (n + k) 𝒞)
    {E E' : Set (Fin (n + k) → ℝ)} (hE : E ∈ 𝒞) (hE' : E' ∈ 𝒞) :
    (fun x ↦ x ∘ fun i : Fin n ↦ i.addNat k) '' E =
        (fun x ↦ x ∘ fun i : Fin n ↦ i.addNat k) '' E' ∨
      Disjoint ((fun x ↦ x ∘ fun i : Fin n ↦ i.addNat k) '' E)
        ((fun x ↦ x ∘ fun i : Fin n ↦ i.addNat k) '' E') :=
  h.image_comp_addNat.isPartition.pairwiseDisjoint.eq_or_disjoint
    (mem_image_of_mem _ hE) (mem_image_of_mem _ hE')

end TauCeti.IsCAD
