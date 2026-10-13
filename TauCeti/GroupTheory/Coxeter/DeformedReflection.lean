/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Graph
public import Mathlib.LinearAlgebra.Reflection
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-!
# Deformed simple reflections of a finite graph

For a unit `q` in a commutative ring, the graph Cartan rows have diagonal coefficient
`1 + q²` and edge coefficient `q`. Subtracting the value of a row times its vertex vector
gives a linear automorphism. Its inverse subtracts `q⁻²` times the same row.

These transformations satisfy the graph's Artin relations. At `q = -1` the Cartan rows
are the rows of `2I - A`, and the transformations are the standard simple reflections.
The construction uses Mathlib's `Module.preReflection` and `Module.reflection`.

The vertex module and its operators are defined algebraically; identifying them with
graded Grothendieck classes requires a separate comparison.
-/

public section
noncomputable section

namespace SimpleGraph

universe u v
variable {V : Type u} [Fintype V] [DecidableEq V] {R : Type v} [CommRing R]
  (G : SimpleGraph V)

/-- The diagonal and edge coefficients of the deformed graph Cartan matrix. -/
def deformedCartanEntry (q : R) (i j : V) : R := by
  classical
  exact if i = j then 1 + q ^ 2 else if G.Adj i j then q else 0

/-- A row of the deformed graph Cartan matrix as a linear functional on vertex coordinates. -/
def deformedCartanRow (q : R) (i : V) : Module.Dual R (V → R) :=
  ∑ j, G.deformedCartanEntry q i j • LinearMap.proj j

@[simp]
theorem deformedCartanRow_single (q : R) (i j : V) :
    G.deformedCartanRow q i (Pi.single j 1) = G.deformedCartanEntry q i j := by
  classical
  simp [deformedCartanRow, LinearMap.sum_apply, LinearMap.proj_apply, Pi.single_apply]

theorem deformedCartanRow_single_self (q : R) (i : V) :
    G.deformedCartanRow q i (Pi.single i 1) = 1 + q ^ 2 := by
  classical
  simp [deformedCartanEntry]

theorem deformedCartanRow_single_of_adj (q : R) {i j : V} (h : G.Adj i j) :
    G.deformedCartanRow q i (Pi.single j 1) = q := by
  classical
  simp [deformedCartanEntry, h.ne, h]

theorem deformedCartanRow_single_of_not_adj (q : R) {i j : V}
    (hne : i ≠ j) (h : ¬ G.Adj i j) :
    G.deformedCartanRow q i (Pi.single j 1) = 0 := by
  classical
  simp [deformedCartanEntry, hne, h]

private theorem inverse_coefficient (q : Rˣ) :
    (↑q⁻¹ : R) ^ 2 * (q : R) ^ 2 = 1 := by
  calc
    _ = ((↑q⁻¹ : R) * q) ^ 2 := by ring
    _ = 1 := by simp

/-- The deformed simple reflection at a vertex, in functional composition order. -/
def deformedReflection (q : Rˣ) (i : V) : (V → R) ≃ₗ[R] (V → R) := by
  classical
  let e : V → R := Pi.single i 1
  let f := G.deformedCartanRow (q : R) i
  refine LinearEquiv.ofLinearMap (Module.preReflection e f)
    (Module.preReflection e ((↑q⁻¹ : R) ^ 2 • f)) ?_ ?_
  · apply LinearMap.ext
    intro x
    dsimp only [e, f]
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Module.preReflection_apply,
      map_sub, map_smul, LinearMap.smul_apply, deformedCartanRow_single_self,
      smul_eq_mul]
    match_scalars <;>
      first | ring1 | linear_combination (G.deformedCartanRow (q : R) i x) * inverse_coefficient q
  · apply LinearMap.ext
    intro x
    dsimp only [e, f]
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Module.preReflection_apply,
      map_sub, map_smul, LinearMap.smul_apply, deformedCartanRow_single_self,
      smul_eq_mul]
    match_scalars <;>
      first | ring1 | linear_combination (G.deformedCartanRow (q : R) i x) * inverse_coefficient q

/-- A deformed reflection subtracts its Cartan-row value in the vertex direction. -/
theorem deformedReflection_apply (q : Rˣ) (i : V) (x : V → R) :
    G.deformedReflection q i x =
      x - G.deformedCartanRow (q : R) i x • Pi.single i 1 := by
  simp only [deformedReflection, LinearEquiv.coe_ofLinearMap, Module.preReflection_apply]

/-- Distinct nonadjacent vertex operators commute. -/
theorem deformedReflection_commute (q : Rˣ) {i j : V}
    (hne : i ≠ j) (h : ¬ G.Adj i j) :
    G.deformedReflection q i * G.deformedReflection q j =
      G.deformedReflection q j * G.deformedReflection q i := by
  have hji : ¬ G.Adj j i := fun h' ↦ h h'.symm
  apply LinearEquiv.ext
  intro x
  simp only [LinearEquiv.mul_apply, deformedReflection_apply, map_sub, map_smul,
    G.deformedCartanRow_single_of_not_adj (q : R) hne h,
    G.deformedCartanRow_single_of_not_adj (q : R) (Ne.symm hne) hji]
  module

/-- Adjacent vertex operators satisfy the length-three braid relation. -/
theorem deformedReflection_braid (q : Rˣ) {i j : V} (h : G.Adj i j) :
    G.deformedReflection q i * G.deformedReflection q j * G.deformedReflection q i =
      G.deformedReflection q j * G.deformedReflection q i * G.deformedReflection q j := by
  apply LinearEquiv.ext
  intro x
  simp only [LinearEquiv.mul_apply, deformedReflection_apply, map_sub, map_smul,
    deformedCartanRow_single_self,
    G.deformedCartanRow_single_of_adj (q : R) h,
    G.deformedCartanRow_single_of_adj (q : R) h.symm]
  module

/-- The deformed reflections define a linear representation of the graph's Artin group. -/
def deformedReflectionRepresentation (q : Rˣ) :
    TauCeti.ArtinGroup G.coxeterMatrix →* ((V → R) ≃ₗ[R] (V → R)) :=
  G.artinGroupLift (G.deformedReflection q)
    (G.deformedReflection_commute q) (G.deformedReflection_braid q)

/-- The representation sends each Artin generator to its vertex operator. -/
@[simp]
theorem deformedReflectionRepresentation_gen (q : Rˣ) (i : V) :
    G.deformedReflectionRepresentation q (TauCeti.ArtinGroup.gen G.coxeterMatrix i) =
      G.deformedReflection q i := by
  simp only [deformedReflectionRepresentation, artinGroupLift_gen]

/-- The vertex direction is multiplied by `-q²`. -/
@[simp]
theorem deformedReflection_single_self (q : Rˣ) (i : V) :
    G.deformedReflection q i (Pi.single i 1) = -(q : R) ^ 2 • Pi.single i 1 := by
  rw [deformedReflection_apply, deformedCartanRow_single_self]
  module

/-- An adjacent vertex direction acquires `-q` times the reflecting direction. -/
theorem deformedReflection_single_of_adj (q : Rˣ) {i j : V} (h : G.Adj i j) :
    G.deformedReflection q i (Pi.single j 1) =
      Pi.single j 1 - (q : R) • Pi.single i 1 := by
  rw [deformedReflection_apply, G.deformedCartanRow_single_of_adj (q : R) h]

/-- A distinct nonadjacent vertex direction is fixed. -/
theorem deformedReflection_single_of_not_adj (q : Rˣ) {i j : V}
    (hne : i ≠ j) (h : ¬ G.Adj i j) :
    G.deformedReflection q i (Pi.single j 1) = Pi.single j 1 := by
  rw [deformedReflection_apply, G.deformedCartanRow_single_of_not_adj (q : R) hne h]
  simp

/-- At `q = -1`, a deformed reflection is Mathlib's ordinary simple reflection. -/
theorem deformedReflection_neg_one (i : V) :
    G.deformedReflection (-1 : Rˣ) i =
      Module.reflection (x := Pi.single i 1) (f := G.deformedCartanRow (-1 : R) i)
        (by rw [deformedCartanRow_single_self]; ring) := by
  apply LinearEquiv.ext
  intro x
  rw [deformedReflection_apply, Module.reflection_apply]
  simp

variable [DecidableRel G.Adj]

/-- The specialized Cartan row has the entries of `2I - A_G`. -/
theorem deformedCartanRow_neg_one_single (i j : V) :
    G.deformedCartanRow (-1 : R) i (Pi.single j 1) =
      ((2 : R) • (1 : Matrix V V R) - G.adjMatrix R) i j := by
  rw [deformedCartanRow_single]
  by_cases hij : i = j
  · subst j
    simp [deformedCartanEntry]
    ring
  · by_cases h : G.Adj i j
    · simp [deformedCartanEntry, hij, h, SimpleGraph.adjMatrix]
    · simp [deformedCartanEntry, hij, h, SimpleGraph.adjMatrix]

end SimpleGraph
