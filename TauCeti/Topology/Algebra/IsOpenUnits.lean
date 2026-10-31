/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsOpenUnits
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Rings with open units: the inverse and square matrices

A topological monoid `M` has open units (`IsOpenUnits M`) when `Units.val : Mˣ → M` is an open
embedding: the units are open and inversion is continuous on them for the subspace topology.
In a monoid with zero with open units, `Ring.inverse` is therefore continuous at every unit. This
file uses that to show that the ring of square matrices over a commutative topological ring `R` with
open units again has open units. The invertible matrices are the preimage of the open set of
units of `R` under the continuous determinant, and the inverse `A⁻¹ = (det A)⁻¹ • adj A` is
continuous on them because the inverse of the determinant is.

Over a nonarchimedean local field `E`, which has open units because it is a topological field,
this says that `GL_n(E)` with the topology of the unit group is the open subspace
`{det ≠ 0}` of the matrices `M_n(E)`. The hypothesis on `R` cannot be dropped: over the adeles,
inversion is not continuous on the units for the subspace topology, already for `n = 1`.

## Main declarations

* `IsOpenUnits.continuousAt_ringInverse`: `Ring.inverse` is continuous at every unit of a ring
  with open units.
* `Matrix.instIsOpenUnits`: square matrices over a commutative topological ring with open units
  have open units.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  §3, pp. 3–4.
-/

public section

open Topology

variable {R : Type*} [MonoidWithZero R] [TopologicalSpace R] [IsOpenUnits R]

/-- In a monoid with zero whose units are open with continuous inversion, `Ring.inverse` is
continuous at every unit. -/
theorem IsOpenUnits.continuousAt_ringInverse (u : Rˣ) : ContinuousAt Ring.inverse (u : R) := by
  rw [← IsOpenUnits.isOpenEmbedding_unitsVal.continuousAt_iff]
  have : (Ring.inverse ∘ Units.val : Rˣ → R) = fun v ↦ ↑v⁻¹ := by
    funext v
    exact Ring.inverse_unit v
  rw [this]
  exact Units.continuous_coe_inv.continuousAt

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R] [IsOpenUnits R]

/-- Square matrices over a commutative topological ring with open units have open units: the
invertible matrices form an open set on which inversion is continuous. -/
instance instIsOpenUnits : IsOpenUnits (Matrix n n R) where
  isOpenEmbedding_unitsVal := by
    refine ⟨Units.isEmbedding_val_mk' (f := Inv.inv) (fun A hA ↦ ?_)
      fun u ↦ (coe_units_inv u).symm, ?_⟩
    · obtain ⟨u, hu⟩ := (isUnit_iff_isUnit_det A).1 hA
      exact (continuousAt_matrix_inv A
        (hu ▸ IsOpenUnits.continuousAt_ringInverse u)).continuousWithinAt
    · have hrange : Set.range (Units.val : (Matrix n n R)ˣ → Matrix n n R) =
          det ⁻¹' Set.range (Units.val : Rˣ → R) := by
        ext A
        exact isUnit_iff_isUnit_det A
      rw [hrange]
      exact IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_range.preimage continuous_id.matrix_det

end Matrix
