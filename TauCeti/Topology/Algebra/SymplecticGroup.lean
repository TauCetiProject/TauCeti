/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# Closedness of the matrix symplectic group

The defining equation `M J Mᵀ = J` of `Matrix.symplecticGroup` is polynomial in the entries, so it
is a closed condition in the entrywise matrix topology. Unlike the orthogonal group the symplectic
group is not compact, so closedness cannot be read off a compactness statement and is proved
directly here.

`TauCeti.GLSymplectic` is the same condition on the underlying matrix of a unit, so its carrier is
the preimage of the symplectic group under the continuous inclusion of the units.

## Main results

* `Matrix.isClosed_symplecticGroup`: the matrix symplectic group is closed over any `T₁`
  topological commutative ring.
* `TauCeti.isClosed_GLSymplectic`: the symplectic subgroup of the general linear group is closed.
-/

public section

open Matrix Set

namespace Matrix

variable (l : Type*) [Fintype l] [DecidableEq l]
  (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T1Space R]

/-- The matrix symplectic group is closed in the entrywise matrix topology. -/
theorem isClosed_symplecticGroup :
    IsClosed (Matrix.symplecticGroup l R : Set (Matrix (l ⊕ l) (l ⊕ l) R)) := by
  have hcont : Continuous fun A : Matrix (l ⊕ l) (l ⊕ l) R => A * J l R * Aᵀ :=
    (continuous_id.matrix_mul continuous_const).matrix_mul continuous_id.matrix_transpose
  have hset : (Matrix.symplecticGroup l R : Set (Matrix (l ⊕ l) (l ⊕ l) R)) =
      {A : Matrix (l ⊕ l) (l ⊕ l) R | A * J l R * Aᵀ = J l R} :=
    Set.ext fun _ => SymplecticGroup.mem_iff
  rw [hset]
  exact isClosed_eq hcont continuous_const

end Matrix

namespace TauCeti

variable (l : Type*) [Fintype l] [DecidableEq l]
  (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T1Space R]

/-- The symplectic subgroup of the general linear group is closed: it is the preimage, under the
continuous inclusion of the units, of the matrix symplectic group. -/
theorem isClosed_GLSymplectic :
    IsClosed ((GLSymplectic l R : Subgroup (GL (l ⊕ l) R)) : Set (GL (l ⊕ l) R)) := by
  have hpre : ((GLSymplectic l R : Subgroup (GL (l ⊕ l) R)) : Set (GL (l ⊕ l) R)) =
      Units.val ⁻¹' (Matrix.symplecticGroup l R : Set (Matrix (l ⊕ l) (l ⊕ l) R)) :=
    Set.ext fun _ => GLSymplectic.mem_iff_mem_symplecticGroup
  rw [hpre]
  exact (Matrix.isClosed_symplecticGroup l R).preimage Units.continuous_val

end TauCeti
