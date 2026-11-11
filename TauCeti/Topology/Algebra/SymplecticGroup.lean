/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Sum

/-!
# Closedness of the matrix symplectic group, and continuity of direct sums

The defining equation `M J Mᵀ = J` of `Matrix.symplecticGroup` is polynomial in the entries, so it
is a closed condition in the entrywise matrix topology, and closedness is proved directly from that
equation here.

`TauCeti.GLSymplectic` is the same condition on the underlying matrix of a unit, so its carrier is
the preimage of the symplectic group under the continuous inclusion of the units.

The symplectic direct sum `Matrix.symplecticSum` of matrices is a reindexed block-diagonal matrix,
so it is continuous, and so is the induced direct sum `TauCeti.GLSymplectic.sum` of symplectic
matrices.

## Main results

* `Matrix.isClosed_symplecticGroup`: the matrix symplectic group is closed over any `T₁`
  topological commutative ring.
* `TauCeti.isClosed_GLSymplectic`: the symplectic subgroup of the general linear group is closed.
* `Continuous.matrix_symplecticSum` and `TauCeti.GLSymplectic.continuous_sum`: the symplectic
  direct sum of matrices, and of symplectic matrices, is continuous.
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

/-- The symplectic direct sum of continuous families of matrices is continuous. -/
theorem Continuous.matrix_symplecticSum {n m R X : Type*} [TopologicalSpace X] [TopologicalSpace R]
    [Zero R] {A : X → Matrix (n ⊕ n) (n ⊕ n) R} {B : X → Matrix (m ⊕ m) (m ⊕ m) R}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x ↦ symplecticSum (A x) (B x) := by
  simpa only [symplecticSum_def] using
    (hA.matrix_fromBlocks continuous_const continuous_const hB).matrix_submatrix _ _

namespace TauCeti.GLSymplectic

variable {n m R : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- The direct sum of symplectic matrices is continuous. -/
theorem continuous_sum :
    Continuous (sum : GLSymplectic n R × GLSymplectic m R → GLSymplectic (n ⊕ m) R) := by
  have h₁ : Continuous fun p : GLSymplectic n R × GLSymplectic m R ↦
      ((p.1 : GL (n ⊕ n) R) : Matrix (n ⊕ n) (n ⊕ n) R) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
  have h₂ : Continuous fun p : GLSymplectic n R × GLSymplectic m R ↦
      ((p.2 : GL (m ⊕ m) R) : Matrix (m ⊕ m) (m ⊕ m) R) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)
  have hval : Continuous fun p : GLSymplectic n R × GLSymplectic m R ↦
      ((sum p : GL ((n ⊕ m) ⊕ (n ⊕ m)) R) : Matrix ((n ⊕ m) ⊕ (n ⊕ m)) _ R) :=
    (h₁.matrix_symplecticSum h₂).congr fun p ↦ (coe_sum p.1 p.2).symm
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hval, ?_⟩)
  exact (hval.comp continuous_inv).congr fun p ↦ by
    simp only [Function.comp_apply, map_inv, Subgroup.coe_inv]

end TauCeti.GLSymplectic
