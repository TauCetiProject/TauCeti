/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Sum

/-!
# The topology of the matrix symplectic group

The defining equation `M J Mᵀ = J` of `Matrix.symplecticGroup` is polynomial in the entries, so it
is a closed condition in the entrywise matrix topology, and closedness is proved directly from that
equation here.

`TauCeti.GLSymplectic` is the same condition on the underlying matrix of a unit, so its carrier is
the preimage of the symplectic group under the continuous inclusion of the units. The
canonical multiplicative equivalence identifies the two subspace topologies. Its continuity
in the matrix-to-units direction uses the formula `A⁻¹ = -J Aᵀ J`.

The symplectic direct sum `Matrix.symplecticSum` of matrices is a reindexed block-diagonal matrix,
so it is continuous, and so is the induced direct sum `TauCeti.GLSymplectic.sum` of symplectic
matrices.

## Main results

* `Matrix.isClosed_symplecticGroup`: the matrix symplectic group is closed over any `T₁`
  topological commutative ring.
* `TauCeti.isClosed_GLSymplectic`: the symplectic subgroup of the general linear group is closed.
* `TauCeti.GLSymplectic.symplecticGroupContinuousMulEquiv`: the canonical equivalence for
  the matrix and unit subspace topologies.
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
  [TopologicalSpace R]

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
  have h₃ : Continuous fun p : GLSymplectic n R × GLSymplectic m R ↦
      (((p.1 : GL (n ⊕ n) R)⁻¹ : GL (n ⊕ n) R) : Matrix (n ⊕ n) (n ⊕ n) R) :=
    Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst)
  have h₄ : Continuous fun p : GLSymplectic n R × GLSymplectic m R ↦
      (((p.2 : GL (m ⊕ m) R)⁻¹ : GL (m ⊕ m) R) : Matrix (m ⊕ m) (m ⊕ m) R) :=
    Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_snd)
  refine (h₃.matrix_symplecticSum h₄).congr fun p ↦ ?_
  have := coe_sum p.1⁻¹ p.2⁻¹
  simpa only [Function.comp_apply, ← Prod.inv_mk (p.1) (p.2), map_inv, Subgroup.coe_inv,
    Prod.mk.eta] using this.symm

end TauCeti.GLSymplectic

namespace TauCeti.GLSymplectic

variable (l : Type*) [Fintype l] [DecidableEq l] (R : Type*) [CommRing R]

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The standard embedding into matrix units is continuous for the subspace topology. -/
theorem continuous_ofSymplecticGroup : Continuous (ofSymplecticGroup l R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_subtype_val.congr fun A ↦
      (coe_ofSymplecticGroup l R A).symm
  · have h : Continuous (fun A : Matrix.symplecticGroup l R ↦
        (-J l R) * (A : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ * J l R) :=
      (continuous_const.matrix_mul continuous_subtype_val.matrix_transpose).matrix_mul
        continuous_const
    refine h.congr fun A ↦ ?_
    have hinv := coe_ofSymplecticGroup l R A⁻¹
    rw [map_inv] at hinv
    exact (SymplecticGroup.coe_inv A).symm.trans hinv.symm

/-- The canonical multiplicative equivalence preserves the original matrix subspace topology. -/
def symplecticGroupContinuousMulEquiv : Matrix.symplecticGroup l R ≃ₜ* GLSymplectic l R where
  __ := (mulEquivSymplecticGroup l R).symm
  continuous_toFun := by
    apply continuous_induced_rng.2
    exact (continuous_ofSymplecticGroup l R).congr fun A ↦
      (coe_mulEquivSymplecticGroup_symm_apply l R A).symm
  continuous_invFun := by
    apply continuous_induced_rng.2
    exact (Units.continuous_val.comp continuous_subtype_val).congr fun A ↦
      (coe_mulEquivSymplecticGroup l R A).symm

/-- The equivalence sends a symplectic matrix to its canonical unit. -/
@[simp]
theorem coe_symplecticGroupContinuousMulEquiv (A : Matrix.symplecticGroup l R) :
    (symplecticGroupContinuousMulEquiv l R A : GL (l ⊕ l) R) =
      ofSymplecticGroup l R A :=
  coe_mulEquivSymplecticGroup_symm_apply l R A

/-- The inverse equivalence keeps the underlying matrix of the symplectic unit. -/
@[simp]
theorem coe_symplecticGroupContinuousMulEquiv_symm (A : GLSymplectic l R) :
    ((symplecticGroupContinuousMulEquiv l R).symm A : Matrix (l ⊕ l) (l ⊕ l) R) =
      ((A : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) :=
  coe_mulEquivSymplecticGroup l R A

end TauCeti.GLSymplectic
