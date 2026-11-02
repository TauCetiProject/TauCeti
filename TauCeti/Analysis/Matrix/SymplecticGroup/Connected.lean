/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.Symplectic
public import TauCeti.Analysis.Matrix.UnitaryGroup.Connected
public import TauCeti.Topology.Algebra.Matrix.Realify

/-!
# Path connectedness of the real symplectic group

The real symplectic group is path connected, including in dimension zero. The positive polar
factor contracts through symplectic matrices, joining each matrix to its orthogonal polar factor.
The intersection of the symplectic and orthogonal groups is the realification of the complex
unitary group, which is path connected. Concatenating these paths joins every symplectic matrix
to the identity.

We provide path connectedness both for the native matrix submonoid `Matrix.symplecticGroup`
and for the subgroup `TauCeti.GLSymplectic` of the general linear group.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, third edition,
  Oxford University Press, 2017, Section 2.2.
-/

public section

open Matrix
open scoped MatrixOrder

namespace Matrix

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The real symplectic matrices form a path connected set, including in dimension zero. -/
theorem isPathConnected_symplecticGroup :
    IsPathConnected (symplecticGroup n ℝ : Set (Matrix (n ⊕ n) (n ⊕ n) ℝ)) := by
  let f : unitaryGroup n ℂ → Matrix (n ⊕ n) (n ⊕ n) ℝ := fun U ↦ (U : Matrix n n ℂ).realify
  have hf : Continuous f :=
    isClosedEmbedding_realify.continuous.comp continuous_subtype_val
  have hrange : Set.range f =
      ((symplecticGroup n ℝ ⊓ orthogonalGroup (n ⊕ n) ℝ :
        Submonoid (Matrix (n ⊕ n) (n ⊕ n) ℝ)) : Set _) := by
    simp only [symplecticGroup_inf_orthogonalGroup, Submonoid.coe_map, Set.image_eq_range,
      realifyAlgHom_apply, f]
    rfl
  have hconn := isPathConnected_range hf
  rw [hrange] at hconn
  refine ⟨1, (symplecticGroup n ℝ).one_mem, fun {A} hA ↦ ?_⟩
  obtain ⟨u, rfl⟩ := (isUnit_iff_isUnit_det A).2 (SymplecticGroup.symplectic_det hA)
  have hU : (u.polarUnitary : Matrix (n ⊕ n) (n ⊕ n) ℝ) ∈
      (symplecticGroup n ℝ ⊓ orthogonalGroup (n ⊕ n) ℝ :
        Submonoid (Matrix (n ⊕ n) (n ⊕ n) ℝ)) :=
    ⟨SymplecticGroup.polarUnitary_mem hA, u.polarUnitary.2⟩
  exact ((hconn.joinedIn 1 (Submonoid.one_mem _) _ hU).mono
    (fun _ h ↦ h.1)).trans (SymplecticGroup.joinedIn_polarUnitary hA).symm

end Matrix

namespace SymplecticGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The native real matrix symplectic group is path connected, including in dimension zero. -/
instance instPathConnectedSpace : PathConnectedSpace (Matrix.symplecticGroup n ℝ) :=
  isPathConnected_iff_pathConnectedSpace.mp (Matrix.isPathConnected_symplecticGroup n)

end SymplecticGroup

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real symplectic subgroup of the general linear group is path connected. -/
instance instPathConnectedSpaceGLSymplectic : PathConnectedSpace (GLSymplectic n ℝ) := by
  have hc : Continuous (GLSymplectic.ofSymplecticGroup n ℝ) := by
    apply Units.continuous_iff.mpr
    constructor
    · simpa only [Function.comp_def, GLSymplectic.coe_ofSymplecticGroup] using
        (continuous_subtype_val : Continuous fun S : Matrix.symplecticGroup n ℝ ↦
          (S : Matrix (n ⊕ n) (n ⊕ n) ℝ))
    · simp only [← map_inv, GLSymplectic.coe_ofSymplecticGroup, SymplecticGroup.coe_inv]
      exact (continuous_const.matrix_mul continuous_subtype_val.matrix_transpose).matrix_mul
        continuous_const
  let f : Matrix.symplecticGroup n ℝ → GLSymplectic n ℝ := fun S ↦
    ⟨GLSymplectic.ofSymplecticGroup n ℝ S, GLSymplectic.ofSymplecticGroup_mem n ℝ S⟩
  have hf : Function.Surjective f := by
    intro A
    refine ⟨GLSymplectic.mulEquivSymplecticGroup n ℝ A, ?_⟩
    apply Subtype.ext
    apply Units.ext
    simp only [f, GLSymplectic.coe_ofSymplecticGroup,
      GLSymplectic.coe_mulEquivSymplecticGroup]
  exact hf.pathConnectedSpace (hc.subtype_mk _)

end TauCeti
