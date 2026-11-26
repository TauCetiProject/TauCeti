/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.ConleyZehnder.FrameChange
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
import TauCeti.Analysis.Matrix.SymplecticGroup.Maslov.Lagrangian
import TauCeti.LinearAlgebra.Basis.Basic
import TauCeti.LinearAlgebra.BilinearForm.LagrangianBasis

/-!
# Loops of linear symplectic maps preserving a Lagrangian subspace

Let `(V, ω)` be a finite-dimensional symplectic vector space and `L ⊆ V` a Lagrangian subspace. A
loop `g` of linear symplectic maps of `V` that preserves `L` at every time has Maslov index zero
(`TauCeti.SymplecticForm.maslovIndex_eq_zero_of_mapsTo`). Indeed, a basis of `L` extends to a
symplectic basis of `V` with `L` spanned by its first half
(`LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_inl_eq`); in this basis the matrices of
`g` have a vanishing lower left block, and such loops of symplectic matrices have Maslov index
zero (`TauCeti.GLSymplectic.maslovIndex_eq_zero_of_toBlocks₂₁_eq_zero`).

So changing the frame of a path of linear symplectic maps by a loop preserving `L` does not change
its Conley–Zehnder index (`TauCeti.SymplecticForm.conleyZehnderIndex_frameChange_of_mapsTo`), by
the change of frame law `TauCeti.SymplecticForm.conleyZehnderIndex_frameChange`. This is the
linear algebra behind gradings read in frames adapted to a Lagrangian distribution, such as the
vertical distribution of a cotangent bundle: two such frames along a periodic orbit differ by a
loop preserving the model Lagrangian, so they assign the orbit the same Conley–Zehnder index.

The statement concerns loops, not single maps: the shear `(q, p) ↦ (q, p + c q)` preserves the
vertical Lagrangian `0 ⊕ ℝ` of `ℝ²` for every `c`, but its Maslov phase is not `±1` for `c ≠ 0`.

## Main results

* `TauCeti.SymplecticForm.maslovIndex_eq_zero_of_mapsTo`: a loop of linear symplectic maps
  preserving a Lagrangian subspace has Maslov index zero.
* `TauCeti.SymplecticForm.conleyZehnderIndex_frameChange_of_mapsTo`: changing the frame by such a
  loop keeps the Conley–Zehnder index.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.2 (the canonical grading of Floer
  homology of cotangent bundles, read in frames adapted to the vertical distribution).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 2.2 (the Maslov index of loops of symplectic matrices).
-/

public section

noncomputable section

open Matrix Module
open scoped unitInterval

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {L : Submodule ℝ V}

/-- **Loops preserving a Lagrangian subspace have Maslov index zero.** If a loop `g` of linear
symplectic maps of `(V, ω)` maps a Lagrangian subspace `L` into itself at every time, then its
Maslov index vanishes. -/
theorem maslovIndex_eq_zero_of_mapsTo (hL : ω.IsLagrangian L) {A : V →L[ℝ] V} (g : Path A A)
    (hg : ∀ t u v, ω (g t u) (g t v) = ω u v) (hgL : ∀ t, Set.MapsTo (g t) L L) :
    ω.maslovIndex g hg = 0 := by
  -- A symplectic basis whose first half is a basis of `L`.
  let e := Module.finBasis ℝ L
  -- `IsLagrangian` is not exposed, so `L = ω.orthogonal L` comes from its two halves.
  obtain ⟨b, hb, hbe⟩ := ω.isAlt.exists_basis_toMatrix_eq_J_inl_eq ω.nondegenerate e
    (le_antisymm (isIsotropic_iff_le.1 hL.isIsotropic) (isCoisotropic_iff_le.1 hL.isCoisotropic))
  rw [ω.maslovIndex_eq hb]
  -- In it, the matrices of `g` have a vanishing lower left block.
  refine GLSymplectic.maslovIndex_eq_zero_of_toBlocks₂₁_eq_zero _ fun t ↦ ?_
  ext i j
  simp only [matrixPath_apply, coe_toGLSymplectic, toBlocks₂₁, of_apply, LinearMap.toMatrix_apply,
    Matrix.zero_apply]
  refine b.repr_inr_eq_zero_of_mem hbe (hgL t ?_) i
  rw [SetLike.mem_coe, hbe]
  exact (e j).property

/-- **Changing the frame by a loop preserving a Lagrangian keeps the Conley–Zehnder index.** Let
`g` be a loop of linear symplectic maps of `(V, ω)` preserving a Lagrangian subspace `L`, with
pointwise inverses `g'`, and `Ψ` a path of linear symplectic maps. Then the path
`t ↦ g(t)⁻¹ Ψ(t) g(0)` has the same Conley–Zehnder index as `Ψ`. -/
theorem conleyZehnderIndex_frameChange_of_mapsTo (hL : ω.IsLagrangian L) {A A' B C : V →L[ℝ] V}
    (g : Path A A) (hg : ∀ t u v, ω (g t u) (g t v) = ω u v) (hgL : ∀ t, Set.MapsTo (g t) L L)
    (g' : Path A' A') (hg' : ∀ t u, g' t (g t u) = u) (Ψ : Path B C)
    (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) :
    ω.conleyZehnderIndex (frameChange g' Ψ A) (ω.apply_frameChange_apply hg hg' hΨ) =
      ω.conleyZehnderIndex Ψ hΨ := by
  rw [ω.conleyZehnderIndex_frameChange g hg g' hg' Ψ hΨ, maslovIndex_eq_zero_of_mapsTo hL g hg hgL,
    Int.cast_zero, mul_zero, add_zero]

end TauCeti.SymplecticForm
