/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.GeneralLinearGroup.Polar
public import TauCeti.Topology.Algebra.Star.Unitary
import TauCeti.Algebra.Algebra.Spectrum
import TauCeti.Analysis.CStarAlgebra.Unitary.Connected

/-!
# The stable component group of a finite-dimensional C⋆-algebra is trivial

An element of a finite-dimensional algebra over a field has finite spectrum
(`spectrum.finite_of_finiteDimensional`), and a unitary with finite spectrum is joined to `1` by
a path of unitaries (`Unitary.joined_one_of_finite_spectrum`). In a finite-dimensional C⋆-algebra
every unitary therefore lies in the identity component of the unitary group.

Applied to the finite-dimensional C⋆-algebras of matrices over a finite-dimensional C⋆-algebra
`A`, and with the polar decomposition of invertible matrices, every class of the stable component
group `π₀ GL_∞(A)` is trivial: `K₁(A) = 0` for finite-dimensional `A`
(`TauCeti.StableComponentGroup.subsingleton_of_finiteDimensional`).

## Main statements

* `TauCeti.StableComponentGroup.subsingleton_of_finiteDimensional`: the stable component group of
  a finite-dimensional C⋆-algebra is trivial.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §8.1.
-/

public section

namespace TauCeti.StableComponentGroup

variable {A : Type*} [CStarAlgebra A]

/-- **`K₁` of a finite-dimensional C⋆-algebra vanishes**: its stable component group is
trivial. -/
instance subsingleton_of_finiteDimensional [FiniteDimensional ℂ A] :
    Subsingleton (StableComponentGroup A) := by
  -- Mathlib's C⋆-algebra structure on `CStarMatrix n n A` is stated for an ordered `A`.
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  suffices h : ∀ x : StableComponentGroup A, x = 1 from ⟨fun x y ↦ (h x).trans (h y).symm⟩
  intro x
  obtain ⟨n, u, hu, rfl⟩ := exists_mem_unitary_mk_eq x
  set U : unitary (CStarMatrix (Fin n) (Fin n) A) :=
    ⟨CStarMatrix.ofMatrix (u : Matrix (Fin n) (Fin n) A), by
      rw [← CStarMatrix.ofMatrix_symm_mem_unitary_iff]; exact hu⟩
  have hU := Unitary.joined_one_of_finite_spectrum U (spectrum.finite_of_finiteDimensional _)
  have hj : Joined 1 u := by
    convert hU.map ((map_continuous (Matrix.GeneralLinearGroup.toCStarMatrixUnits (n := Fin n)
      (A := A)).symm).comp Unitary.continuous_toUnits) using 1
    · simp
    · ext : 1
      simp [U]
  simpa using mk_eq_one_of_mem_connectedComponentOfOne (by
    simpa using hj.inv_mul_mem_connectedComponentOfOne)

end TauCeti.StableComponentGroup
