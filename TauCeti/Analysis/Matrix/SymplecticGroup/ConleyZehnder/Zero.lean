/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Multiplicity

/-!
# The zero axiom for the Conley–Zehnder index

A path of symplectic matrices along which the eigenvalue `1` keeps the same geometric multiplicity
has Conley–Zehnder index zero
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq`).

The straightened graph `T Γ(A)` of a real matrix `A` meets `ℝ^{n ⊕ n}`, the straightened diagonal,
in the image of the fixed vectors of `A`, so the dimension of that intersection is the dimension of
the eigenspace of `A` at `1`
(`Matrix.finrank_realImage_diagonalStraightening_mul_graphFrame_inf_realSubspace`). The zero axiom
then follows from the zero axiom for the Maslov index
(`Matrix.UnitaryGroup.maslovIndex_eq_zero_of_finrank_eq`).

## Main results

* `Matrix.finrank_realImage_diagonalStraightening_mul_graphFrame_inf_realSubspace`: the graph of
  `A` meets the diagonal in a space of the dimension of the fixed vectors of `A`.
* `TauCeti.GLSymplectic.rootMultiplicity_one_charpoly_souriau_graphUnitaryFrame`: the multiplicity
  of `1` as an eigenvalue of the Souriau map of the unitary graph frame.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq`: the zero axiom for
  the Conley–Zehnder index.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Theorem 2.3 (the zero axiom) and Section 4.
-/

public section

open Matrix Module Module.End TauCeti

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The graph of `A` meets the diagonal in the fixed vectors of `A`.** The real dimension of the
intersection of the straightened graph `T Γ(A)` with `ℝ^{n ⊕ n}`, the straightened diagonal, is
the dimension of the eigenspace of `A` at `1`. -/
theorem finrank_realImage_diagonalStraightening_mul_graphFrame_inf_realSubspace
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    finrank ℝ ((diagonalStraightening n * graphFrame A).realImage ⊓ realSubspace (n ⊕ n) :
      Submodule ℝ _) = finrank ℝ (eigenspace (toLin' A) 1) := by
  set T := (toEuclideanCLM (𝕜 := ℂ) (diagonalStraightening n) :
      EuclideanSpace ℂ (n ⊕ n) →ₗ[ℂ] EuclideanSpace ℂ (n ⊕ n)).restrictScalars ℝ
  have hT : Function.Injective T := fun x y h ↦
    (UnitaryGroup.toLinearIsometryEquiv ⟨_, diagonalStraightening_mem_unitaryGroup⟩).injective <| by
      -- Both sides act by `diagonalStraightening n *ᵥ ·`, so `h` closes the goal by `rfl`.
      rw [UnitaryGroup.toLinearIsometryEquiv_apply, UnitaryGroup.toLinearIsometryEquiv_apply]
      exact h
  rw [← realImage_diagonalStraightening_mul_graphFrame_one, realImage_mul, realImage_mul,
    ← Submodule.map_inf T hT, realImage_graphFrame_inf_realImage_graphFrame_one,
    ← Submodule.map_comp]
  exact (Submodule.equivMapOfInjective (T ∘ₗ graphFrameLin A)
    (hT.comp (graphFrameLin_injective A)) _).finrank_eq.symm

end Matrix

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The multiplicity of `1` as an eigenvalue of the Souriau map of the unitary graph frame of a
symplectic matrix `A` is the dimension of the fixed vectors of `A`. -/
theorem rootMultiplicity_one_charpoly_souriau_graphUnitaryFrame (A : GLSymplectic n ℝ) :
    (UnitaryGroup.souriau (graphUnitaryFrame A) :
      Matrix (n ⊕ n) (n ⊕ n) ℂ).charpoly.rootMultiplicity 1 =
        finrank ℝ (eigenspace (toLin' ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) 1) := by
  rw [UnitaryGroup.rootMultiplicity_one_charpoly_souriau, realImage_graphUnitaryFrame,
    finrank_realImage_diagonalStraightening_mul_graphFrame_inf_realSubspace]

/-- **The zero axiom for the Conley–Zehnder index.** A path of symplectic matrices along which the
eigenvalue `1` keeps the same geometric multiplicity has Conley–Zehnder index zero. In particular
a path of symplectic matrices without the eigenvalue `1` has index zero. -/
theorem conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq {A B : GLSymplectic n ℝ}
    (γ : Path A B) {k : ℕ}
    (h : ∀ t, finrank ℝ (eigenspace (toLin' ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))
      1) = k) :
    conleyZehnderIndex γ = 0 := by
  rw [conleyZehnderIndex_def, UnitaryGroup.maslovIndex_eq_zero_of_rootMultiplicity_eq _ (k := k)
    fun t ↦ by rw [Path.map_coe, Function.comp_apply,
      rootMultiplicity_one_charpoly_souriau_graphUnitaryFrame, h t], neg_zero]

end TauCeti.GLSymplectic
