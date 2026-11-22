/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Homotopy
public import TauCeti.Analysis.Matrix.SymplecticGroup.Connected
import TauCeti.LinearAlgebra.Eigenspace.Matrix

/-!
# Naturality of the Conley–Zehnder index

The Conley–Zehnder index of a path `Ψ` of symplectic matrices
(`TauCeti.GLSymplectic.conleyZehnderIndex`) is invariant under conjugation by a constant
symplectic matrix: `CZ(P Ψ P⁻¹) = CZ(Ψ)` (`TauCeti.GLSymplectic.conleyZehnderIndex_map_conj`).
This is the naturality axiom of the index.

The proof goes through the homotopy axiom
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_of_homotopy_of_finrank_eigenspace_eq`). The
symplectic group is path connected, so `P` is joined to the identity by a path `δ`, and
`(s, t) ↦ δ s Ψ(t) (δ s)⁻¹` is a homotopy from `Ψ` to `P Ψ P⁻¹`. Its paths
`s ↦ δ s Ψ(0) (δ s)⁻¹` and `s ↦ δ s Ψ(1) (δ s)⁻¹` through the endpoints run through conjugates
of a fixed matrix, so the eigenvalue `1` keeps its multiplicity along them.

Together with the loop axiom (`TauCeti.GLSymplectic.conleyZehnderIndex_mul`) it describes how the
index changes under a change of symplectic trivialization. Two trivializations of a symplectic
vector bundle along a loop differ by a loop `Φ` of symplectic matrices, based at some `P`, and a
path `Ψ` of matrices in the first trivialization becomes `t ↦ Φ(t) Ψ(t) P⁻¹` in the second. Its
index is `CZ(Ψ) - 2 μ(Φ)`, where `μ` is the Maslov index of loops
(`TauCeti.GLSymplectic.conleyZehnderIndex_mul_mul_refl_inv`). For the linearized flow along a
periodic orbit this is the change of the index under a change of the trivialization along the
orbit; the loop axiom alone covers only loops based at the identity.

## Main results

* `TauCeti.GLSymplectic.conleyZehnderIndex_map_conj`: naturality under conjugation by a constant
  symplectic matrix.
* `TauCeti.GLSymplectic.conleyZehnderIndex_mul_mul_refl_inv`: the change of the index under a
  change of symplectic trivialization along a loop.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Theorem 2.3 (the naturality axiom).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999 (the naturality and loop axioms of the Conley–Zehnder index).
-/

public section

open Matrix Module Module.End TauCeti
open scoped unitInterval

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Naturality of the Conley–Zehnder index.** Conjugating a path of symplectic matrices by a
constant symplectic matrix `P` does not change its Conley–Zehnder index: `CZ(P Ψ P⁻¹) = CZ(Ψ)`. -/
theorem conleyZehnderIndex_map_conj (P : GLSymplectic n ℝ) {A B : GLSymplectic n ℝ}
    (γ : Path A B) :
    conleyZehnderIndex (γ.map (f := fun X ↦ P * X * P⁻¹) (by fun_prop)) =
      conleyZehnderIndex γ := by
  let δ := PathConnectedSpace.somePath (1 : GLSymplectic n ℝ) P
  -- The homotopy `(s, t) ↦ δ s γ(t) (δ s)⁻¹` from `γ` to its conjugate by `P`. Its paths through
  -- the endpoints run through conjugates of a fixed matrix.
  let F : C(I × I, GLSymplectic n ℝ) := ⟨fun p ↦ δ p.1 * γ p.2 * (δ p.1)⁻¹, by fun_prop⟩
  have hk (x : I) (s : I) : finrank ℝ (eigenspace
      (toLin' ((F (s, x) : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) 1) =
        finrank ℝ (eigenspace (toLin' ((γ x : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) 1) := by
    have hF : ((F (s, x) : GLSymplectic n ℝ) : GL (n ⊕ n) ℝ) =
        (δ s : GL (n ⊕ n) ℝ) * (γ x : GL (n ⊕ n) ℝ) * (δ s : GL (n ⊕ n) ℝ)⁻¹ := by
      simp [F]
    rw [hF, Units.val_mul, Units.val_mul]
    exact finrank_eigenspace_toLin'_conj (δ s : GL (n ⊕ n) ℝ) _ 1
  exact (conleyZehnderIndex_eq_of_homotopy_of_finrank_eigenspace_eq γ _ F (fun t ↦ by simp [F, δ])
    (fun t ↦ by simp [F, δ]) (hk 0) (hk 1)).symm

/-- **Change of symplectic trivialization along a loop.** Let `Φ` be a loop of symplectic
matrices based at `P`, not necessarily the identity, and `γ` a path of symplectic matrices. Then
the path `t ↦ Φ(t) γ(t) P⁻¹` has Conley–Zehnder index `CZ(γ) - 2 μ(Φ)`, where `μ` is the Maslov
index of loops of symplectic matrices.

If `γ` is the linearized flow along a periodic orbit in a symplectic trivialization of the
tangent bundle along the orbit, and `Φ` compares a second such trivialization with the first,
then the linearized flow in the second trivialization is `t ↦ Φ(t) γ(t) Φ(0)⁻¹`. -/
theorem conleyZehnderIndex_mul_mul_refl_inv {P : GLSymplectic n ℝ} (Φ : Path P P)
    {A B : GLSymplectic n ℝ} (γ : Path A B) :
    conleyZehnderIndex ((Φ.mul γ).mul (Path.refl P⁻¹)) =
      conleyZehnderIndex γ - 2 * maslovIndex Φ := by
  -- Pointwise `Φ γ P⁻¹ = (Φ P⁻¹) (P γ P⁻¹)`, where `Φ P⁻¹` is a loop based at the identity.
  let φ : Path (1 : GLSymplectic n ℝ) 1 :=
    (Φ.mul (Path.refl P⁻¹)).cast (mul_inv_cancel P).symm (mul_inv_cancel P).symm
  have hφ : maslovIndex φ = maslovIndex Φ := by
    have h := maslovIndex_mul Φ (Path.refl P⁻¹)
    rw [maslovIndex_refl, add_zero] at h
    rw [← h, maslovIndex_def, maslovIndex_def]
    exact Circle.degree_congr _ _ fun t ↦ by simp [φ]
  rw [conleyZehnderIndex_congr _
      (φ.mul (γ.map (f := fun X ↦ P * X * P⁻¹) (by fun_prop))) fun t ↦ by simp [φ, mul_assoc],
    conleyZehnderIndex_mul, conleyZehnderIndex_map_conj, hφ]

end TauCeti.GLSymplectic
